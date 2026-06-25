#!/usr/bin/env python3
"""In-process, real-time per-case auditor for AoA×PutnamBench evaluation.

Architecture (in-evaluator, 2026-06):
  The evaluator's audited agent class (``MinilangAgent_PutnamBench_Audited``)
  owns the auditor's lifecycle at the exact per-case ``validate()`` boundary:
    - ``CaseAuditor(case_name, log_dir)`` + ``.start()`` when a case begins;
    - ``.switch_to(invocation_id)`` each time an attempt mints a new invid
      (``_make_invocation_id`` override) — so pass@N and resume/retry stale
      invid dirs never confuse which directory to read;
    - ``await .stop()`` in ``finally`` when the case ends/raises.
  ``.start()`` launches ONE long-lived Opus (claude-opus-4-8) agent as an
  in-process ``asyncio`` task. The agent loops: call ``next_increment()`` →
  the tool blocks ~POLL_SECONDS, then LOCALLY reads the new bytes appended to
  the current attempt's ``<log_dir>/<invid>/interaction.yaml`` (no ssh — the
  evaluator, the central RPC host that writes the log, and the log file all
  share one node/filesystem) → returns the increment → agent analyses →
  ``report_issue(...)`` on a finding → loops again. There is NO agent-side
  "done" signal: the case ending cancels the asyncio task (the SDK's
  ``query()`` teardown terminates the underlying ``claude`` subprocess).

Safety (H1): the agent gets ``tools=[]`` (no built-in Bash/Edit/Write/…),
``permission_mode="dontAsk"`` (NOT bypassPermissions), ``strict_mcp_config``
and an allow-list of exactly the two ``mcp__audit__*`` tools — so a misled
Opus cannot touch the cluster, the eval, or the filesystem.
Cost (H4): ``max_budget_usd`` per case, a bounded ``max_turns`` backstop, and
idle backoff when nothing new is being written; per-agent ``total_cost_usd`` /
``session_id`` are logged.

Findings are appended to FINDINGS (jsonl) for human triage.
Underlying ``claude_agent_sdk`` uses the local ``claude`` CLI auth.

Online cross-case dedup (2026-06): ``report_issue`` ALWAYS appends the raw
finding to the jsonl (immutable audit trail), then best-effort feeds it to a
process-wide ``_Deduper`` singleton (one per findings file, shared by every
``CaseAuditor`` on the single evaluator event loop). The deduper embeds the
finding (Qwen3 M2: incoming = instruction-wrapped query, stored clusters =
bare documents), faiss-knn the top-K candidate "canonical issue clusters",
and asks a short-lived ``ClaudeSDKClient`` QA agent whether it is the SAME
underlying defect as one of them (conservative: never merge without QA
confirmation). It maintains a derived view (``audit_dedup_state.json`` +
``audit_issues.md``). Dedup is strictly best-effort: any failure/timeout
falls back to "raw finding already saved" and never breaks the auditor.
Two-phase lock: embed/knn/QA run OUTSIDE the lock; only the deterministic
state mutation + atomic flush hold the lock (no await inside it).
"""
import asyncio
import base64
import json
import os
import time
from typing import Any, cast

from claude_agent_sdk import (
    tool, create_sdk_mcp_server, ClaudeAgentOptions, query, ResultMessage,
    ClaudeSDKClient,
)

# ---------------- configuration (all env-overridable) ----------------
POLL_SECONDS    = int(os.environ.get("AUDIT_POLL_SECONDS", "120"))    # base block per next_increment
IDLE_STEP       = int(os.environ.get("AUDIT_IDLE_STEP", "60"))        # extra sleep per consecutive empty poll
IDLE_MAX_MULT   = int(os.environ.get("AUDIT_IDLE_MAX_MULT", "4"))     # cap on the idle-backoff multiplier
MODEL           = os.environ.get("AUDIT_MODEL", "claude-opus-4-8")
EFFORT          = cast(Any, os.environ.get("AUDIT_EFFORT", "high"))  # SDK validates at runtime; free env str
FINDINGS        = os.environ.get("AUDIT_FINDINGS")                   # abs override; default = <log_dir>/audit_findings.jsonl
MAX_TURNS       = int(os.environ.get("AUDIT_MAX_TURNS", "2000"))      # safety backstop; real bound = case end (cancel)
_BUDGET_ENV     = os.environ.get("AUDIT_MAX_BUDGET_USD")
MAX_BUDGET_USD  = float(_BUDGET_ENV) if _BUDGET_ENV else None         # None = no cap (user choice); env sets a per-case $ cap

# Built-in tools to explicitly disallow as belt-and-suspenders on top of tools=[].
_DISALLOWED = ["Bash", "Edit", "Write", "Read", "NotebookEdit",
               "WebFetch", "WebSearch", "Glob", "Grep", "Task", "TodoWrite"]
_DOC_SEP = b"\n---\n"   # interaction.yaml multi-doc separator (model.py _append_yaml)
_ALLOWED = ["mcp__audit__next_increment", "mcp__audit__report_issue"]

# ---------------- online dedup configuration ----------------
AUDIT_DEDUP            = os.environ.get("AUDIT_DEDUP", "1") != "0"      # master switch; "0" → pure raw append
AUDIT_DEDUP_TOPK       = int(os.environ.get("AUDIT_DEDUP_TOPK", "20"))  # knn candidates handed to the QA agent
AUDIT_DEDUP_TIMEOUT    = int(os.environ.get("AUDIT_DEDUP_TIMEOUT", "120"))   # per-finding consider() wall cap (best-effort)
AUDIT_DEDUP_MODEL      = os.environ.get("AUDIT_DEDUP_MODEL", MODEL)     # QA model (default = auditor's, opus)
AUDIT_DEDUP_QA_CONC    = int(os.environ.get("AUDIT_DEDUP_QA_CONCURRENCY", "4"))  # peak concurrent QA subprocesses
AUDIT_DEDUP_QA_TURNS   = int(os.environ.get("AUDIT_DEDUP_QA_TURNS", "6"))    # QA agent turn backstop
_REPR_CAP              = int(os.environ.get("AUDIT_DEDUP_REPR_CAP", "800"))  # per-candidate repr_detail char cap (head)
_FINDING_CAP          = int(os.environ.get("AUDIT_DEDUP_FINDING_CAP", "4000"))  # new-finding detail char cap (head) to QA
_DEDUP_ALLOWED = ["mcp__dedup__submit_verdict"]
# Qwen3 M2: the incoming finding is embedded as a QUERY with this instruction
# manually prepended (sent via role='document' so the provider's own Isabelle/HOL
# task is bypassed); stored cluster texts are embedded BARE (role='document').
_DEDUP_INSTRUCT = ("Given an audit finding about an AI theorem-proving system, "
                   "retrieve prior findings describing the same underlying system defect.")

_DEDUP_QA_SYSTEM = """你是审计发现的【去重判定员】。给你【一条新发现】和【若干已有"问题簇"】,
判断这条新发现是否与其中某个簇属于【同一个底层系统缺陷 / 同一机制】——即便它们来自不同 case、
不同引理、不同行号、表面措辞不同。
【保守原则·最重要】只有当你确信是同一底层问题时才判重复;只要拿不准,就判"新"。
绝不因"表面相似/同属一个大主题"就合并——不同根因即使症状相似也算【不同】问题
(例:同是"Obvious 反馈误导",但一个是措辞问题、一个是残余目标渲染问题,属不同缺陷)。
判定优先依据每条的【原始 detail(行号/来源/系统定位)】,而非二手 summary。
判完【调用一次 submit_verdict】:is_duplicate(bool);若 true 给 duplicate_of(命中簇的 id);
若 false(确为新问题)给 canonical_title 与 canonical_summary——简洁、【去 case 化】地概括这个缺陷本质
(不带具体引理名/行号/case 名),供后续比对。reason 给一句判定依据。用中文。"""


# ---------------- audit system prompt (user-tuned; adapted to in-process loop) ----------------
AUDIT_PROMPT = """你是 AoA 证明代理系统的【只读审计员】,实时跟踪 PutnamBench 一个证明 case({case})。

工作方式:反复调用 next_increment() 获取该 case 当前 attempt 日志的新增片段(每次会阻塞约两分钟;
返回里的 invocation 字段标明你正在看哪个 attempt——pass@N 重试会换到新的 invocation,你跟着看即可)。
拿到增量就深读其中的系统提示、工具回显、交互措辞、agent 推理与行为、证明状态;发现问题就调
report_issue 上报。**你的对话本身就是记忆**:你记得之前看过和报过什么,所以同一问题不要重复上报,
但要把前后片段联系起来看。**你无需自己判断 case 何时结束**——case 结束时审计会被自动停止;在那之前
持续轮询即可,某次返回空增量(暂无新内容)也继续轮询。

【目标】开放式发现"这套系统能怎样改进、以更好地帮助 LLM 完成证明"。两类都报:
(A) 系统自身的缺陷/不良设计;(B) LLM 自身的失误、困惑、无谓试错——不评判 LLM,而是借此反推
"系统(更好的工具/提示/反馈/护栏/自动化/引导)本可怎样帮它避免"。不预设清单,主动设想尚未想到的问题类别。

例如(不限于此):① 健全性漏洞(假 proven、oracle/sorry、注释或删除未闭合却判完成 等"证出不成立或未真证之物");
② 回显/反馈与真实证明状态不符——工具回显与内核真实状态矛盾或对不上(如同一步同时报"失败"又报"全部完成";
同一项两种呈现;错误信息里的 id 与可操作 id 命名空间错位);③ 任何奇怪、自相矛盾、或令 LLM 困惑/被误导的
响应——即便不算"错",只要妨碍或带偏 LLM 就值得报。

【报告校准·务必防漏报】不要因"也许是预期/我不太懂 Isabelle/这点小"就压下观察:拿不准就报,并各标
severity(若属实多严重)与 confidence(把握多大),二者独立(允许高严重+低把握)。唯一不必报:系统正常、
LLM 也顺利、确无可改进处(单纯题难、合理重构/试错、单纯慢且系统无更好支持空间)。

【证据与克制】report_issue 的 detail 里给出现象的行号/片段定位(无需逐字照抄),标明来源是客观工具回显/
证明状态还是 agent 主观思考;指明系统哪一处、为何不好/什么后果。可参考这些角度切入(仅供参考·非强制·
清单外同样要报):工具语义与返回、提示词与 schema、交互与反馈设计、错误信息质量、奇怪/误导响应、被诱导出
的 agent 行为、健全性、子代理/fork 交接处的提示传递与拼接。不要强行下结论、不要臆测根因——记录现象、
根因留 OPEN;只读不复现,需要的决定性验证写成"建议人类执行"。

【高危信号】不该泄漏给 agent 的裸内核异常、崩溃、整 case 异常终止(无 SESSION_END、无主 agent 总计 cost、
止于深层 worker、紧随 Cancelled/UNEXPECTED ERROR)——会吞掉整 case 并被误记 FAIL、浪费数小时算力,severity 拔高。

【盲区】你逐次只看到新增片段:跨片段判断标"基于目前所见";标明像单题偶发还是疑似系统性。report 用中文。"""


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%S")


def _norm_severity(raw) -> str:
    """Deterministic map of a free-text severity to {low,medium,high}. Checks
    high → medium → low (so 'low-medium' takes the higher = medium); unknown →
    conservative 'medium'. Only the dedup layer normalizes; raw stays in jsonl."""
    s = str(raw or "").strip().lower()
    if "high" in s or "高" in s:
        return "high"
    if "medium" in s or "med" in s or "中" in s:
        return "medium"
    if "low" in s or "低" in s:
        return "low"
    return "medium"


def _norm_confidence(raw) -> str:
    """Same mapping as severity for the confidence field; unknown → 'medium'."""
    return _norm_severity(raw)


# Per-findings-file monotonic line counter (1-based line number of the just-
# appended record in audit_findings.jsonl). All writes are synchronous on the
# single event loop, so the counter is race-free; only committed AFTER a
# successful append so a failed write never desyncs the count.
_LINE_COUNTERS: dict[str, int] = {}


def _findings_line_base(path: str) -> str:
    key = os.path.realpath(path)
    if key not in _LINE_COUNTERS:
        try:
            with open(path, "rb") as f:
                _LINE_COUNTERS[key] = sum(1 for _ in f)   # resume: existing line count
        except FileNotFoundError:
            _LINE_COUNTERS[key] = 0
    return key


class CaseAuditor:
    """Per-case in-process auditor. Lifecycle driven by the evaluator:
    ``start()`` → ``switch_to(invid)`` (per attempt) → ``await stop()``.

    All public methods are never-raise: auditing must never break ``validate``.
    Everything runs on the evaluator's single asyncio event loop; the only
    blocking file read is offloaded to a thread so it cannot stall the other
    work-stealing workers."""

    def __init__(self, case_name: str, log_dir: str):
        self.case_name = case_name
        self.log_dir = log_dir
        # findings co-locate with the logs by default (shared storage, persists);
        # AUDIT_FINDINGS gives an absolute override. All auditors write from the
        # single evaluator process/event loop, so one shared file is append-safe.
        self._findings_path = FINDINGS or os.path.join(log_dir, "audit_findings.jsonl")
        self._current_invid: str | None = None
        # per-invid incremental-read cursor: {invid: {"offset": int, "size": int}}
        self._offsets: dict[str, dict] = {}
        self._nogrowth = 0
        self._task: asyncio.Task | None = None
        self._cost_total = 0.0
        self._server = self._build_server()

    # ---- evaluator-facing lifecycle (never-raise) ----
    def start(self) -> None:
        try:
            if self._task is None:
                self._task = asyncio.create_task(self._run())
        except Exception as e:  # pragma: no cover - defensive
            self._log(f"start failed: {e}")

    def switch_to(self, invocation_id: str) -> None:
        """Tell the auditor which attempt's log to follow now. Called the moment
        an invid is minted (``_make_invocation_id``); single-threaded so a plain
        attribute set is race-free w.r.t. the polling coroutine."""
        try:
            self._current_invid = invocation_id
            # Reset (not setdefault) the cursor: a repeated invid means the dir
            # was renamed to .old_<ts> and recreated fresh (pass@N / resume), so
            # the prior offset is stale and must restart at 0.
            self._offsets[invocation_id] = {"offset": 0, "size": -1}
            self._nogrowth = 0
        except Exception as e:  # pragma: no cover - defensive
            self._log(f"switch_to failed: {e}")

    async def stop(self) -> None:
        t = self._task
        self._task = None
        if t is None or t.done():
            return
        t.cancel()
        try:
            await t
        except (asyncio.CancelledError, Exception):
            pass  # cancellation drives query()'s teardown; nothing to surface

    # ---- internals ----
    def _log(self, msg: str) -> None:
        print(f"[audit:{self.case_name}] {msg}", flush=True)

    def _tool_text(self, payload: dict) -> dict:
        return {"content": [{"type": "text", "text": json.dumps(payload, ensure_ascii=False)}]}

    def _build_server(self):
        auditor = self

        @tool("next_increment",
              "阻塞约两分钟后,返回本 case 当前 attempt 日志(interaction.yaml)自上次以来的新增片段。",
              {})
        async def next_increment(args):
            return await auditor._read_increment()

        @tool("report_issue",
              "上报一条审计发现(只在确有问题时调用;同一问题在本对话内已报过就不要重复)。",
              {"severity": str, "confidence": str, "title": str, "detail": str})
        async def report_issue(args):
            rec = auditor._write_finding(args)            # raw append (immutable) — always
            if AUDIT_DEDUP and rec is not None:
                # best-effort online dedup; a failure/timeout MUST NOT break the
                # auditor or lose the finding (raw is already on disk).
                try:
                    dd = _get_deduper(auditor._findings_path)
                    await asyncio.wait_for(dd.consider(rec), timeout=AUDIT_DEDUP_TIMEOUT)
                except Exception as e:
                    auditor._log(f"dedup best-effort skipped: {e}")
            return {"content": [{"type": "text", "text": "recorded"}]}

        return create_sdk_mcp_server("audit", "1.0.0", tools=[next_increment, report_issue])

    def _poll_delay(self) -> int:
        return POLL_SECONDS + min(self._nogrowth, IDLE_MAX_MULT) * IDLE_STEP

    async def _read_increment(self) -> dict:
        await asyncio.sleep(self._poll_delay())
        invid = self._current_invid
        if not invid:
            return self._tool_text({"status": "waiting", "new_chars": 0, "increment": "",
                                    "note": "证明尚未开始(还没有 invocation)"})
        path = os.path.join(self.log_dir, invid, "interaction.yaml")
        try:
            text = await asyncio.to_thread(self._read_file_increment, invid, path)
        except Exception as e:
            return self._tool_text({"status": "read_error", "error": str(e),
                                    "invocation": invid, "new_chars": 0, "increment": ""})
        if text.strip():
            self._nogrowth = 0
        else:
            self._nogrowth += 1
        return self._tool_text({"status": "ok", "invocation": invid,
                                "new_chars": len(text), "increment": text})

    def _read_file_increment(self, invid: str, path: str) -> str:
        """Return new complete-document bytes (decoded) since the last read of
        *invid*'s interaction.yaml. Document-boundary-safe (same technique as
        watcher.scan_logs): never hand back a partially-written trailing doc
        unless the file has gone quiescent. Runs in a worker thread."""
        st = self._offsets.setdefault(invid, {"offset": 0, "size": -1})
        off, last_size = st["offset"], st["size"]
        if not os.path.exists(path):
            return ""
        size = os.path.getsize(path)
        if size < off:            # truncated/replaced — reset defensively
            off = 0
        if size <= off:
            st["size"] = size
            return ""
        with open(path, "rb") as fh:
            fh.seek(off)
            chunk = fh.read()
        # parts[:-1] are separator-terminated → complete docs; parts[-1] is the
        # trailing doc, complete only if the file is quiescent (size unchanged).
        parts = chunk.split(_DOC_SEP)
        consume_upto = len(chunk) - len(parts[-1])
        if parts[-1].strip() and size == last_size:
            consume_upto = len(chunk)
        consumed = chunk[:consume_upto]
        st["offset"] = off + consume_upto
        st["size"] = size
        return consumed.decode("utf-8", errors="replace")

    def _write_finding(self, args: dict) -> dict | None:
        """Append the raw finding to the jsonl (immutable log) and return the
        record (incl. its 1-based ``line`` in the file) for the deduper, or
        ``None`` on failure. Synchronous (no await) → atomic on the event loop;
        the line counter is committed only after a successful write."""
        try:
            d = os.path.dirname(self._findings_path)
            if d:
                os.makedirs(d, exist_ok=True)
            key = _findings_line_base(self._findings_path)
            line_no = _LINE_COUNTERS[key] + 1            # intended; committed after write
            rec = {
                "ts": _now_iso(),
                "case": self.case_name,
                "invocation": self._current_invid,
                "severity": args.get("severity", ""),
                "confidence": args.get("confidence", ""),
                "title": args.get("title", ""),
                "detail": args.get("detail", ""),
                "line": line_no,
            }
            with open(self._findings_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            _LINE_COUNTERS[key] = line_no                # commit only on success
            return rec
        except Exception as e:  # pragma: no cover - defensive
            self._log(f"write_finding failed: {e}")
            return None

    def _options(self) -> ClaudeAgentOptions:
        return ClaudeAgentOptions(
            system_prompt=AUDIT_PROMPT.format(case=self.case_name),
            model=MODEL,
            effort=EFFORT,
            tools=[],                         # H1: disable all built-in tools
            mcp_servers={"audit": self._server},
            allowed_tools=_ALLOWED,           # auto-allow exactly our two tools
            disallowed_tools=_DISALLOWED,     # belt-and-suspenders
            strict_mcp_config=True,           # ignore project/global MCP config
            permission_mode="dontAsk",        # H1: NOT bypassPermissions
            max_turns=MAX_TURNS,
            max_budget_usd=MAX_BUDGET_USD,    # H4: per-case cost cap
        )

    async def _run(self) -> None:
        """The long-lived audit agent. Never-raise except for cancellation,
        which must propagate so query()'s teardown terminates the subprocess."""
        prompt = ("开始持续审计本 case。反复调用 next_increment() 取新增日志、深读分析,"
                  "发现问题就调 report_issue;持续轮询,审计会在 case 结束时自动停止。")
        try:
            async for msg in query(prompt=prompt, options=self._options()):
                if isinstance(msg, ResultMessage):
                    cost = getattr(msg, "total_cost_usd", None)
                    if isinstance(cost, (int, float)):
                        self._cost_total += cost
                    self._log(f"结束 subtype={getattr(msg, 'subtype', '?')} "
                              f"cost={cost} session={getattr(msg, 'session_id', None)} "
                              f"total_cost={self._cost_total:.4f}")
        except asyncio.CancelledError:
            raise
        except Exception as e:
            self._log(f"agent 异常: {e}")


# ---------------- online cross-case dedup ----------------
_SEV = {"low": 1, "medium": 2, "high": 3}
_SEV_INV = {1: "low", 2: "medium", 3: "high"}


def _head(s, cap: int) -> str:
    """Head-truncate (keep the start, where the one-liner + first evidence live)."""
    s = s or ""
    return s if len(s) <= cap else (s[:cap] + "…[截断]")


def _truthy(x) -> bool:
    if isinstance(x, bool):
        return x
    return str(x).strip().lower() in ("true", "1", "yes", "y", "是", "重复", "duplicate")


class _Deduper:
    """Process-wide (per findings file) online cross-case dedup, shared by every
    CaseAuditor on the single evaluator event loop. Maintains a DERIVED view
    (canonical issue clusters) in ``audit_dedup_state.json`` (sole source of
    truth, atomic-written) + a human-readable ``audit_issues.md``. The raw
    ``audit_findings.jsonl`` is never touched here (it is the immutable log).

    Two-phase lock: embed/knn/QA run OUTSIDE ``self._lock``; only the
    deterministic state mutation + atomic flush hold it (no ``await`` inside).
    Conservative: a cluster is only created/merged on an explicit QA verdict;
    QA failure/timeout → finding stays in jsonl only (no half-baked cluster).
    """

    # Lazy-initialized in _lazy(); declared Any so member access below is clean.
    _provider: Any
    _np: Any
    _faiss: Any

    def __init__(self, findings_path: str):
        self.findings_path = findings_path
        d = os.path.dirname(os.path.realpath(findings_path)) or "."
        self.state_path = os.path.join(d, "audit_dedup_state.json")
        self.report_path = os.path.join(d, "audit_issues.md")
        self.issues: list[dict] = []
        self.next_id = 1
        self._lock = None          # lazy asyncio.Lock (bound to running loop)
        self._sem = None           # lazy module-singleton asyncio.Semaphore (QA peak)
        self._provider = None      # lazy embedding provider
        self._np = None            # lazy numpy
        self._faiss = None         # lazy faiss
        self._model = None         # embedding model name (set in _lazy; recorded in state)
        self._cost_total = 0.0
        self._load()

    def _log(self, msg: str) -> None:
        print(f"[dedup] {msg}", flush=True)

    # ---- lazy resources ----
    def _lazy(self) -> None:
        if self._provider is not None:
            return
        import numpy as np
        import faiss
        from Isabelle_Semantic_Embedding.semantics import _resolve_embedding_config_env
        from Isabelle_Semantic_Embedding.semantic_embedding import make_embedding_provider
        self._np = np
        self._faiss = faiss
        drv, base, model = _resolve_embedding_config_env()
        self._model = model
        self._provider = make_embedding_provider(drv, base, model)
        self._log(f"embedder ready: {model}")

    def _get_lock(self):
        if self._lock is None:
            self._lock = asyncio.Lock()
        return self._lock

    def _get_sem(self):
        if self._sem is None:
            self._sem = asyncio.Semaphore(AUDIT_DEDUP_QA_CONC)
        return self._sem

    # ---- vectors ----
    def _sum_of(self, iss: dict):
        s = iss.get("_sum")
        if s is None:
            s = self._np.frombuffer(base64.b64decode(iss["vec_sum_b64"]), dtype="float32").copy()
            iss["_sum"] = s
        return s

    def _unit(self, v):
        a = self._np.ascontiguousarray(v, dtype="float32").reshape(1, -1)
        self._faiss.normalize_L2(a)            # in place; 1 - L2²/2 = cosine for unit vecs
        return a[0]

    async def _embed_query(self, text: str):
        """Qwen3 M2 query side: manual Instruct/Query prefix, sent BARE
        (role='document') so the provider's own Isabelle/HOL task is bypassed."""
        wrapped = f"Instruct: {_DEDUP_INSTRUCT}\nQuery:{text}"
        r = await self._provider.embed([wrapped], role="document")
        return self._np.asarray(r.vectors[0], dtype="float32")

    async def _embed_doc(self, text: str):
        """Qwen3 M2 document side: bare text."""
        r = await self._provider.embed([text], role="document")
        return self._np.asarray(r.vectors[0], dtype="float32")

    def _knn(self, qvec):
        """Synchronous snapshot + faiss.knn → up to TOPK candidate issues. No
        await → consistent w.r.t. concurrent under-lock mutations on the loop."""
        if not self.issues:
            return []
        np, faiss = self._np, self._faiss
        snap = list(self.issues)
        mat = np.ascontiguousarray(
            np.stack([self._unit(self._sum_of(i) / max(i.get("n", 1), 1)) for i in snap]),
            dtype="float32")
        q = np.ascontiguousarray(self._unit(qvec).reshape(1, -1), dtype="float32")
        k = min(AUDIT_DEDUP_TOPK, len(snap))
        idx = faiss.knn(q, mat, k)[1]          # (distances, indices) → indices only
        return [snap[j] for j in idx[0] if 0 <= j < len(snap)]

    # ---- QA agent (short-lived ClaudeSDKClient; off the critical path) ----
    def _qa_prompt(self, rec: dict, cands: list[dict]) -> str:
        nf = (f"# 新发现\n- title: {rec.get('title','')}\n"
              f"- severity: {rec.get('severity','')} · confidence: {rec.get('confidence','')} "
              f"· case: {rec.get('case','')}\n- detail:\n{_head(rec.get('detail',''), _FINDING_CAP)}\n")
        lines = ["# 已有问题簇候选(按相似度排序)"]
        for c in cands:
            lines.append(f"\n## id={c['id']}  occurrences={c.get('occurrences',0)}  severity={c.get('severity','')}")
            lines.append(f"- title: {c.get('title','')}")
            lines.append(f"- summary: {c.get('summary','')}")
            lines.append(f"- repr_detail: {_head(c.get('repr_detail',''), _REPR_CAP)}")
        return (nf + "\n" + "\n".join(lines) +
                "\n\n判断这条新发现是否与上面某个簇属于同一底层系统缺陷(保守判定),"
                "然后调用 submit_verdict 一次。")

    async def _qa(self, rec: dict, cands: list[dict]) -> dict:
        holder: dict = {}

        @tool("submit_verdict",
              "提交去重判定(只调用一次)。is_duplicate=true 时给 duplicate_of(命中簇 id);"
              "=false(新问题)时给 canonical_title 与去 case 化的 canonical_summary。",
              {"is_duplicate": bool, "duplicate_of": str, "reason": str,
               "canonical_title": str, "canonical_summary": str})
        async def submit_verdict(args):
            holder.update(args)
            return {"content": [{"type": "text", "text": "recorded"}]}

        server = create_sdk_mcp_server("dedup", "1.0.0", tools=[submit_verdict])
        opts = ClaudeAgentOptions(
            system_prompt=_DEDUP_QA_SYSTEM,
            model=AUDIT_DEDUP_MODEL, effort=EFFORT,
            tools=[], mcp_servers={"dedup": server},
            allowed_tools=_DEDUP_ALLOWED, disallowed_tools=_DISALLOWED,
            strict_mcp_config=True, permission_mode="dontAsk",
            max_turns=AUDIT_DEDUP_QA_TURNS,
        )
        prompt = self._qa_prompt(rec, cands)
        async with self._get_sem():
            # __aexit__ disconnects (terminates the subprocess); off the critical
            # path, so no explicit interrupt() needed (avoids its 60s control timeout).
            async with ClaudeSDKClient(options=opts) as c:
                await c.query(prompt)
                async for msg in c.receive_response():
                    if isinstance(msg, ResultMessage):
                        cost = getattr(msg, "total_cost_usd", None)
                        if isinstance(cost, (int, float)):
                            self._cost_total += cost
        return holder

    # ---- state mutation (called ONLY under self._lock; strictly no await) ----
    def _agg_severity(self, instances: list[dict]) -> str:
        pairs = [(_SEV[_norm_severity(i.get("raw_severity"))],
                  _SEV[_norm_confidence(i.get("confidence"))]) for i in instances]
        if not pairs:
            return "low"
        wsum = sum(s * c for s, c in pairs)
        csum = sum(c for _, c in pairs)
        base = round(wsum / csum) if csum else 1                  # confidence-weighted: low-conf doesn't inflate
        sentinel = max((s for s, c in pairs if c >= 2), default=0)  # ≥medium-conf high not averaged away
        return _SEV_INV[max(1, min(3, max(base, sentinel)))]

    def _agg_confidence(self, instances: list[dict]) -> str:
        return _SEV_INV[max((_SEV[_norm_confidence(i.get("confidence"))] for i in instances), default=1)]

    def _add_instance(self, iss: dict, rec: dict, dvec) -> None:
        iss["instances"].append({
            "case": rec.get("case"), "invocation": rec.get("invocation"),
            "ts": rec.get("ts"), "raw_title": rec.get("title"),
            "raw_severity": rec.get("severity"), "confidence": rec.get("confidence"),
            "line": rec.get("line"),
        })
        iss["occurrences"] = len(iss["instances"])
        iss["last_seen"] = rec.get("ts")
        s = self._sum_of(iss) + dvec                              # running sum (UN-normalized; order-independent)
        iss["_sum"] = s
        iss["n"] = iss.get("n", 0) + 1
        iss["vec_sum_b64"] = base64.b64encode(s.astype("float32").tobytes()).decode("ascii")
        iss["severity"] = self._agg_severity(iss["instances"])
        iss["confidence"] = self._agg_confidence(iss["instances"])

    def _apply(self, rec: dict, dvec, verdict: dict) -> None:
        if not verdict or "is_duplicate" not in verdict:
            self._log("QA 无 verdict;跳过(原始 finding 已在 jsonl 保底)")
            return
        if _truthy(verdict.get("is_duplicate")):
            tgt = verdict.get("duplicate_of") or ""
            iss = next((i for i in self.issues if i["id"] == tgt), None)
            if iss is not None:
                self._add_instance(iss, rec, dvec)
                return
            self._log(f"QA 判重但 duplicate_of={tgt!r} 不存在;按新簇处理")
        title = (rec.get("title") or "").strip()
        iid = f"AUDIT-{self.next_id:04d}"
        self.next_id += 1
        iss = {
            "id": iid,
            "title": (verdict.get("canonical_title") or title).strip() or title,
            "summary": (verdict.get("canonical_summary") or title).strip(),
            "severity": "low", "confidence": "low",
            "occurrences": 0, "first_seen": rec.get("ts"), "last_seen": rec.get("ts"),
            "repr_detail": _head(rec.get("detail", ""), _REPR_CAP),
            "instances": [], "n": 0,
            "_sum": self._np.zeros(dvec.shape[0], dtype="float32"),
        }
        self.issues.append(iss)
        self._add_instance(iss, rec, dvec)

    # ---- persistence (atomic; state.json is the sole source of truth) ----
    def _atomic_write(self, path: str, text: str) -> None:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)

    def _save(self) -> None:
        dim = None
        if self.issues:
            s0 = self.issues[0].get("_sum")
            if s0 is not None:
                dim = int(len(s0))
        data = {"version": 1, "model": self._model, "dim": dim, "next_id": self.next_id,
                "issues": [{k: v for k, v in i.items() if not k.startswith("_")} for i in self.issues]}
        self._atomic_write(self.state_path, json.dumps(data, ensure_ascii=False))
        self._atomic_write(self.report_path, self._render_md())

    def _validate_loaded(self, data: dict, issues) -> None:
        """Reject a JSON-valid but semantically/dimensionally corrupt state, so a
        bad cluster never sticks in self.issues and silently breaks _knn for every
        remaining finding of the run (decision C: any corruption → .corrupt backup
        + empty restart, done by the caller _load). Raises ValueError on any defect.

        tier 1 (stdlib only): each cluster's vec_sum_b64 must be present, base64-
        decodable, float32-aligned, the SAME dim across all clusters, n a positive
        int. tier 2 (needs semantics, skipped on ImportError): the recorded
        embedding model must equal the current one — a different model embeds at a
        different dim and would crash np.stack in _knn against the stored vectors."""
        if not isinstance(issues, list):
            raise ValueError("issues is not a list")
        if not issues:
            return
        dim = None
        for i, iss in enumerate(issues):
            cid = iss.get("id", i)
            b64 = iss.get("vec_sum_b64")
            if not isinstance(b64, str) or not b64:
                raise ValueError(f"cluster {cid}: missing/empty vec_sum_b64")
            raw = base64.b64decode(b64)                      # raises on garbled base64
            if len(raw) == 0 or len(raw) % 4 != 0:
                raise ValueError(f"cluster {cid}: vec byte length {len(raw)} not float32-aligned")
            d = len(raw) // 4
            if dim is None:
                dim = d
            elif d != dim:
                raise ValueError(f"cluster {cid}: dim {d} != {dim} (inconsistent across clusters)")
            n = iss.get("n")
            if not isinstance(n, int) or n < 1:
                raise ValueError(f"cluster {cid}: invalid n={n!r}")
        saved_dim = data.get("dim")
        if isinstance(saved_dim, int) and dim is not None and saved_dim != dim:
            raise ValueError(f"recorded dim {saved_dim} != actual {dim}")
        saved_model = data.get("model")
        if saved_model:
            try:
                from Isabelle_Semantic_Embedding.semantics import _resolve_embedding_config_env
                cur_model = _resolve_embedding_config_env()[2]
            except Exception as e:   # cannot resolve → dedup won't run anyway; don't destroy state
                self._log(f"WARN: cannot resolve current embedding model for state check ({e}); "
                          "skipping model-match validation")
            else:
                if saved_model != cur_model:
                    raise ValueError(f"embedding model changed: state={saved_model!r} now={cur_model!r}")

    def _load(self) -> None:
        if not os.path.exists(self.state_path):
            return
        try:
            with open(self.state_path, encoding="utf-8") as f:
                data = json.load(f)
            issues = data.get("issues", [])
            self._validate_loaded(data, issues)             # semantic/dim/model corruption → raise
            self.issues = issues
            self.next_id = int(data.get("next_id", len(issues) + 1))
            self._log(f"loaded {len(self.issues)} clusters from {self.state_path}")
        except Exception as e:
            bak = self.state_path + ".corrupt"
            try:
                os.replace(self.state_path, bak)
            except Exception:
                bak = "(backup failed)"
            self._log(f"state 损坏/不兼容,弃用 ({e});已备份到 {bak},空簇重启")
            self.issues = []
            self.next_id = 1

    def _render_md(self) -> str:
        items = sorted(self.issues,
                       key=lambda i: (_SEV.get(i.get("severity", "low"), 1), i.get("occurrences", 0)),
                       reverse=True)
        out = [f"# 审计去重报告  ({len(self.issues)} 簇 · 累计 QA 成本 ${self._cost_total:.4f} · {_now_iso()})", ""]
        for i in items:
            insts = i.get("instances", [])
            out.append(f"## [{i['id']}] {i.get('title','')}")
            out.append(f"- severity **{i.get('severity')}** · confidence {i.get('confidence')} "
                       f"· occurrences **{i.get('occurrences')}**")
            out.append(f"- first_seen {i.get('first_seen')} · last_seen {i.get('last_seen')}")
            out.append(f"- summary: {i.get('summary','')}")
            out.append(f"- 实例 {len(insts)}:")
            for ins in insts[:80]:
                out.append(f"    - case={ins.get('case')} invid={ins.get('invocation')} "
                           f"line={ins.get('line')} sev={ins.get('raw_severity')} "
                           f"conf={ins.get('confidence')} ts={ins.get('ts')}")
            if len(insts) > 80:
                out.append(f"    - …(+{len(insts) - 80} more)")
            out.append(f"- repr_detail:\n\n{i.get('repr_detail','')}\n")
            out.append("")
        return "\n".join(out)

    # ---- orchestration (best-effort; NEVER raises) ----
    async def consider(self, rec: dict) -> None:
        try:
            self._lazy()
            text = ((rec.get("title") or "").strip() + "\n" + (rec.get("detail") or "").strip()).strip()
            if not text:
                return
            qvec = await self._embed_query(text)            # outside lock
            cands = self._knn(qvec)                          # sync snapshot+knn (no await)
            if not cands:
                title = (rec.get("title") or "").strip()
                verdict = {"is_duplicate": False, "canonical_title": title, "canonical_summary": title}
            else:
                verdict = await self._qa(rec, cands)         # outside lock, inside QA semaphore
            dvec = await self._embed_doc(text)               # outside lock
            async with self._get_lock():                     # ── critical section: NO await below ──
                self._apply(rec, dvec, verdict)
                self._save()
        except Exception as e:
            self._log(f"consider failed: {e}")


_DEDUPERS: dict[str, _Deduper] = {}


def _get_deduper(findings_path: str) -> _Deduper:
    """Process-wide singleton per (realpath-normalized) findings file."""
    key = os.path.realpath(findings_path)
    dd = _DEDUPERS.get(key)
    if dd is None:
        dd = _Deduper(findings_path)
        _DEDUPERS[key] = dd
    return dd


# ---------------- offline self-test + local one-shot debug ----------------
async def _selftest():
    """Offline: no cluster, no Opus. Verify option/server construction (H1/H4
    field names) and the document-boundary-safe incremental reader."""
    import tempfile
    print("== option/server construction (H1/H4) ==")
    a = CaseAuditor(case_name="demo", log_dir="/tmp/fleet_audit_selftest")
    opts = a._options()
    assert opts.tools == [], "tools must be [] (H1)"
    assert opts.permission_mode == "dontAsk", "must use dontAsk, not bypassPermissions (H1)"
    assert opts.allowed_tools == _ALLOWED
    assert opts.strict_mcp_config is True
    assert opts.max_budget_usd == MAX_BUDGET_USD   # None = no cap by default (user); env AUDIT_MAX_BUDGET_USD sets one
    assert opts.max_turns == MAX_TURNS
    print(f"  tools={opts.tools} perm={opts.permission_mode} budget={opts.max_budget_usd} "
          f"turns={opts.max_turns} model={opts.model}")
    print(f"  server={type(a._server).__name__} allowed={opts.allowed_tools}")

    print("== incremental reader (doc-boundary, no 60K cap, pass@N switch) ==")
    with tempfile.TemporaryDirectory() as d:
        a2 = CaseAuditor(case_name="demo2", log_dir=d)
        inv1 = "abc_1"
        os.makedirs(os.path.join(d, inv1))
        p = os.path.join(d, inv1, "interaction.yaml")
        a2.switch_to(inv1)
        # one complete doc + a partial trailing doc (not quiescent yet)
        with open(p, "w", encoding="utf-8") as f:
            f.write("---\nevent: SESSION_START\n\n---\nevent: partial")
        t1 = a2._read_file_increment(inv1, p)
        assert "SESSION_START" in t1, t1
        assert "partial" not in t1, "trailing partial doc must be held back"
        # same size next poll → quiescent → trailing doc flushed
        t2 = a2._read_file_increment(inv1, p)
        assert "partial" in t2, t2
        # append a large doc (>60000 chars) → must NOT be truncated (M7/M8)
        big = "x" * 70000
        with open(p, "a", encoding="utf-8") as f:
            f.write(f"\n---\nbig: {big}\n")
        a2._read_file_increment(inv1, p)               # grew, hold trailing
        t3 = a2._read_file_increment(inv1, p)          # quiescent → flush
        assert len(t3) >= 70000, f"increment truncated! len={len(t3)}"
        # pass@N: switch to a new invid → independent cursor, stale dir untouched
        inv2 = "def_2"
        os.makedirs(os.path.join(d, inv2))
        p2 = os.path.join(d, inv2, "interaction.yaml")
        with open(p2, "w", encoding="utf-8") as f:
            f.write("---\nevent: SESSION_START\nattempt: 2\n")
        a2.switch_to(inv2)
        assert a2._current_invid == inv2
        a2._read_file_increment(inv2, p2)              # trailing (only) doc held back
        t4 = a2._read_file_increment(inv2, p2)         # quiescent → flush
        assert "attempt: 2" in t4, t4
        assert inv1 in a2._offsets and inv2 in a2._offsets, "per-invid cursors kept separate"
        print("  reader OK (boundary held until quiescent, 60K cap removed, per-invid cursors)")

    rec = a._write_finding({"severity": "low", "confidence": "low",
                            "title": "selftest", "detail": "selftest record"})
    assert rec is not None and isinstance(rec.get("line"), int) and rec["line"] >= 1, rec
    print(f"  findings write OK -> {a._findings_path} (rec line={rec['line']})")

    print("== dedup pure-function checks (offline, no network) ==")
    assert _norm_severity("中") == "medium" and _norm_severity("low-medium") == "medium"
    assert _norm_severity("HIGH") == "high" and _norm_severity("低") == "low" and _norm_severity("???") == "medium"
    assert _truthy(True) and _truthy("yes") and not _truthy("no") and not _truthy(False)
    assert _head("abcdef", 3) == "abc…[截断]" and _head("ab", 5) == "ab"
    with tempfile.TemporaryDirectory() as dd_dir:
        fp = os.path.join(dd_dir, "audit_findings.jsonl")
        dd = _Deduper(fp)
        # J: a lone high-severity / LOW-confidence guess must NOT pin the cluster high
        lo = [{"raw_severity": "high", "confidence": "low"},
              {"raw_severity": "low", "confidence": "high"},
              {"raw_severity": "low", "confidence": "high"}]
        assert dd._agg_severity(lo) == "low", dd._agg_severity(lo)
        # J sentinel: a >=medium-confidence high is NOT averaged away
        hi = [{"raw_severity": "high", "confidence": "high"},
              {"raw_severity": "low", "confidence": "low"}]
        assert dd._agg_severity(hi) == "high", dd._agg_severity(hi)
        # atomic save + reload (a VALID state round-trips)
        import numpy as _np0
        goodvec = base64.b64encode(_np0.ones(8, dtype="float32").tobytes()).decode("ascii")
        dd.next_id = 7
        dd.issues = [{"id": "AUDIT-0001", "title": "t", "summary": "s", "severity": "high",
                      "confidence": "low", "occurrences": 1, "first_seen": "x", "last_seen": "x",
                      "repr_detail": "d", "instances": [{"case": "c", "line": 3}], "n": 1,
                      "vec_sum_b64": goodvec}]
        dd._save()
        assert _Deduper(fp).next_id == 7 and len(_Deduper(fp).issues) == 1
        # JSON-valid but SEMANTICALLY corrupt (empty vec) → validated as corrupt →
        # .corrupt backup + empty restart (NOT loaded as a sticky bad cluster).
        bad = json.loads(open(dd.state_path, encoding="utf-8").read())
        bad["issues"][0]["vec_sum_b64"] = ""
        with open(dd.state_path, "w", encoding="utf-8") as f:
            f.write(json.dumps(bad, ensure_ascii=False))
        ddx = _Deduper(fp)
        assert ddx.issues == [] and ddx.next_id == 1, "semantic-corrupt state must degrade to empty"
        assert os.path.exists(dd.state_path + ".corrupt"), "semantic-corrupt state must be backed up"
        # JSON-broken state → also degrades
        with open(dd.state_path, "w", encoding="utf-8") as f:
            f.write("{ not valid json ")
        dd3 = _Deduper(fp)
        assert dd3.issues == [] and dd3.next_id == 1, "corrupt state must degrade to empty"
    print("  dedup OK (severity agg + sentinel, truthy/head, save+reload, semantic+json corrupt degrade)")
    try:
        import numpy as _np
        v = _np.arange(8, dtype="float32") + 0.5
        v2 = _np.frombuffer(base64.b64decode(base64.b64encode(v.tobytes()).decode("ascii")), dtype="float32")
        assert _np.array_equal(v, v2), "base64 float32 round-trip"
        print("  vector base64 round-trip OK")
    except ImportError:
        print("  (numpy unavailable; skipped vector round-trip)")
    print("selftest OK")


async def _one(log_dir: str, invid: str):
    """Local LIVE debug (needs claude CLI auth): run a real audit agent against
    an existing local <log_dir>/<invid>/interaction.yaml. Use a tiny poll and a
    small turn cap, e.g.:
        AUDIT_POLL_SECONDS=5 AUDIT_MAX_TURNS=4 \\
        python tools/aoa_putnam_eval/fleet_audit_agents.py --one <log_dir> <invid>
    Doubles as the launch-time check that tools=[] still permits mcp tool calls."""
    a = CaseAuditor(case_name=f"debug:{invid}", log_dir=log_dir)
    a.switch_to(invid)
    a.start()
    t = a._task
    try:
        if t is not None:
            await t
    except asyncio.CancelledError:
        pass


async def _replay(jsonl_path: str):
    """Validate the ONLINE dedup on a real corpus: feed an existing
    ``audit_findings.jsonl`` through the SAME ``_Deduper.consider()`` path the
    live ``report_issue`` uses. State/report land in a fresh temp dir. Needs the
    ``claude`` CLI auth (QA agent) + ``EMBEDDING_API_KEY`` (embeddings). Usage:
        python tools/aoa_putnam_eval/fleet_audit_agents.py --replay <findings.jsonl>"""
    import tempfile
    d = tempfile.mkdtemp(prefix="audit_dedup_replay_")
    dd = _Deduper(os.path.join(d, "audit_findings.jsonl"))
    with open(jsonl_path, encoding="utf-8") as f:
        recs = [json.loads(ln) for ln in f if ln.strip()]
    print(f"replay {len(recs)} findings → {d}", flush=True)
    for k, rec in enumerate(recs, 1):
        rec.setdefault("line", k)
        await dd.consider(rec)
        print(f"  [{k}/{len(recs)}] clusters={len(dd.issues)} cost=${dd._cost_total:.4f}", flush=True)
    print(f"\n=== {len(dd.issues)} clusters · QA cost ${dd._cost_total:.4f} ===\n", flush=True)
    print(dd._render_md())
    print(f"\nstate:  {dd.state_path}\nreport: {dd.report_path}", flush=True)


if __name__ == "__main__":
    import sys
    if "--selftest" in sys.argv:
        asyncio.run(_selftest())
    elif "--one" in sys.argv:
        i = sys.argv.index("--one")
        asyncio.run(_one(sys.argv[i + 1], sys.argv[i + 2]))
    elif "--replay" in sys.argv:
        i = sys.argv.index("--replay")
        asyncio.run(_replay(sys.argv[i + 1]))
    else:
        print("usage: fleet_audit_agents.py [--selftest | --one <log_dir> <invid> | --replay <findings.jsonl>]")
        print("  (this module is normally driven in-process by "
              "MinilangAgent_PutnamBench_Audited, not run standalone)")
