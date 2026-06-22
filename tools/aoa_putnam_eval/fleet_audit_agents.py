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
"""
import asyncio
import json
import os
import time

from claude_agent_sdk import (
    tool, create_sdk_mcp_server, ClaudeAgentOptions, query, ResultMessage,
)

# ---------------- configuration (all env-overridable) ----------------
POLL_SECONDS    = int(os.environ.get("AUDIT_POLL_SECONDS", "120"))    # base block per next_increment
IDLE_STEP       = int(os.environ.get("AUDIT_IDLE_STEP", "60"))        # extra sleep per consecutive empty poll
IDLE_MAX_MULT   = int(os.environ.get("AUDIT_IDLE_MAX_MULT", "4"))     # cap on the idle-backoff multiplier
MODEL           = os.environ.get("AUDIT_MODEL", "claude-opus-4-8")
EFFORT          = os.environ.get("AUDIT_EFFORT", "high")
FINDINGS        = os.environ.get("AUDIT_FINDINGS")                   # abs override; default = <log_dir>/audit_findings.jsonl
MAX_TURNS       = int(os.environ.get("AUDIT_MAX_TURNS", "2000"))      # safety backstop; real bound = case end (cancel)
_BUDGET_ENV     = os.environ.get("AUDIT_MAX_BUDGET_USD")
MAX_BUDGET_USD  = float(_BUDGET_ENV) if _BUDGET_ENV else None         # None = no cap (user choice); env sets a per-case $ cap

# Built-in tools to explicitly disallow as belt-and-suspenders on top of tools=[].
_DISALLOWED = ["Bash", "Edit", "Write", "Read", "NotebookEdit",
               "WebFetch", "WebSearch", "Glob", "Grep", "Task", "TodoWrite"]
_DOC_SEP = b"\n---\n"   # interaction.yaml multi-doc separator (model.py _append_yaml)
_ALLOWED = ["mcp__audit__next_increment", "mcp__audit__report_issue"]


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
            self._offsets.setdefault(invocation_id, {"offset": 0, "size": -1})
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
            auditor._write_finding(args)
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

    def _write_finding(self, args: dict) -> None:
        try:
            d = os.path.dirname(self._findings_path)
            if d:
                os.makedirs(d, exist_ok=True)
            rec = {
                "ts": _now_iso(),
                "case": self.case_name,
                "invocation": self._current_invid,
                "severity": args.get("severity", ""),
                "confidence": args.get("confidence", ""),
                "title": args.get("title", ""),
                "detail": args.get("detail", ""),
            }
            with open(self._findings_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        except Exception as e:  # pragma: no cover - defensive
            self._log(f"write_finding failed: {e}")

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

    a._write_finding({"severity": "low", "confidence": "low",
                      "title": "selftest", "detail": "selftest record"})
    print(f"  findings write OK -> {a._findings_path} (default = <log_dir>/audit_findings.jsonl)")
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


if __name__ == "__main__":
    import sys
    if "--selftest" in sys.argv:
        asyncio.run(_selftest())
    elif "--one" in sys.argv:
        i = sys.argv.index("--one")
        asyncio.run(_one(sys.argv[i + 1], sys.argv[i + 2]))
    else:
        print("usage: fleet_audit_agents.py [--selftest | --one <log_dir> <invid>]")
        print("  (this module is normally driven in-process by "
              "MinilangAgent_PutnamBench_Audited, not run standalone)")
