#!/usr/bin/env python3
"""Orchestrator (watcher) for the MathBench missing-lemma loop.

Runs PutnamBench cases one at a time through the AoA agent (DeepSeek.V4-pro by
default) with the missing-lemma survey enabled (AOA_MISSING_LEMMA_SURVEY),
tails the per-invocation ``missing_lemmas.yaml`` logs while the case runs,
confirms each claim against the Isabelle2025-2 + afp-2026-05-13 sources via a
headless Claude Code agent (Agent SDK, opus 4.8, built-in auto permission
mode; results submitted through a validated in-process MCP answer tool), and —
when a claim is confirmed as a missing import theory — kills the run, drives
Phase 2 (import + reconcile + heap rebuild + REPL restart + semantic collect,
via another Claude Code agent plus deterministic shell steps), then re-runs
the same case.

Design record: ``MISSING_LEMMA_LOOP.md`` at the repo root.

State lives in ``missing_lemma_loop_state/``:
  - ``ledger.json``         every claim ever reported + its adjudication
  - ``offsets.json``        per-log-file scan offsets
  - ``heap_theories.txt``   theories currently in the MathBench_Prover heap
  - ``verdicts/``           search-agent verdict JSONs
  - ``phase2/``             phase-2 agent result JSONs + transcripts
  - ``accept_candidates.md``  divergences the phase-2 agent would have ACCEPTed
  - ``report.md``           regenerated human-readable report

Subcommands:
  run        the main loop (default)
  scan       offline: ingest new missing_lemmas.yaml entries into the ledger
  report     regenerate report.md from the ledger
  heap-dump  refresh heap_theories.txt from `isabelle build -n -l`
"""

from __future__ import annotations

import argparse
import asyncio
import concurrent.futures
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[2]
STATE_DIR = ROOT / "missing_lemma_loop_state"
PROMPT_DIR = Path(__file__).resolve().parent / "prompts"

# permission_gate.py sits beside this file; ensure `from permission_gate import`
# resolves whether launched as `-m tools.missing_lemma_loop.watcher` (the loop
# dir is NOT on sys.path then) or as a script. Without this, the adjudication
# thread dies with ModuleNotFoundError and claims never get adjudicated.
_LOOP_DIR = str(Path(__file__).resolve().parent)
if _LOOP_DIR not in sys.path:
    sys.path.insert(0, _LOOP_DIR)

REPL_ADDR = "127.0.0.1:6666"
REPL_PORT = 6666
# Bind 0.0.0.0 so the evaluator reaches it via the configured hostname
# (config/evaluation_servers.csv uses `cslcw2u`, which resolves to 127.0.1.1 —
# a 127.0.0.1-bound socket would refuse it).
REPL_START_CMD = ("./contrib/Isa-REPL/repl_server.sh 0.0.0.0:6666 "
                  "MathBench_Prover /tmp/repl_outputs -o threads=10 -o document=false")
# Address the watcher pre-launches the RPC host on and exports as RPC_Host.
# (Isabelle_RPC has had no default address since 0.4.0 -- with RPC_Host unset each
# Isabelle would spawn its own ephemeral host instead.)  The watcher OWNS this host:
# it pre-starts it with AOA_MISSING_LEMMA_SURVEY in its environment (用户方案
# 2026-06-11) so the lazy-spawn race ("whichever Isabelle process reconnects
# first donates its env") can never decide the survey switch.
RPC_HOST_ADDR = "127.0.0.1:27182"
# The semantic collect runs against its OWN REPL + RPC pair (用户决定
# 2026-06-12): the interpretation server lives inside the collect process
# (semantics_manage starts one in-process when --rpc-addr is free) and the
# dedicated REPL's ML callbacks go there via its RPC_Host env — fully
# decoupled from the AoA pair (6666/27182), whose host died entangled with a
# collect crash on 2026-06-12 11:55.
COLLECT_REPL_ADDR = "127.0.0.1:6665"
COLLECT_REPL_PORT = 6665
COLLECT_RPC_ADDR = "127.0.0.1:27183"
COLLECT_REPL_START_CMD = (f"./contrib/Isa-REPL/repl_server.sh {COLLECT_REPL_ADDR} "
                          "MathBench_Prover /tmp/repl_outputs_collect "
                          "-o threads=10 -o document=false")
SEMANTIC_COLLECT_CMD = ("./contrib/Semantic_Embedding/semantics_manage.py collect "
                        "MathBench_Prover.MathBench_Prover "
                        f"--repl-addr {COLLECT_REPL_ADDR} "
                        f"--rpc-addr {COLLECT_RPC_ADDR} "
                        "--embed-models qwen3-embedding-8b --model 'claude-opus-4-8[1m]'")
# Sledgehammer's external provers are launched by Isabelle's bash_process in
# their OWN setsid process groups; its killpg cleanup runs only on a normal
# JVM exit, so killing poly from outside strands them (two orphan veriT burned
# 99.7% CPU x16h, 2026-06-12). kill_repl_and_host sweeps them — but ONLY
# processes positively identified by comm whitelist AND a domain-precise env
# marker (shared machine: other sessions run the same binaries).
# Exact /proc/<pid>/comm values of the bundled binaries (cvc5 is a no-exec
# bash wrapper around cvc5-bin — the -bin is the load-bearing kill; eprover-ho
# is E's preferred exec name in future components; cvc4 ships with 2024).
_PROVER_NAMES = ("veriT", "vampire", "cvc5", "cvc5-bin", "cvc4", "z3",
                 "eprover", "eprover-ho", "SPASS", "zipperposition")
# Domain markers: these RPC_Host values are pinned ONLY in the per-child env
# dicts of the 6666 AoA REPL and the 6665 collect REPL — never exported into
# the watcher's own os.environ — so carrying one proves descent from a REPL
# this function just killed. AOA_MISSING_LEMMA_SURVEY is deliberately NOT a
# marker (it sits in the watcher's environ and is inherited tree-wide, e.g.
# by the phase-2 agent's 7777 REPL → would kill ITS working provers). 27180
# (build/7777 domain) is deliberately excluded for the same reason; the Base
# build itself spawns no provers (imports-only body, Auto_Sledgehammer lives
# in the child session).
_ORPHAN_ENV_MARKERS = (f"RPC_Host={RPC_HOST_ADDR}".encode(),
                       f"RPC_Host={COLLECT_RPC_ADDR}".encode())

# Dump MathBench_Prover (covers MathBench_ProverBase + the source-loaded
# MathBench_Prover.thy layer) AND Minilang_AoA — facts living in the
# source-loaded layers must not be misjudged as missing imports.
HEAP_LIST_CMD = "isabelle build -n -l MathBench_Prover Minilang_AoA"

# Cross-cutting runtime stats: missing_lemmas docs ever parsed (the survey
# canary reads this) and the watcher-owned RPC host pid (liveness checks).
SCAN_STATS = {"missing_lemmas_docs": 0}
_RPC_HOST_PID: int | None = None


def log(msg: str) -> None:
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


def bash(cmd: str, **kwargs):
    """Run *cmd* in a bash that sourced envir.sh, from the repo root."""
    return subprocess.run(["bash", "-c", f"source envir.sh && {cmd}"],
                          cwd=ROOT, **kwargs)


def bash_timed(cmd: str, timeout: float) -> int:
    """Run a LONG deterministic step with a real process-group kill on
    timeout. `subprocess.run(timeout=)` only SIGKILLs the direct child; bash
    exec-optimizes into e.g. the `isabelle` wrapper → java, whose poly
    children would survive as orphans (and a timed-out orphan build can later
    write an UNGATED heap). Returns the exit code; -1 on timeout."""
    proc = subprocess.Popen(["bash", "-c", f"source envir.sh && {cmd}"],
                            cwd=ROOT, start_new_session=True)
    try:
        return proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_proc(proc)
        return -1


def emit_event(level: str, kind: str, **data) -> None:
    """Append a structured event to events.jsonl — the interface the
    top-level supervisory agent watches (用户提议 2026-06-12). Levels:
    FATAL (needs the supervisor/user NOW), WARN (report, don't block),
    INFO (periodic digest material)."""
    evt = {"ts": datetime.now().isoformat(), "level": level, "kind": kind,
           **data}
    try:
        with open(STATE_DIR / "events.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(evt, ensure_ascii=False) + "\n")
    except OSError as e:
        log(f"WARNING: cannot write events.jsonl: {e}")


# ---------------------------------------------------------------------------
# State: ledger + offsets
# ---------------------------------------------------------------------------

def _load_json(path: Path, default):
    if path.exists():
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return default


def _save_json(path: Path, data) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    tmp.replace(path)


class Ledger:
    """Persistent record of every missing-lemma claim and its adjudication.

    Statuses:
      pending                  recorded, not yet adjudicated
      searching                a search agent is working on it
      missing_import           confirmed missing; phase 2 not yet done
      imported                 phase 2 added its theory to the heap
      already_in_heap          fact exists in the heap → retrieval failure
      not_found                searched both corpora, nothing matches
      provided_but_unfindable  was imported earlier, agent STILL cannot find it
      duplicate                same fact as another live entry (ref field)
      import_failed            phase 2 could not reconcile its theory
    """

    def __init__(self, path: Path):
        self.path = path
        self.entries: list[dict] = _load_json(path, [])

    def save(self) -> None:
        _save_json(self.path, self.entries)

    @staticmethod
    def claim_key(report: dict) -> str:
        name = (report.get("name_guess") or report.get("name") or "").strip().lower()
        if name:
            return f"name:{re.sub(r'[^a-z0-9]+', '_', name)}"
        eng = (report.get("english") or "").strip().lower()
        return "eng:" + re.sub(r"\s+", " ", eng)[:160]

    def add_claim(self, case: str, invocation: str, trigger: str, report: dict) -> dict:
        # Collection records EVERYTHING as pending — duplicate detection is an
        # AGENT's job, never a deterministic key match (用户决定 2026-06-11,
        # 复议确认 2026-06-12: a name guess is not an identity). The dedup
        # agent screens each batch (embedding candidates + slim digest) before
        # the search agent; either may return verdict "duplicate" with a
        # duplicate_of reference, and apply_verdicts() inherits the prior
        # adjudication (imported → provided_but_unfindable, etc.).
        entry = {
            "id": f"ml-{len(self.entries) + 1:04d}",
            "key": self.claim_key(report),
            "case": case,
            "invocation": invocation,
            "trigger": trigger,
            "first_seen": datetime.now().isoformat(),
            "report": report,
            "status": "pending",
            "resolution": {},
        }
        self.entries.append(entry)
        self.save()
        return entry

    @staticmethod
    def digest_entry(e: dict) -> dict:
        """The ONE projection of a ledger entry that may reach an agent
        prompt or the survey feedback file: never the raw resolution, which
        carries circuit-breaker notes / evidence meant for humans (评审 M5)."""
        r = e["report"]
        return {
            "id": e["id"],
            "name": r.get("name_guess") or r.get("name") or "",
            "english": (r.get("english") or "")[:200],
            "status": e["status"],
            "theory": e["resolution"].get("theory"),
            "lemma_name": e["resolution"].get("lemma_name"),
        }

    def adjudicated_digest(self, limit: int = 300,
                           only: tuple | None = None) -> list[dict]:
        """Compact view of previously adjudicated claims, handed to the
        dedup/search agents so they flag duplicates instead of re-searching.
        Deduplicated by claim key (latest adjudication wins) so the cap packs
        distinct facts, not repetitions. *only* restricts to those statuses —
        used for the slim always-included digest of imported/already_in_heap
        facts (正确性兜底, 评审 H2)."""
        by_key: dict[str, dict] = {}
        for e in self.entries:
            if e["status"] in ("pending", "searching", "duplicate"):
                continue
            if only is not None and e["status"] not in only:
                continue
            by_key[e["key"]] = self.digest_entry(e)
        return list(by_key.values())[-limit:]

    def pending(self) -> list[dict]:
        return [e for e in self.entries if e["status"] == "pending"]

    def by_id(self, eid: str) -> dict:
        return next(e for e in self.entries if e["id"] == eid)


SURVEY_FEEDBACK_PATH = STATE_DIR / "survey_feedback.json"
_FEEDBACK_STATUSES = ("already_in_heap", "not_found", "import_failed",
                      "provided_but_unfindable")


def write_survey_feedback(ledger: 'Ledger', attempt_ids: set) -> None:
    """Verdict feedback for the AoA survey prompt (第一重防重报). Attempt-
    scoped (用户裁决 2026-06-12): only claims ingested during the CURRENT
    attempt that already carry a final adjudication — cross-attempt repeats
    are deliberately let through to the dedup stage, because a re-report of
    an imported fact IS the provided_but_unfindable signal. digest_entry
    projection only (never raw resolution). Atomic write (tmp in the same
    dir + replace): the RPC-host process reads this file mid-survey."""
    entries = [Ledger.digest_entry(e) for e in ledger.entries
               if e["id"] in attempt_ids and e["status"] in _FEEDBACK_STATUSES]
    tmp = SURVEY_FEEDBACK_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(entries, indent=2, ensure_ascii=False),
                   encoding="utf-8")
    tmp.replace(SURVEY_FEEDBACK_PATH)


# ---------------------------------------------------------------------------
# Log scanning
# ---------------------------------------------------------------------------

_DOC_SEP = b"\n---\n"


def _ingest_doc(doc, ledger: Ledger, case: str, invocation: str,
                new_entries: list[dict]) -> None:
    if not isinstance(doc, dict) or doc.get("event") != "MISSING_LEMMAS":
        return
    SCAN_STATS["missing_lemmas_docs"] += 1  # counts empty surveys too (canary)
    for lemma in doc.get("lemmas") or []:
        if not isinstance(lemma, dict):
            continue
        entry = ledger.add_claim(
            case=case, invocation=invocation,
            trigger=doc.get("trigger", "?"), report=lemma)
        new_entries.append(entry)
        log(f"claim {entry['id']} [{entry['status']}] "
            f"({entry['trigger']}) {entry['key']}")


def scan_logs(log_dir: Path, offsets: dict, ledger: Ledger, case: str) -> list[dict]:
    """Ingest new MISSING_LEMMAS docs from every missing_lemmas.yaml under
    *log_dir*. Returns the newly added ledger entries. NO filtering — every
    reported lemma becomes a ledger entry.

    Document-boundary-safe incremental parsing: documents are separated by
    ``\\n---\\n`` (the writer flushes one whole doc at a time). We consume
    documents that are TERMINATED by a following separator unconditionally;
    the trailing (possibly still-being-written) document is consumed only once
    the file has stopped growing across two polls AND it parses. Never advance
    the offset into the middle of a document — a truncated chunk that happens
    to parse would poison every later poll of the file. Offsets are stored as
    ``{"offset": int, "size": int}`` per file (legacy int upgraded)."""
    # invocation_id -> case-name map the evaluator writes at case start (B1).
    # Lets the fleet attribute each claim to its real PutnamBench case instead
    # of the single placeholder *case* passed in (which is "?" when 18 cases
    # survey concurrently into one log dir). Re-read each scan so freshly
    # started cases appear; a missing entry falls back to *case*.
    case_info: dict[str, str] = {}
    ci_path = log_dir / "case_info.jsonl"
    if ci_path.exists():
        try:
            for ln in ci_path.read_text(encoding="utf-8").splitlines():
                ln = ln.strip()
                if not ln:
                    continue
                rec = json.loads(ln)
                inv = rec.get("invocation_id")
                if inv:
                    case_info[inv] = rec.get("case_name", case)
        except (OSError, json.JSONDecodeError) as e:
            log(f"WARNING: failed to read case_info.jsonl: {e}")

    new_entries: list[dict] = []
    for f in sorted(log_dir.glob("*/missing_lemmas.yaml")):
        invocation_id = f.parent.name
        if ".old_" in invocation_id:
            continue  # renamed stale invocation dirs — never re-ingest
        actual_case = case_info.get(invocation_id, case)
        key = str(f)
        st = offsets.get(key, 0)
        if isinstance(st, int):  # legacy format upgrade
            st = {"offset": st, "size": -1}
        off, last_size = st["offset"], st["size"]
        size = f.stat().st_size
        if size < off:  # truncated/replaced file — reset defensively
            log(f"WARNING: {f} shrank ({size} < {off}); resetting offset")
            off = 0
        with open(f, "rb") as fh:
            fh.seek(off)
            chunk = fh.read()
        # Split on doc separators. parts[:-1] are separator-terminated →
        # complete; parts[-1] is the trailing doc, complete only if the file
        # is quiescent (same size as the previous poll).
        parts = chunk.split(_DOC_SEP)
        consume_upto = len(chunk) - len(parts[-1])  # bytes incl. last sep
        complete = parts[:-1]
        if parts[-1].strip() and size == last_size:
            complete.append(parts[-1])
            consume_upto = len(chunk)
        for raw in complete:
            if not raw.strip():
                continue
            try:
                text = raw.decode("utf-8")
                doc = yaml.safe_load(text.removeprefix("---\n"))
            except (UnicodeDecodeError, yaml.YAMLError) as e:
                if raw is complete[-1] and consume_upto == len(chunk):
                    # trailing doc judged complete but unparsable — leave it
                    # for the next poll instead of consuming garbage
                    consume_upto = len(chunk) - len(parts[-1])
                    break
                log(f"WARNING: skipping unparsable doc in {f}: {e}")
                continue
            _ingest_doc(doc, ledger, actual_case, invocation_id, new_entries)
        offsets[key] = {"offset": off + consume_upto, "size": size}
    return new_entries


# ---------------------------------------------------------------------------
# Headless claude agents (Claude Agent SDK — same dependency the repo already
# uses in driver_claude_code.py and semantic_interpretation.py)
# ---------------------------------------------------------------------------

# One worker thread is enough: the watcher runs at most one search agent at a
# time (claims are batched), concurrently with the evaluator subprocess.
_AGENT_POOL = concurrent.futures.ThreadPoolExecutor(max_workers=1)

# CLI selection: None = the SDK's bundled CLI. claude-agent-sdk 0.1.72 bundled
# 2.1.126, which predated auto-mode support for opus 4.8 ("auto mode
# unavailable for this model") — that cost a day of misdiagnosis; after
# upgrading to claude-agent-sdk 0.2.97 the bundled CLI is 2.1.173 and fine
# (verified 2026-06-11). If auto mode ever errors again, check the bundled CLI
# version first, and point this at shutil.which("claude") as a quick fix.
_CLI_PATH: str | None = None


async def _claude_agent_async(prompt: str, *, model: str | None,
                              transcript_path: Path,
                              timeout: float | None = None,
                              mission: str,
                              answer_tool=None,
                              done=None) -> None:
    from claude_agent_sdk import (ClaudeAgentOptions, ClaudeSDKClient,
                                  HookMatcher, ResultMessage,
                                  create_sdk_mcp_server)
    from permission_gate import static_pretooluse_hook

    perm_log = transcript_path.with_suffix(".perm.log")
    # Permissions are answered EXCLUSIVELY by Claude Code's built-in auto-mode
    # classifier (用户拍板: never any self-made judging; if auto is
    # unavailable, CRASH — set_permission_mode below raises in that case).
    # The static red-line PreToolUse hook runs earlier, so red-line calls
    # never reach the classifier; mission text goes into the prompt (both the
    # agent and the classifier read it as boundaries).
    prompt = f"Your mission and boundaries:\n{mission}\n\n{prompt}"
    mcp_servers = {}
    if answer_tool is not None:
        mcp_servers["results"] = create_sdk_mcp_server(
            "results", tools=[answer_tool])

    options = ClaudeAgentOptions(
        cwd=str(ROOT),
        # Load project settings so CLAUDE.md and .claude/skills (notably
        # mathbench-import-reconcile for the phase-2 agent) are available.
        setting_sources=["project"],
        model=model,
        cli_path=_CLI_PATH,
        permission_mode="auto",
        hooks={"PreToolUse": [HookMatcher(
            matcher="*", hooks=[static_pretooluse_hook(perm_log)])]},
        mcp_servers=mcp_servers,
        # Raise the Bash foreground timeout from the 2-min default to 5 min
        # so slow cluster commands (git status on the 136M repo, isabelle
        # build, divergence/gate runs) are not auto-backgrounded/SIGTERMed.
        # That backgrounding wedged the phase-2 reconcile agent: it could not
        # retrieve the backgrounded output and falsely concluded the shell was
        # dead, then reverted a valid promotion. Merged onto inherited env by
        # the SDK ({**inherited_env, **options.env}), so PATH/conda/keys stay.
        env={"BASH_DEFAULT_TIMEOUT_MS": "300000"},
    )

    # ClaudeSDKClient (not one-shot query()): permission/control answers
    # travel on the bidirectional control channel, which query() closes after
    # the prompt iterator is exhausted ("Stream closed").
    #
    # The session must NOT end at the first ResultMessage when a *done*
    # predicate is given: an agent that backgrounds a long step (the phase-2
    # heap rebuild, observed live 2026-06-11 23:32) ends its turn to await
    # the task notification — closing the client there kills its background
    # work and loses the answer-tool call. So with done!=None we keep
    # receiving across turns (the CLI auto-reinvokes the agent on task
    # completion); only when the stream goes idle BETWEEN turns do we nudge
    # the agent (bounded), and we stop once done() holds.
    # The CLI survives long idles fine (probed: 300s, full option combo) —
    # the earlier "idle exit" was a misdiagnosed artifact of cancelling the
    # message generator. The window need only catch "agent forgot to call
    # the answer tool"; in-session steps are all short foreground calls now
    # (the heap rebuild lives outside the session), so 120s is generous.
    _NUDGE_IDLE_SECONDS = 120
    _MAX_NUDGES = 8
    _NUDGE_TEXT = (
        "You ended your turn without completing the required answer-tool "
        "call. That call is the only deliverable of this session. If your "
        "work is done, call the answer tool NOW with the real outcome. If "
        "some work is genuinely unfinished, bring the FILES back to a "
        "consistent state first: a theory whose validation or promotion you "
        "could not finish must be reported as failed AND have your edits for "
        "it reverted. If you started a long background command, report it in "
        "the `failed` reason so the watcher knows — do not wait for it.")

    async def _drive() -> None:
        with open(transcript_path, "a", encoding="utf-8") as t:
            def _log_message(message) -> bool:
                """Write *message* to the transcript; True iff turn ended."""
                for block in getattr(message, "content", None) or []:
                    text = getattr(block, "text", None)
                    if isinstance(text, str):
                        t.write(text + "\n")
                    tool = getattr(block, "name", None)
                    if tool is not None and hasattr(block, "input"):
                        t.write(f"[tool_use] {tool} "
                                f"{json.dumps(block.input, ensure_ascii=False)[:400]}\n")
                    if getattr(block, "is_error", False):
                        t.write(f"[tool_error] {str(getattr(block, 'content', ''))[:400]}\n")
                if isinstance(message, ResultMessage):
                    t.write(f"\n=== result: is_error={message.is_error} "
                            f"cost=${message.total_cost_usd or 0:.4f} ===\n")
                    if message.is_error:
                        raise RuntimeError(
                            f"claude agent failed: {message.result!r:.500}")
                    t.flush()
                    return True
                t.flush()
                return False

            async with ClaudeSDKClient(options=options) as client:
                # Options-level "auto" silently degrades to default mode when
                # unavailable (leaving headless permission requests
                # unanswered) — set it explicitly so unavailability RAISES.
                await client.set_permission_mode("auto")
                await client.query(prompt)
                if done is None:
                    async for message in client.receive_response():
                        _log_message(message)
                    return
                # Messages are pumped into a queue by a persistent task:
                # waiting with a timeout directly on the generator's
                # __anext__ would CANCEL it on timeout, which kills the
                # async generator and tears down the transport reader
                # (observed live: StopAsyncIteration + CLI "Stream closed"
                # right after the first nudge). Cancelling queue.get() is
                # harmless.
                _SENTINEL = object()
                queue: asyncio.Queue = asyncio.Queue()
                pump_error: list[BaseException] = []

                async def _pump() -> None:
                    try:
                        async for m in client.receive_messages():
                            await queue.put(m)
                    except asyncio.CancelledError:
                        raise
                    except BaseException as e:  # preserve the REAL root cause
                        pump_error.append(e)
                    finally:
                        await queue.put(_SENTINEL)

                pump_task = asyncio.create_task(_pump())
                try:
                    turn_open = True
                    nudges = 0
                    while True:
                        try:
                            message = await asyncio.wait_for(
                                queue.get(),
                                timeout=(None if turn_open
                                         else _NUDGE_IDLE_SECONDS))
                        except asyncio.TimeoutError:
                            # idle between turns, deliverable still missing
                            if done():
                                return
                            nudges += 1
                            if nudges > _MAX_NUDGES:
                                raise RuntimeError(
                                    f"agent never called the answer tool "
                                    f"after {_MAX_NUDGES} nudges")
                            t.write(f"\n=== nudge {nudges}/{_MAX_NUDGES} ===\n")
                            t.flush()
                            await client.query(_NUDGE_TEXT)
                            turn_open = True
                            continue
                        if message is _SENTINEL:
                            if pump_error:
                                raise RuntimeError(
                                    "agent message stream died"
                                ) from pump_error[0]
                            if not done():
                                raise RuntimeError(
                                    "agent stream ended before the answer "
                                    "tool was called")
                            return
                        # Messages flowing = a turn is open (covers the CLI's
                        # automatic re-invocation after a background task —
                        # without this, a >idle-window foreground step in such
                        # a turn would be mid-turn nudged).
                        turn_open = True
                        if _log_message(message):   # a turn just ended
                            if done():
                                return
                            turn_open = False   # await auto-continuation/nudge
                finally:
                    pump_task.cancel()
                    try:
                        await pump_task
                    except (asyncio.CancelledError, Exception):
                        pass

    if timeout is not None:
        await asyncio.wait_for(_drive(), timeout=timeout)
    else:
        await _drive()


def run_claude_agent(prompt: str, *, model: str | None,
                     transcript_path: Path,
                     timeout: float | None = None,
                     mission: str = "",
                     answer_tool=None,
                     done=None) -> None:
    """Blocking wrapper (the watcher itself is synchronous)."""
    asyncio.run(_claude_agent_async(prompt, model=model,
                                    transcript_path=transcript_path,
                                    timeout=timeout, mission=mission,
                                    answer_tool=answer_tool, done=done))


# ---------------------------------------------------------------------------
# Embedding candidate retrieval (qwen3, reuses the Semantic_Embedding provider)
#
# 确定性归脚本：embeddings only RETRIEVE likely-duplicate candidates for the
# dedup agent; every judgment stays with an agent (deterministic key-based
# auto-dedup was rejected 2026-06-12 — a name guess is not an identity).
# Correctness never depends on the similarity threshold: the slim digest of
# imported/already_in_heap facts is always in the prompts (评审 H2).
# ---------------------------------------------------------------------------

_EMBED_TOP_K = 20      # 用户定 2026-06-12
_EMBED_MIN_SIM = 0.5   # quality knob only — tune from production, not offline
_embed_provider = None  # set by init_embedding(); None = candidates disabled


def _claim_embed_text(report: dict) -> str:
    """Deterministic embed text, v1. The provider's disk cache keys on the
    EXACT string — any instability here re-embeds the whole ledger every
    batch, and an overlong text makes the API 400 (which the provider's
    retry loop treats as retryable, burning the whole time budget). So:
    fixed field order, fixed separators, one normalizer, per-field caps.
    Changing the field set or caps is a deliberate cache-flush event."""
    parts = []
    for label, keys, cap in (("name", ("name_guess", "name"), 120),
                             ("statement", ("english",), 1500),
                             ("isabelle", ("isabelle_statement",), 1500),
                             ("why needed", ("why_needed",), 800),
                             ("detail", ("detail",), 800)):
        val = next((report.get(k) for k in keys if report.get(k)), "")
        parts.append(f"{label}: {str(val or '')[:cap]}")
    return "\n".join(parts)


def init_embedding(ledger: 'Ledger') -> None:
    """One-time probe + import + prewarm at watcher startup. The package
    import is heavy (its __init__ drags rocksdict/claude_agent_sdk/faiss) —
    pay it once here, never on the search hot path. The provider reads
    QWEN3_EMBEDDING_API_KEY at class-definition time and a missing key does
    NOT raise — it sends unauthenticated requests that 401 into ~17min of
    doomed backoff — so probe BOTH the env var and provider.api_key up front.
    The key lives in secret.sh (envir.sh does not source it): the watcher
    must be launched from a shell that sourced secret.sh."""
    global _embed_provider
    if not os.getenv("QWEN3_EMBEDDING_API_KEY"):
        log("WARNING: QWEN3_EMBEDDING_API_KEY not set (source secret.sh "
            "before launching the watcher) — duplicate-candidate retrieval "
            "disabled; agents fall back to the full digest")
        return
    try:
        from Isabelle_Semantic_Embedding.semantic_embedding import (
            embedding_provider)
        provider = embedding_provider("qwen3-embedding-8b")
    except Exception as e:
        log(f"WARNING: embedding provider unavailable "
            f"({type(e).__name__}: {e}) — candidate retrieval disabled")
        return
    if provider.api_key is None:
        log("WARNING: embedding provider has no API key (set after import?) "
            "— candidate retrieval disabled")
        return
    _embed_provider = provider
    # Prewarm: the text→vector disk cache has a 3-day TTL; after a quiet
    # spell a batch would face the whole ledger cold and blow the 60s budget.
    texts = [_claim_embed_text(e["report"]) for e in ledger.entries
             if e["status"] not in ("pending", "searching", "duplicate")]
    if texts:
        try:
            asyncio.run(asyncio.wait_for(provider.embed(texts), 120))
            log(f"embedding cache prewarmed ({len(texts)} adjudicated entries)")
        except Exception as e:
            log(f"WARNING: embedding prewarm failed ({type(e).__name__}: {e})"
                f" — keeping candidates enabled; batches fail open per-call")


def embedding_candidates(claims: list[dict], ledger: 'Ledger') \
        -> tuple[dict[str, list[dict]], dict[str, list[str]]] | None:
    """Per-claim likely-duplicate candidates (top _EMBED_TOP_K adjudicated
    entries with cosine ≥ _EMBED_MIN_SIM) plus mutual same-batch twin marks.
    Returns None when disabled or on ANY failure — callers fall back to the
    full digest. Vectors are L2-normalized by the provider (cosine = dot;
    do not normalize again)."""
    if _embed_provider is None:
        return None
    adjud = [e for e in ledger.entries
             if e["status"] not in ("pending", "searching", "duplicate")]
    texts = ([_claim_embed_text(c["report"]) for c in claims]
             + [_claim_embed_text(e["report"]) for e in adjud])
    try:
        result = asyncio.run(asyncio.wait_for(_embed_provider.embed(texts), 60))
    except Exception as e:
        log(f"WARNING: embedding retrieval failed ({type(e).__name__}: {e}) "
            f"— falling back to the full digest")
        return None
    import numpy as np
    vecs = result.vectors
    cvecs, evecs = vecs[:len(claims)], vecs[len(claims):]
    cands: dict[str, list[dict]] = {c["id"]: [] for c in claims}
    if adjud:
        sims = cvecs @ evecs.T
        for i, c in enumerate(claims):
            order = np.argsort(-sims[i])[:_EMBED_TOP_K]
            cands[c["id"]] = [
                dict(Ledger.digest_entry(adjud[j]),
                     similarity=round(float(sims[i][j]), 3))
                for j in order if sims[i][j] >= _EMBED_MIN_SIM]
    twins: dict[str, list[str]] = {c["id"]: [] for c in claims}
    if len(claims) > 1:
        csims = cvecs @ cvecs.T
        for i, c in enumerate(claims):
            twins[c["id"]] = [claims[j]["id"] for j in range(len(claims))
                              if j != i and csims[i][j] >= _EMBED_MIN_SIM]
    return cands, twins


_VERDICT_VALUES = ("missing_import", "already_in_heap", "not_found", "duplicate")


def _make_verdict_tool(claim_ids: list[str], known_ids: set[str]):
    """In-process MCP tool the search agent MUST call to submit its verdicts
    (structured output as a forced tool call, not parsed from chat/file).
    Each item is validated; invalid items are rejected with an immediate error
    message so the agent corrects and resubmits. *known_ids* (batch ∪ ledger)
    validates duplicate_of at submission time — a dangling reference would
    otherwise silently re-pend the claim into a wasted re-search (评审 H1).
    Returns (tool, holder) — accepted verdicts accumulate in *holder* keyed
    by claim_id."""
    from claude_agent_sdk import tool
    holder: dict[str, dict] = {}
    expected = set(claim_ids)

    @tool("submit_verdicts",
          "Submit your verdicts for one or more claims. May be called several "
          "times; a later submission overwrites the earlier one for the same "
          "claim_id. Finish only after every claim has an accepted verdict.",
          {"type": "object",
           "properties": {
               "verdicts": {
                   "type": "array",
                   "items": {
                       "type": "object",
                       "properties": {
                           "claim_id": {"type": "string"},
                           "verdict": {"type": "string",
                                       "enum": list(_VERDICT_VALUES)},
                           "duplicate_of": {"type": "string"},
                           "lemma_name": {"type": "string"},
                           "theory": {"type": "string"},
                           "evidence": {"type": "string"},
                           "notes": {"type": "string"},
                       },
                       "required": ["claim_id", "verdict"]}}},
           "required": ["verdicts"]})
    async def submit_verdicts(args: dict):
        items = args.get("verdicts")
        if not isinstance(items, list):
            return {"content": [{"type": "text",
                                 "text": "`verdicts` must be an array."}],
                    "is_error": True}
        errors = []
        for i, v in enumerate(items):
            if not isinstance(v, dict):
                errors.append(f"item {i}: not an object")
                continue
            cid, verdict = v.get("claim_id"), v.get("verdict")
            if cid not in expected:
                errors.append(f"item {i}: unknown claim_id {cid!r}")
            elif verdict not in _VERDICT_VALUES:
                errors.append(f"{cid}: invalid verdict {verdict!r}")
            elif verdict == "missing_import" and not v.get("theory"):
                errors.append(f"{cid}: missing_import requires `theory`")
            elif verdict == "already_in_heap" and not v.get("lemma_name"):
                errors.append(f"{cid}: already_in_heap requires `lemma_name`")
            elif verdict == "duplicate" and not v.get("duplicate_of"):
                errors.append(f"{cid}: duplicate requires `duplicate_of`")
            elif verdict == "duplicate" and v["duplicate_of"] == cid:
                errors.append(f"{cid}: duplicate_of must not be the claim itself")
            elif verdict == "duplicate" and v["duplicate_of"] not in known_ids:
                errors.append(f"{cid}: duplicate_of {v['duplicate_of']!r} is "
                              f"not a known ledger/batch id")
            else:
                holder[cid] = v
        remaining = sorted(expected - holder.keys())
        msg = f"Recorded {len(holder)}/{len(expected)} verdicts."
        if errors:
            msg += " REJECTED: " + "; ".join(errors) + "."
        if remaining:
            msg += f" Still unanswered: {', '.join(remaining)}."
        else:
            msg += " All claims answered — you may stop."
        return {"content": [{"type": "text", "text": msg}],
                "is_error": bool(errors)}

    return submit_verdicts, holder


def _make_dedup_tool(claim_ids: list[str], known_ids: set[str]):
    """In-process MCP tool of the duplicate-screening agent (用户提案
    2026-06-12: judgment split off so the search agent can focus on
    exploration; ALL agents deliver via an answer tool — hard rule).
    Same validate-and-resubmit contract as _make_verdict_tool."""
    from claude_agent_sdk import tool
    holder: dict[str, dict] = {}
    expected = set(claim_ids)

    @tool("submit_dedup",
          "Submit your duplicate-screening judgments for one or more claims. "
          "May be called several times; a later submission overwrites the "
          "earlier one for the same claim_id. Finish only after every claim "
          "has an accepted judgment.",
          {"type": "object",
           "properties": {
               "judgments": {
                   "type": "array",
                   "items": {
                       "type": "object",
                       "properties": {
                           "claim_id": {"type": "string"},
                           "verdict": {"type": "string",
                                       "enum": ["new", "duplicate"]},
                           "duplicate_of": {"type": "string"},
                           "notes": {"type": "string"},
                       },
                       "required": ["claim_id", "verdict"]}}},
           "required": ["judgments"]})
    async def submit_dedup(args: dict):
        items = args.get("judgments")
        if not isinstance(items, list):
            return {"content": [{"type": "text",
                                 "text": "`judgments` must be an array."}],
                    "is_error": True}
        errors = []
        for i, v in enumerate(items):
            if not isinstance(v, dict):
                errors.append(f"item {i}: not an object")
                continue
            cid, verdict = v.get("claim_id"), v.get("verdict")
            if cid not in expected:
                errors.append(f"item {i}: unknown claim_id {cid!r}")
            elif verdict not in ("new", "duplicate"):
                errors.append(f"{cid}: invalid verdict {verdict!r}")
            elif verdict == "duplicate" and not v.get("duplicate_of"):
                errors.append(f"{cid}: duplicate requires `duplicate_of`")
            elif verdict == "duplicate" and v["duplicate_of"] == cid:
                errors.append(f"{cid}: duplicate_of must not be the claim itself")
            elif verdict == "duplicate" and v["duplicate_of"] not in known_ids:
                errors.append(f"{cid}: duplicate_of {v['duplicate_of']!r} is "
                              f"not a known ledger/batch id")
            else:
                holder[cid] = v
        remaining = sorted(expected - holder.keys())
        msg = f"Recorded {len(holder)}/{len(expected)} judgments."
        if errors:
            msg += " REJECTED: " + "; ".join(errors) + "."
        if remaining:
            msg += f" Still unanswered: {', '.join(remaining)}."
        else:
            msg += " All claims answered — you may stop."
        return {"content": [{"type": "text", "text": msg}],
                "is_error": bool(errors)}

    return submit_dedup, holder


def _make_result_tool():
    """In-process MCP tool the phase-2 agent MUST call to submit its result.
    Returns (tool, holder)."""
    from claude_agent_sdk import tool
    holder: dict = {}

    @tool("submit_result",
          "Submit the final phase-2 result. Call exactly once, when done.",
          {"type": "object",
           "properties": {
               "imported": {"type": "array", "items": {
                   "type": "object",
                   "properties": {"theory": {"type": "string"},
                                  "reconciliations": {"type": "array",
                                                      "items": {"type": "string"}}},
                   "required": ["theory"]}},
               "failed": {"type": "array", "items": {
                   "type": "object",
                   "properties": {"theory": {"type": "string"},
                                  "reason": {"type": "string"}},
                   "required": ["theory"]}},
               "divergence_decisions": {"type": "object",
                                        "properties": {"fixed": {"type": "integer"},
                                                       "accepted": {"type": "integer"}}},
               "files_promoted": {"type": "boolean"},
           },
           "required": ["imported", "failed", "files_promoted"]})
    async def submit_result(args: dict):
        errors = []
        imported = args.get("imported")
        if not isinstance(imported, list) or any(
                not (isinstance(i, dict) and i.get("theory")) for i in imported):
            errors.append("`imported` must be an array of objects with `theory`")
        if not isinstance(args.get("failed"), list):
            errors.append("`failed` must be an array")
        if not isinstance(args.get("files_promoted"), bool):
            errors.append("`files_promoted` must be a boolean — report what "
                          "you actually edited")
        if errors:
            return {"content": [{"type": "text", "text": "; ".join(errors)}],
                    "is_error": True}
        holder.clear()
        holder.update(args)
        return {"content": [{"type": "text",
                             "text": "Result recorded. You may stop."}]}

    return submit_result, holder


def _json_block(title: str, data) -> str:
    return (f"\n## {title}\n\n```json\n"
            + json.dumps(data, indent=2, ensure_ascii=False) + "\n```\n")


def _run_adjudication(cfg, *, dedup_prompt: str, dedup_tool, dedup_holder: dict,
                      ids: list[str], known_ids: set[str],
                      payload: list[dict], search_head: str,
                      search_tail: str, out: Path) -> dict[str, dict]:
    """Worker-thread body of the two-stage adjudication pipeline (用户提案
    2026-06-12): the duplicate-screening agent first, then the search agent
    on the 'new' subset only. An all-duplicates batch skips the search agent
    entirely; a failed/partial screening fails OPEN (the whole batch goes to
    the search agent, whose safety-valve duplicate verdict + slim digest
    still protect the provided_but_unfindable link). Returns the search
    agent's verdict holder."""
    from permission_gate import DEDUP_MISSION, SEARCH_MISSION
    new_ids = list(ids)
    try:
        run_claude_agent(dedup_prompt, model=cfg.search_model,
                         transcript_path=out.with_suffix(".dedup.log"),
                         timeout=cfg.search_timeout, mission=DEDUP_MISSION,
                         answer_tool=dedup_tool,
                         done=lambda: set(ids) <= dedup_holder.keys())
        # Unanswered claims count as "new" — never silently dropped.
        new_ids = [cid for cid in ids
                   if dedup_holder.get(cid, {}).get("verdict") != "duplicate"]
        log(f"dedup agent: {len(ids) - len(new_ids)}/{len(ids)} judged "
            f"duplicate")
    except Exception as e:
        log(f"WARNING: dedup agent failed ({type(e).__name__}: {e}) — "
            f"fail-open: whole batch goes to the search agent")
        dedup_holder.clear()
        new_ids = list(ids)
    if not new_ids:
        log("dedup agent: whole batch is duplicates — search agent skipped")
        return {}
    new_set = set(new_ids)
    prompt = (search_head
              + _json_block("Claims", [p for p in payload
                                       if p["claim_id"] in new_set])
              + search_tail)
    search_tool, search_holder = _make_verdict_tool(new_ids, known_ids)
    run_claude_agent(prompt, model=cfg.search_model,
                     transcript_path=out.with_suffix(".log"),
                     timeout=cfg.search_timeout, mission=SEARCH_MISSION,
                     answer_tool=search_tool,
                     done=lambda: new_set <= search_holder.keys())
    return search_holder


def start_search(cfg, ledger: 'Ledger', claims: list[dict]) \
        -> tuple[concurrent.futures.Future, Path, list[str], dict]:
    """Launch the adjudication pipeline for *claims* (non-blocking: runs in a
    worker thread so the evaluator keeps being polled meanwhile). Prompt
    composition: the slim digest of imported/already_in_heap facts goes into
    BOTH stages unconditionally (correctness floor, 评审 H2); per-claim
    embedding candidates go to the dedup agent when available, else both
    prompts fall back to the full digest."""
    # M2: bound the batch so a backlog (e.g. an 18-prover survey burst) can't
    # build one giant dedup/search prompt that times out. The remainder stays
    # pending and is picked up by the next search round (the single in-flight
    # search gate paginates it).
    cap = getattr(cfg, "max_claims_per_batch", 0) or 0
    if cap and len(claims) > cap:
        log(f"adjudication batch capped at {cap}/{len(claims)} claims; "
            f"remainder stays pending for the next round")
        claims = claims[:cap]
    for c in claims:
        c["status"] = "searching"
    out = STATE_DIR / "verdicts" / f"verdict_{claims[0]['id']}_{int(time.time())}.json"
    ids = [c["id"] for c in claims]
    known_ids = set(ids) | {e["id"] for e in ledger.entries}
    payload = [{"claim_id": c["id"], **c["report"]} for c in claims]

    slim = ledger.adjudicated_digest(only=("imported", "already_in_heap"))
    slim_block = _json_block("Imported / in-heap facts", slim) if slim else ""
    emb = embedding_candidates(claims, ledger)
    if emb is not None:
        cands, twins = emb
        dedup_payload = [dict(p,
                              likely_duplicates=cands.get(p["claim_id"], []),
                              possible_batch_twins=twins.get(p["claim_id"], []))
                         for p in payload]
        full_digest_block = ""
    else:
        dedup_payload = payload
        digest = ledger.adjudicated_digest()
        full_digest_block = (_json_block(
            "Previously adjudicated claims (duplicate check)", digest)
            if digest else "")

    dedup_prompt = ((PROMPT_DIR / "dedup_prompt.md").read_text(encoding="utf-8")
                    + _json_block("Claims", dedup_payload)
                    + slim_block + full_digest_block)
    search_head = ((PROMPT_DIR / "search_prompt.md").read_text(encoding="utf-8")
                   .replace("HEAP_THEORIES_FILE",
                            str(STATE_DIR / "heap_theories.txt")))
    search_tail = slim_block + full_digest_block

    log(f"adjudication pipeline → {len(claims)} claim(s), "
        f"candidates={'on' if emb is not None else 'off'}, "
        f"verdicts at {out.name}")
    dedup_tool, dedup_holder = _make_dedup_tool(ids, known_ids)
    fut = _AGENT_POOL.submit(
        _run_adjudication, cfg, dedup_prompt=dedup_prompt,
        dedup_tool=dedup_tool, dedup_holder=dedup_holder, ids=ids,
        known_ids=known_ids, payload=payload, search_head=search_head,
        search_tail=search_tail, out=out)
    return fut, out, ids, dedup_holder


def finish_search(ledger: Ledger,
                  search: tuple[concurrent.futures.Future, Path, list[str], dict],
                  wait_timeout: float | None = None) -> list[str]:
    """Collect a finished (or awaited) adjudication pipeline; returns
    confirmed theories. Search verdicts and the dedup agent's duplicate
    judgments merge into ONE verdict file (audit trail), adjudicated by the
    same two-pass apply_verdicts."""
    fut, out, ids, dedup_holder = search
    search_holder: dict[str, dict] = {}
    try:
        search_holder = fut.result(timeout=wait_timeout) or {}
    except Exception as e:
        log(f"WARNING: adjudication pipeline failed: {type(e).__name__}: {e}")
    dedup_dups = [dict(v, verdict="duplicate")
                  for cid, v in dedup_holder.items()
                  if v.get("verdict") == "duplicate"
                  and cid not in search_holder]
    verdicts = list(search_holder.values()) + dedup_dups
    out.write_text(json.dumps({"verdicts": verdicts,
                               "dedup": list(dedup_holder.values())},
                              indent=2, ensure_ascii=False), encoding="utf-8")
    return apply_verdicts(ledger, out, ids)


def _resolve_dup_target(ledger: Ledger, verdicts: dict[str, dict],
                        start_id: str) -> dict | None:
    """Follow a duplicate_of chain to the entry carrying a REAL adjudication.
    Chains arise when a same-batch twin points at a representative that is
    itself a duplicate of an older entry. Chase through both this batch's
    not-yet-applied duplicate verdicts and old `duplicate` ledger entries.
    Returns None on a dangling id, an unanswered (`searching`) member, a
    cycle, or depth overflow — the caller re-pends the claim."""
    cur, seen = start_id, set()
    while cur not in seen and len(seen) < 10:
        seen.add(cur)
        try:
            ref = ledger.by_id(cur)
        except StopIteration:
            return None  # dangling id (tool-validated, but be safe)
        v = verdicts.get(cur)
        if v and v.get("verdict") == "duplicate" and v.get("duplicate_of"):
            cur = v["duplicate_of"]
            continue
        if ref["status"] == "duplicate" and ref["resolution"].get("ref"):
            cur = ref["resolution"]["ref"]
            continue
        if ref["status"] in ("searching", "pending"):
            # An unanswered batch member (pass 1 already re-pended it) or a
            # pre-existing pending entry: inheriting now would freeze the twin
            # as a bare "duplicate" that never sees the ref's eventual verdict
            # — re-pend instead so both go through the next round together.
            return None
        return ref
    return None  # cycle or depth overflow


def _emit_unfindable_warn(ledger: Ledger, e: dict, ref: dict,
                          warned_refs: set) -> None:
    """One WARN per imported ref (评审 M3): the supervisory stream gets one
    event per underlying fact, not one per re-report. Coalesced against both
    this pass (warned_refs) and the ledger (an earlier entry already carrying
    provided_but_unfindable for the same ref) — never against events.jsonl."""
    rid = ref["id"]
    if rid in warned_refs or any(
            x is not e and x["status"] == "provided_but_unfindable"
            and x["resolution"].get("ref") == rid for x in ledger.entries):
        return
    warned_refs.add(rid)
    r = e["report"]
    emit_event("WARN", "provided_but_unfindable", id=e["id"], ref=rid,
               name=r.get("name_guess") or r.get("name") or "",
               lemma_name=ref["resolution"].get("lemma_name"),
               theory=ref["resolution"].get("theory"))


def _inherit_duplicate(ledger: Ledger, e: dict, ref: dict,
                       warned_refs: set) -> None:
    """Inherit *ref*'s adjudication into the duplicate claim *e*. A duplicate
    of an IMPORTED entry means "provided yet still unfindable": a retrieval/
    visibility problem to surface, not an import gap. Note duplicate-of-
    missing_import stays a plain terminal "duplicate" even after the ref is
    later imported — accepted (评审 M2): the in-flight window is tiny (a
    confirmed missing_import kills the case immediately) and the NEXT
    re-report after the import lands provided_but_unfindable normally."""
    if ref["status"] == "imported":
        e["status"] = "provided_but_unfindable"
        e["resolution"] = dict(ref["resolution"], ref=ref["id"])
        _emit_unfindable_warn(ledger, e, ref, warned_refs)
    elif ref["status"] in ("already_in_heap", "not_found",
                           "import_failed", "provided_but_unfindable"):
        e["status"] = ref["status"]
        e["resolution"] = dict(ref["resolution"], ref=ref["id"])
    else:
        e["status"] = "duplicate"
        e["resolution"] = {"ref": ref["id"]}


def apply_verdicts(ledger: Ledger, out: Path, claim_ids: list[str]) -> list[str]:
    """Read a verdict file; update the ledger. Returns confirmed-missing
    theories (deduped) needing phase 2.

    Two passes (评审 H1): non-duplicate verdicts land first, duplicates
    second — a same-batch twin must read its representative's REAL
    adjudication, not the transient `searching` every batched claim carries.
    Duplicate refs are resolved transitively (_resolve_dup_target); an
    unresolvable chain re-pends the claim instead of freezing it wrong."""
    theories: list[str] = []
    try:
        data = json.loads(out.read_text(encoding="utf-8"))
        verdicts = {v["claim_id"]: v for v in data.get("verdicts", [])}
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as e:
        log(f"WARNING: unreadable verdict file {out}: {e} — claims back to pending")
        verdicts = {}
    dup_ids: list[str] = []
    for cid in claim_ids:
        e = ledger.by_id(cid)
        v = verdicts.get(cid)
        if v is None:
            e["status"] = "pending"  # agent skipped it — retry later
            continue
        verdict = v.get("verdict")
        if verdict == "duplicate" and v.get("duplicate_of"):
            dup_ids.append(cid)  # second pass
            continue
        e["resolution"] = {k: v.get(k) for k in
                           ("lemma_name", "theory", "evidence", "notes") if v.get(k)}
        if verdict == "missing_import" and v.get("theory"):
            e["status"] = "missing_import"
            if v["theory"] not in theories:
                theories.append(v["theory"])
        elif verdict == "already_in_heap":
            e["status"] = "already_in_heap"
        elif verdict == "not_found":
            e["status"] = "not_found"
        else:
            e["status"] = "pending"
    warned_refs: set = set()
    for cid in dup_ids:
        e = ledger.by_id(cid)
        ref = _resolve_dup_target(ledger, verdicts, verdicts[cid]["duplicate_of"])
        if ref is None or ref["id"] == cid:
            log(f"WARNING: {cid}: unresolvable duplicate_of chain "
                f"(→ {verdicts[cid]['duplicate_of']}) — back to pending")
            e["status"] = "pending"
            continue
        _inherit_duplicate(ledger, e, ref, warned_refs)
    ledger.save()
    return theories


_BUILD_CMD = ("RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 "
              "-o system_heaps MathBench_ProverBase")
# Judgment work goes to the agent, every deterministic step to the watcher
# (用户决定 2026-06-12). The three files the agent may promote into:
_MATHBENCH_FILES = ("tasks/MathBench_Prover/MathBench_Prover.thy",
                    "tasks/MathBench_Prover/Base/MathBench_ProverBase.thy",
                    "tasks/MathBench_Prover/ROOT")
# D1 circuit breaker (用户: 兜底即可，重点在报错): a theory fed into this many
# phase-2 rounds without EITHER getting imported OR being judged failed is
# force-closed as import_failed and surfaced loudly.
PHASE2_STUCK_LIMIT = 2


def _theory_stuck_path() -> Path:
    return STATE_DIR / "theory_stuck.json"


def _load_theory_stuck() -> dict:
    return _load_json(_theory_stuck_path(), {})


def _save_theory_stuck(d: dict) -> None:
    _save_json(_theory_stuck_path(), d)


def _theory_dead(theory: str) -> bool:
    """True once the circuit breaker has given up on *theory* (hit
    PHASE2_STUCK_LIMIT). Tracked per-THEORY in a side file (M4) so a re-reported
    claim that becomes a fresh ledger entry cannot reset the count."""
    return bool(theory) and _load_theory_stuck().get(theory, 0) >= PHASE2_STUCK_LIMIT


def _note_phase2_no_progress(ledger: Ledger, theories: set, reason: str) -> None:
    """Per-theory circuit breaker. Count a progress-less phase-2 round for each
    theory in a side file — NOT per ledger entry: a re-report becomes a fresh
    entry whose per-entry counter would reset (the A3 cycling bug). At
    PHASE2_STUCK_LIMIT, mark every still-missing entry of that theory
    import_failed so it stops re-triggering the barrier."""
    theories = {t for t in theories if t}
    if not theories:
        return
    stuck = _load_theory_stuck()
    for th in theories:
        n = stuck.get(th, 0) + 1
        stuck[th] = n
        if n >= PHASE2_STUCK_LIMIT:
            for e in ledger.entries:
                if (e["status"] == "missing_import"
                        and e["resolution"].get("theory") == th):
                    e["status"] = "import_failed"
                    e["resolution"]["notes"] = (
                        f"circuit breaker: {n} phase-2 rounds without progress "
                        f"({reason}) — needs human/supervisor attention")
            emit_event("WARN", "phase2_circuit_breaker", theory=th,
                       rounds=n, reason=reason)
    _save_theory_stuck(stuck)
    ledger.save()


def _clear_theory_stuck(theories: set) -> None:
    """A theory that finally landed clears its no-progress count."""
    theories = {t for t in theories if t}
    if not theories:
        return
    stuck = _load_theory_stuck()
    if any(th in stuck for th in theories):
        for th in theories:
            stuck.pop(th, None)
        _save_theory_stuck(stuck)


def _promotion_marker() -> Path:
    return STATE_DIR / "phase2" / "PROMOTING.json"


def _recover_crashed_promotion() -> None:
    """m1: if a prior run_phase2 died AFTER promoting the MathBench source but
    BEFORE its rebuild succeeded, the marker survives and points at the pre-edit
    snapshot — restore it so the next build starts from a buildable state (a
    half-promoted source would otherwise fail every later build)."""
    m = _promotion_marker()
    if not m.exists():
        return
    try:
        snap = Path(json.loads(m.read_text(encoding="utf-8"))["snapshot"])
        for rel in _MATHBENCH_FILES:
            src = snap / Path(rel).name
            if src.exists():
                shutil.copy2(src, ROOT / rel)
        log(f"m1: recovered a crashed phase-2 promotion — restored MathBench "
            f"source from {snap}")
        emit_event("WARN", "phase2_promotion_recovered", snapshot=str(snap))
    except (OSError, json.JSONDecodeError, KeyError) as e:
        log(f"WARNING: could not recover crashed promotion: {e}")
    finally:
        m.unlink(missing_ok=True)


def run_phase2(cfg, ledger: Ledger, theories: list[str],
               restart_proving: bool = True) -> bool:
    """Import *theories* into MathBench. The AGENT does the judgment half
    (inner-loop validation + promotion edits + submit_result); the watcher
    then runs the deterministic spine itself: heap rebuild → goal-gate
    re-check → ledger marking → isolated semantic collect → fresh AoA pair.
    Returns True iff the rebuilt heap passed the gate."""
    stamp = int(time.time())
    out = STATE_DIR / "phase2" / f"phase2_{stamp}.json"
    blog = STATE_DIR / "phase2" / f"build_{stamp}.log"
    log(f"PHASE 2: importing {theories}")
    if cfg.dry_run:
        log("dry-run: skipping phase 2")
        return False

    # m1: recover a prior promotion that crashed before its rebuild succeeded
    # (marker, if present, points at the pre-edit snapshot).
    _recover_crashed_promotion()

    # D5①: ensure heap == source BEFORE the agent starts. A lingering re-entry
    # (earlier round promoted files but never rebuilt) would otherwise make
    # the agent's first `mathbench_repl.py restart` silently trigger a full
    # rebuild it cannot wait for. No-op seconds when already fresh.
    log("pre-agent heap freshness build (no-op when fresh)")
    pre_rc = bash_timed(f"{_BUILD_CMD} >> {blog} 2>&1",
                        timeout=cfg.build_timeout)
    env_note = ""
    if pre_rc != 0:
        tail = ""
        try:
            tail = blog.read_text(encoding="utf-8", errors="replace")[-2000:]
        except OSError:
            pass
        env_note = (
            "\n## Environment note (pre-build failed)\n\n"
            "The watcher's pre-agent heap freshness build of "
            "MathBench_ProverBase FAILED — the promoted state left by an "
            "earlier round is probably broken. Diagnosing and repairing the "
            "three MathBench files so the session builds again is part of "
            "your job this round. Build log tail:\n\n```\n" + tail + "\n```\n")
        emit_event("WARN", "phase2_prebuild_failed", log=str(blog))
        log(f"WARNING: pre-agent build failed (exit {pre_rc}) — the agent "
            f"will be asked to repair the promoted state")

    # P3: snapshot the three files (post-pre-build = last known-good when
    # pre_rc==0) so a failed post-agent rebuild can restore a buildable state
    # instead of leaving broken promoted source that every later REPL start
    # would implicitly retry to build.
    snapdir = STATE_DIR / "phase2" / f"snapshot_{stamp}"
    snapdir.mkdir(parents=True, exist_ok=True)
    for rel in _MATHBENCH_FILES:
        shutil.copy2(ROOT / rel, snapdir / Path(rel).name)
    # m1: mark the source as about-to-be-promoted; cleared once the rebuild
    # succeeds. A crash in between leaves this marker → the next run restores.
    _promotion_marker().write_text(
        json.dumps({"snapshot": str(snapdir)}), encoding="utf-8")

    template = (PROMPT_DIR / "phase2_prompt.md").read_text(encoding="utf-8")
    prompt = template.replace("THEORIES_PLACEHOLDER",
                              "\n".join(f"- {t}" for t in theories)) + env_note
    from permission_gate import PHASE2_MISSION
    answer_tool, holder = _make_result_tool()
    try:
        run_claude_agent(prompt, model=cfg.phase2_model,
                         transcript_path=out.with_suffix(".log"),
                         timeout=cfg.phase2_timeout,
                         mission=PHASE2_MISSION, answer_tool=answer_tool,
                         done=lambda: bool(holder))
    except Exception as e:
        log(f"WARNING: phase-2 agent raised {type(e).__name__}: {e} — "
            f"judging by its submitted result anyway")
    # Persist the submitted result (audit trail).
    out.write_text(json.dumps(holder, indent=2, ensure_ascii=False),
                   encoding="utf-8")
    if not holder:
        log("ERROR: phase-2 agent never called submit_result; aborting phase 2")
        emit_event("WARN", "phase2_no_result", theories=theories,
                   transcript=str(out.with_suffix(".log")))
        _note_phase2_no_progress(ledger, set(theories), "no submit_result")
        return False
    result = holder
    imported = {i["theory"] for i in result.get("imported", []) if i.get("theory")}
    failed = {i["theory"]: i.get("reason", "?") for i in result.get("failed", [])}
    if not result.get("files_promoted") or not imported:
        log(f"phase 2 promoted nothing (imported={imported}, failed={failed})")
        for e in ledger.entries:
            if e["status"] == "missing_import" and e["resolution"].get("theory") in failed:
                e["status"] = "import_failed"
                e["resolution"]["notes"] = failed[e["resolution"]["theory"]]
        ledger.save()
        _note_phase2_no_progress(ledger, set(theories) - set(failed),
                                 "submitted without promoting")
        return False

    # Deterministic spine (用户决定 2026-06-12: 固定脚本流程，不进 agent 会话
    # —— 长步骤在会话里曾连续两晚破坏交付): heap rebuild → 7777 restart →
    # authoritative goal gate. The agent only judged and edited files.
    log(f"rebuilding MathBench_ProverBase heap (deterministic; log: {blog})")
    rc = bash_timed(f"{_BUILD_CMD} >> {blog} 2>&1", timeout=cfg.build_timeout)
    if rc != 0:
        log(f"ERROR: heap rebuild failed (exit {rc}, see {blog}) — restoring "
            f"the pre-agent file snapshot; old heap remains valid")
        # P3: without the restore, the broken promoted source would make every
        # later REPL start implicitly retry this failed build forever.
        for rel in _MATHBENCH_FILES:
            shutil.copy2(snapdir / Path(rel).name, ROOT / rel)
        _promotion_marker().unlink(missing_ok=True)  # restored → buildable
        for e in ledger.entries:
            th = e["resolution"].get("theory")
            if e["status"] == "missing_import" and th in (imported | set(failed)):
                e["status"] = "import_failed"
                e["resolution"]["notes"] = (
                    failed.get(th) or f"heap rebuild failed, see {blog}")
        ledger.save()
        emit_event("WARN", "phase2_build_failed", theories=sorted(imported),
                   log=str(blog), snapshot_restored=True)
        _note_phase2_no_progress(
            ledger, set(theories) - imported - set(failed), "build failed")
        return False
    # m1: rebuild succeeded → source and heap are consistent; the snapshot is
    # no longer needed to recover a crash.
    _promotion_marker().unlink(missing_ok=True)
    log("heap rebuilt; re-running the authoritative goal gate")
    rc = bash_timed(f"RPC_Host=127.0.0.1:27180 python tools/mathbench_repl.py "
                    f"restart >> {blog} 2>&1", timeout=900)
    if rc != 0:
        raise RuntimeError(
            f"post-rebuild 7777 REPL restart failed/timed out (see {blog}) — "
            f"environment state is suspect; aborting the run")
    rc = bash_timed(f"python -m tools.test_mathbench_goals >> {blog} 2>&1",
                    timeout=3600)
    if rc != 0:
        # The heap on disk now CONTAINS the import but provably changes goal
        # terms (or is unverified, on timeout) — running ANY case against it
        # would corrupt results. D2 (用户决定): persist an explicit interlock
        # that blocks every future run until the supervisory agent (or the
        # user) repairs the environment and removes the marker after a green
        # rebuild+gate. Entries stay missing_import on purpose.
        marker = STATE_DIR / "HEAP_SUSPECT"
        marker.write_text(
            f"{datetime.now().isoformat()} post-rebuild goal gate "
            f"{'TIMED OUT' if rc == -1 else 'FAILED'} for {sorted(imported)}\n"
            f"build log: {blog}\n"
            f"Recovery: diagnose (agent judgment required), make the gate "
            f"green (`{_BUILD_CMD}` then `python -m tools.test_mathbench_goals`"
            f" must exit 0), then delete this file.\n", encoding="utf-8")
        emit_event("FATAL", "heap_suspect", theories=sorted(imported),
                   log=str(blog), marker=str(marker))
        raise RuntimeError(
            f"post-rebuild goal gate FAILED (see {blog}) — the rebuilt heap "
            f"is semantically suspect; HEAP_SUSPECT interlock written, no "
            f"run will start until it is cleared")
    log("post-rebuild goal gate green")

    # D3 (用户拍板 B 方案): the gate-green heap IS the import — mark the
    # ledger NOW with semantic_collect_failed preset (truthful: not yet in
    # the semantic index), so a crash during the hours-long collect can never
    # send the bookkeeping back to missing_import and re-burn the whole
    # spine. The flag is cleared right after a successful collect.
    refresh_heap_theories()
    heap_lines = (STATE_DIR / "heap_theories.txt").read_text(
        encoding="utf-8").splitlines()
    imported_entries = []
    for e in ledger.entries:
        if e["status"] == "missing_import":
            th = e["resolution"].get("theory")
            if th in imported:
                # P7: never trust the claim alone — the theory's source file
                # must actually appear in the rebuilt heap's listing.
                tname = th.rsplit(".", 1)[-1]
                if not any(ln.endswith(f"/{tname}.thy") for ln in heap_lines):
                    e["status"] = "import_failed"
                    e["resolution"]["notes"] = (
                        "agent reported imported but the theory is not "
                        "present in the rebuilt heap listing")
                    emit_event("WARN", "imported_not_in_heap", theory=th)
                    continue
                e["status"] = "imported"
                e["resolution"]["imported_at"] = datetime.now().isoformat()
                e["resolution"]["semantic_collect_failed"] = True  # until collected
                e["resolution"].pop("phase2_stuck_rounds", None)
                imported_entries.append(e)
            elif th in failed:
                e["status"] = "import_failed"
                e["resolution"]["notes"] = failed[th]
            elif th in theories:
                # In this batch but covered by neither imported nor failed —
                # the agent mis-spelled or dropped it (the prompt demands
                # verbatim echo). Mark it so it doesn't linger silently.
                e["status"] = "import_failed"
                e["resolution"]["notes"] = ("not covered by the phase-2 "
                                            "result (spelling drift?)")
    ledger.save()
    emit_event("INFO", "phase2_imported",
               theories=[e["resolution"].get("theory")
                         for e in imported_entries])

    # M4: per-theory circuit-breaker bookkeeping. Theories asked-for that did
    # NOT end up `imported` this round (agent mis-promoted, or P7 found them
    # absent from the heap listing) count as a no-progress round — tracked per
    # theory so re-reports can't reset it; theories that landed clear their
    # counter. This is the path the old per-entry counter missed (A3).
    landed = {e["resolution"].get("theory") for e in imported_entries}
    _clear_theory_stuck(landed)
    not_landed = {t for t in theories if t} - landed
    if not_landed:
        _note_phase2_no_progress(ledger, not_landed,
                                 "asked to import but did not land in the heap")

    # Isolated semantic collect (6665/27183), then a fresh AoA pair
    # (6666/27182) for the re-run. A collect failure leaves the truthful
    # semantic_collect_failed flag in place — the supervisory agent heals it
    # later; the import itself stays valid.
    if run_semantic_collect(cfg):
        for e in imported_entries:
            e["resolution"].pop("semantic_collect_failed", None)
        ledger.save()
    # The fleet driver restarts the whole compute fleet itself (scancel +
    # relaunch with the rebuilt heap); only the single-host caller needs the
    # local 6666/27182 pair back.
    if restart_proving:
        restart_repl(cfg)
    return True


# ---------------------------------------------------------------------------
# REPL + heap helpers
# ---------------------------------------------------------------------------

def port_listening(port: int) -> bool:
    r = subprocess.run(["ss", "-tln"], capture_output=True, text=True)
    return bool(re.search(rf":{port}\b", r.stdout))


def _orphan_prover_marked(pid: int) -> bool:
    """Positive domain identification: /proc/<pid>/environ carries the AoA
    (27182) or collect (27183) RPC_Host token. Exact-token match on the
    \\0-split environ (the _host_env_ok pattern) — never a substring scan."""
    try:
        environ = Path(f"/proc/{pid}/environ").read_bytes()
    except OSError:
        return False
    return any(tok in _ORPHAN_ENV_MARKERS for tok in environ.split(b"\0"))


def _comm(pid: int) -> str | None:
    try:
        return Path(f"/proc/{pid}/comm").read_text().strip()
    except OSError:
        return None


def _sigterm_orphan_provers() -> list[tuple[int, str]]:
    """Find and SIGTERM the sledgehammer provers stranded by the REPLs this
    module just killed: comm in _PROVER_NAMES (pgrep -x — comm only, never -f)
    AND environ marker (_orphan_prover_marked). One unified SIGTERM pass over
    the whole confirmed set, so a dying cvc5 wrapper cannot shed its cvc5-bin
    child before the child is signalled. Returns the confirmed set for the
    post-grace SIGKILL step."""
    confirmed = []
    for name in _PROVER_NAMES:
        r = subprocess.run(["pgrep", "-x", name], capture_output=True, text=True)
        confirmed += [(int(tok), name) for tok in r.stdout.split()
                      if _orphan_prover_marked(int(tok))]
    for pid, _ in confirmed:
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    if confirmed:
        log(f"sweeping {len(confirmed)} orphan prover(s) of the AoA/collect "
            f"domains: {confirmed}")
    return confirmed


def _sigkill_orphan_survivors(confirmed: list[tuple[int, str]]) -> None:
    """SIGKILL whatever survived the SIGTERM grace — but re-verify identity
    first (comm still whitelisted AND marker still present): between SIGTERM
    and now the pid may have been recycled to an innocent process
    (_host_identity_ok rationale). Emits the supervisory WARN event."""
    if not confirmed:
        return
    time.sleep(2)   # rest of the grace; caller's sleep(3) was the first part
    sigkilled = []
    for pid, name in confirmed:
        if _comm(pid) == name and _orphan_prover_marked(pid):
            try:
                os.kill(pid, signal.SIGKILL)
                sigkilled.append(pid)
            except ProcessLookupError:
                pass
    emit_event("WARN", "orphan_provers_swept",
               procs=[{"pid": p, "name": n} for p, n in confirmed],
               sigkilled=sigkilled)


def kill_repl_and_host() -> None:
    """Stop the 6666 REPL server (LISTEN side only — not clients of the port)
    and the shared Isabelle_RPC_Host, then sweep the prover orphans they
    strand (see _PROVER_NAMES). WARNING: terminates every session other
    agents may have on them — by design the watcher owns both during a run.
    Note: with --no-restart-repl and a live 6666 this is never reached at
    startup — correct, since that REPL's provers may be legitimately working."""
    global _RPC_HOST_PID
    subprocess.run(["bash", "-c",
                    f"lsof -ti tcp:{REPL_PORT} -s TCP:LISTEN | xargs -r kill"],
                   cwd=ROOT)
    subprocess.run(["pkill", "-f", "fork_and_launch__"])
    _RPC_HOST_PID = None
    orphans = _sigterm_orphan_provers()
    time.sleep(3)
    _sigkill_orphan_survivors(orphans)


def _host_env_ok(pid: int, survey_interval: int) -> bool:
    """True iff /proc/<pid>/environ carries the survey variable with the
    expected value."""
    want = f"AOA_MISSING_LEMMA_SURVEY={survey_interval}".encode()
    try:
        environ = Path(f"/proc/{pid}/environ").read_bytes()
    except OSError:
        return False
    return want in environ.split(b"\0")


def _host_identity_ok(pid: int) -> bool:
    """Guard against pid reuse: the process must still be OUR host — its
    cmdline carries the RPC address."""
    try:
        return RPC_HOST_ADDR.encode() in Path(f"/proc/{pid}/cmdline").read_bytes()
    except OSError:
        return False


def _find_listening_host_pid() -> int | None:
    """Pid of the process LISTENING on the RPC host port, if any."""
    port = RPC_HOST_ADDR.rsplit(":", 1)[1]
    r = subprocess.run(["bash", "-c",
                        f"lsof -ti tcp:{port} -s TCP:LISTEN"],
                       capture_output=True, text=True)
    pids = [int(x) for x in r.stdout.split() if x.strip()]
    return pids[0] if pids else None


def start_rpc_host(cfg, addr: str = RPC_HOST_ADDR,
                   extra_env: dict | None = None) -> int:
    """Pre-start the Isabelle_RPC_Host with AOA_MISSING_LEMMA_SURVEY in its
    environment (watcher owns the host — 用户方案 2026-06-11). Verifies via
    /proc/<pid>/environ that the variable actually reached the daemon, which
    is the deterministic replacement for the lazy-spawn env race.

    *addr* is the bind address. The single-host path binds 127.0.0.1; the fleet
    binds 0.0.0.0:PORT so EVERY compute REPL connects to this ONE login-node
    host — that keeps the semantic retrieval DB (SQLite/LMDB on lustre) touched
    by a SINGLE process, instead of N concurrent compute-node hosts corrupting
    it ("file is not a database"). 用户方案 2026-06-17."""
    global _RPC_HOST_PID
    env = dict(os.environ, AOA_MISSING_LEMMA_SURVEY=str(cfg.survey_interval),
               AOA_MISSING_LEMMA_FEEDBACK=str(SURVEY_FEEDBACK_PATH))
    if extra_env:
        env.update(extra_env)
    logp = STATE_DIR / "rpc_host.log"
    r = subprocess.run(
        [sys.executable, "-c",
         "import Isabelle_RPC_Host\nIsabelle_RPC_Host.fork_and_launch__()",
         addr, str(logp)],
        cwd=ROOT, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"failed to launch Isabelle_RPC_Host: {r.stderr[-1000:]}")
    deadline = time.time() + 30
    pid = None
    while time.time() < deadline and pid is None:
        time.sleep(1)
        pg = subprocess.run(["pgrep", "-f", "fork_and_launch__"],
                            capture_output=True, text=True)
        for cand in sorted((int(x) for x in pg.stdout.split() if x.strip()),
                           reverse=True):
            try:  # several hosts can coexist (e.g. 27180) — match OUR address
                cmdline = Path(f"/proc/{cand}/cmdline").read_bytes()
            except OSError:
                continue
            if addr.encode() in cmdline:
                pid = cand
                break
    if pid is None:
        raise RuntimeError(f"Isabelle_RPC_Host did not appear (see {logp})")
    if not _host_env_ok(pid, cfg.survey_interval):
        raise RuntimeError(
            f"Isabelle_RPC_Host pid {pid} is running WITHOUT "
            f"AOA_MISSING_LEMMA_SURVEY={cfg.survey_interval} in its environment "
            f"— the survey channel is broken; refusing to continue")
    _RPC_HOST_PID = pid
    log(f"Isabelle_RPC_Host pid {pid} up with survey interval "
        f"{cfg.survey_interval} (verified via /proc)")
    return pid


def check_rpc_host_alive(cfg) -> None:
    """Keep the survey channel guaranteed when the watcher-owned RPC host
    disappears. The host can be killed by concurrent agent sessions on this
    shared machine (`pkill -f fork_and_launch__` is a documented dev step —
    observed live 2026-06-11 18:14); the REPL then lazily respawns one,
    inheriting the REPL's own env, which the watcher deliberately seeded with
    the survey variable (the designed backstop). So instead of aborting the
    night on a pid change, RE-VERIFY: adopt a replacement whose /proc environ
    carries the variable; restart the host ourselves when nobody listens;
    fail only when a listener provably lacks the variable."""
    global _RPC_HOST_PID
    if _RPC_HOST_PID is None:
        return
    if (Path(f"/proc/{_RPC_HOST_PID}").exists()
            and _host_identity_ok(_RPC_HOST_PID)):
        return
    dead = _RPC_HOST_PID
    _RPC_HOST_PID = None
    repl = _find_listening_host_pid()
    if repl is not None:
        if _host_env_ok(repl, cfg.survey_interval):
            _RPC_HOST_PID = repl
            log(f"WARNING: watcher-owned Isabelle_RPC_Host (pid {dead}) died; "
                f"adopted replacement pid {repl} (survey env verified via /proc). "
                f"The AoA session that lived in the dead host is lost — its "
                f"attempt will fail and be retried.")
            emit_event("WARN", "host_adopted", dead_pid=dead, new_pid=repl)
            return
        raise RuntimeError(
            f"watcher-owned Isabelle_RPC_Host (pid {dead}) died and the "
            f"replacement pid {repl} lacks AOA_MISSING_LEMMA_SURVEY="
            f"{cfg.survey_interval} — the survey channel is broken")
    log(f"WARNING: watcher-owned Isabelle_RPC_Host (pid {dead}) died with no "
        f"replacement listening — restarting it")
    emit_event("WARN", "host_restarted", dead_pid=dead)
    start_rpc_host(cfg)


def run_semantic_collect(cfg) -> bool:
    """Semantic collect against a DEDICATED REPL (6665) whose ML callbacks go
    to a DEDICATED RPC address (27183) — semantics_manage serves that address
    in-process when it is free, so the interpretation agent lives and dies
    with the collect, never inside the watcher-owned AoA host. Returns True
    iff the collect succeeded. Always leaves 6665 stopped."""
    def _kill_6665_listener() -> None:
        subprocess.run(["bash", "-c",
                        f"lsof -ti tcp:{COLLECT_REPL_PORT} -s TCP:LISTEN "
                        f"| xargs -r kill"], cwd=ROOT)

    kill_repl_and_host()   # one big-heap REPL at a time (also idempotent)
    # A STALE 6665 from a crashed earlier round would make port_listening
    # true instantly and the collect would run against an OLD heap with
    # collect_ok=True — silent index poisoning. Sweep first.
    _kill_6665_listener()
    time.sleep(2)
    log(f"starting dedicated collect REPL on {COLLECT_REPL_ADDR}")
    env = dict(os.environ, RPC_Host=COLLECT_RPC_ADDR)
    logf = open(STATE_DIR / "collect_repl.log", "a", encoding="utf-8")
    repl_proc = subprocess.Popen(
        ["bash", "-c", f"source envir.sh && exec {COLLECT_REPL_START_CMD}"],
        cwd=ROOT, env=env, stdout=logf, stderr=subprocess.STDOUT,
        start_new_session=True)
    logf.close()
    collect_ok = False
    try:
        deadline = time.time() + cfg.repl_ready_timeout
        while not port_listening(COLLECT_REPL_PORT):
            if time.time() > deadline:
                log(f"ERROR: collect REPL on {COLLECT_REPL_PORT} did not come "
                    f"up (see {STATE_DIR/'collect_repl.log'}) — skipping collect")
                return False
            time.sleep(10)
        time.sleep(15)
        log("semantic collect (this can take a while)…")
        rc = bash_timed(SEMANTIC_COLLECT_CMD, timeout=cfg.collect_timeout)
        collect_ok = rc == 0
        if not collect_ok:
            log(f"ERROR: semantic collect failed (exit {rc}) — new lemmas "
                f"will be invisible to `query` until collected; flagged in "
                f"the ledger")
        return collect_ok
    finally:
        kill_proc(repl_proc)        # whole process group, incl. mid-startup
        _kill_6665_listener()       # the daemonized server it may have left
        if not collect_ok:
            emit_event("WARN", "semantic_collect_failed",
                       log=str(STATE_DIR / "collect_repl.log"))


def restart_repl(cfg) -> None:
    """Kill REPL + host, pre-start the host with the survey env (verified),
    then start the REPL server and wait until the port listens."""
    log("restarting Isabelle_RPC_Host + REPL on 6666")
    kill_repl_and_host()
    start_rpc_host(cfg)
    # The REPL also gets the env var: if the host ever dies and the REPL's
    # Isabelle respawns it lazily, the respawn inherits a CORRECT environment.
    # RPC_Host is pinned explicitly — an operator shell that happens to export
    # a different RPC_Host must not silently re-route the REPL's callbacks
    # away from the watcher-owned host.
    env = dict(os.environ, AOA_MISSING_LEMMA_SURVEY=str(cfg.survey_interval),
               AOA_MISSING_LEMMA_FEEDBACK=str(SURVEY_FEEDBACK_PATH),
               RPC_Host=RPC_HOST_ADDR)
    logf = open(STATE_DIR / "repl_server.log", "a", encoding="utf-8")
    subprocess.Popen(["bash", "-c", f"source envir.sh && exec {REPL_START_CMD}"],
                     cwd=ROOT, env=env, stdout=logf, stderr=subprocess.STDOUT,
                     start_new_session=True)
    logf.close()  # Popen dup'ed the fd
    deadline = time.time() + cfg.repl_ready_timeout
    while time.time() < deadline:
        if port_listening(REPL_PORT):
            log("REPL port 6666 is listening")
            time.sleep(15)  # settle: heap load continues after bind
            return
        time.sleep(10)
    raise RuntimeError("REPL on 6666 did not come up in time "
                       f"(see {STATE_DIR/'repl_server.log'})")


def refresh_heap_theories() -> Path:
    out = STATE_DIR / "heap_theories.txt"
    log("refreshing heap theory list")
    # NOTE: `isabelle build -n` exits non-zero when some listed session has no
    # built heap image yet; the listing itself is still complete, so judge by
    # output content rather than exit code.
    r = bash(HEAP_LIST_CMD, capture_output=True, text=True)
    # `isabelle build -n -l` prints `Session CHAPTER/NAME` headers followed by
    # the session's source FILES (two-space indented absolute paths). Keep the
    # session headers and the .thy paths — the search agent decides heap
    # membership by matching a found lemma's .thy path against this list.
    keep = [ln.strip() for ln in r.stdout.splitlines()
            if ln.startswith("Session ")
            or (ln.startswith("  ") and ln.rstrip().endswith(".thy"))]
    n_thy = sum(1 for k in keep if k.endswith(".thy"))
    if n_thy == 0:
        raise RuntimeError(
            f"`{HEAP_LIST_CMD}` produced no .thy entries "
            f"(exit {r.returncode}):\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    out.write_text("\n".join(keep) + "\n", encoding="utf-8")
    log(f"{n_thy} theory files in heap → {out}")
    return out


# ---------------------------------------------------------------------------
# Evaluator subprocess
# ---------------------------------------------------------------------------

def start_eval(cfg, case: str, force_retry: bool) -> subprocess.Popen:
    cmd = [sys.executable, "evaluation/evaluator_top.py", "agent-putnam",
           cfg.driver, "-c", case, "--result", cfg.result,
           "--timeout-seconds", str(cfg.timeout_seconds),
           "--log-dir", cfg.log_dir]
    if force_retry:
        cmd += ["--force-retry", case]
    log(f"evaluator → {case} (force_retry={force_retry})")
    logf = open(STATE_DIR / f"eval_{case}.log", "a", encoding="utf-8")
    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=logf, stderr=subprocess.STDOUT,
                            start_new_session=True)
    logf.close()  # Popen dup'ed the fd
    return proc


def kill_proc(proc: subprocess.Popen) -> None:
    if proc.poll() is None:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            proc.wait(timeout=30)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass


def case_status(cfg, case: str) -> str | None:
    """Read the case's status from the result db ('SUCCESS'/'FAIL'/…) or None."""
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from sqlitedict import SqliteDict  # noqa: deferred heavy import
    import evaluation.evaluator  # noqa: F401  (Result unpickling)
    with SqliteDict(cfg.result) as db:
        if case in db:
            return db[case].status.value
    return None


class CaseState:
    """Per-case loop bookkeeping that must survive watcher crashes:
    attempt counts, outcome history, and the 'a phase 2 just ran for this
    case — it is OWED a re-run' flag (without it, a crash between phase 2 and
    the re-run would permanently skip the very case the heap was grown for)."""

    def __init__(self):
        self.path = STATE_DIR / "case_state.json"
        self.data: dict = _load_json(self.path, {})

    def of(self, case: str) -> dict:
        return self.data.setdefault(
            case, {"attempts": 0, "rerun_owed": False, "outcomes": []})

    def save(self) -> None:
        _save_json(self.path, self.data)


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def run_one_case(cfg, ledger: Ledger, offsets: dict, case: str,
                 cstate: CaseState, *, canary_armed: bool = False) -> None:
    log_dir = Path(cfg.log_dir)
    st = cstate.of(case)
    while st["attempts"] < cfg.max_attempts:
        # Lingering confirmed-but-unimported theories (an earlier phase 2
        # aborted) are imported FIRST — running the attempt before they are
        # in the heap would just re-prove without them for a whole budget.
        lingering = {e["resolution"]["theory"] for e in ledger.entries
                     if e["status"] == "missing_import"
                     and e["resolution"].get("theory")}
        if lingering and not cfg.dry_run:
            log(f"lingering confirmed missing import(s) {sorted(lingering)} — "
                f"running phase 2 before the next attempt")
            ok = run_phase2(cfg, ledger, sorted(lingering))
            st["outcomes"].append(
                f"pre-attempt phase2({sorted(lingering)}) {'ok' if ok else 'FAILED'}")
            cstate.save()
            # run_phase2 already restarted REPL+host on success; on failure
            # the running pair was never touched — either way proceed.
        st["attempts"] += 1
        attempt = st["attempts"]
        force = attempt > 1 or st["rerun_owed"] or case_status(cfg, case) is not None
        st["rerun_owed"] = False
        cstate.save()
        log(f"=== {case} attempt {attempt}/{cfg.max_attempts} ===")
        # Survey feedback resets HERE, inside the attempt loop — not in the
        # case preamble, which pre-attempt phase-2 and retry-continue skip
        # (评审 M5). attempt_ids collects every claim ingested this attempt.
        attempt_ids: set[str] = set()
        write_survey_feedback(ledger, attempt_ids)
        proc = start_eval(cfg, case, force_retry=force)
        t_start = time.time()
        search: tuple[concurrent.futures.Future, Path, list[str], dict] | None = None
        phase2_theories: list[str] = []
        killed_for_phase2 = False
        try:
            while True:
                time.sleep(cfg.poll_interval)
                check_rpc_host_alive(cfg)
                attempt_ids.update(
                    e["id"] for e in scan_logs(log_dir, offsets, ledger, case))
                _save_json(STATE_DIR / "offsets.json", offsets)

                if search is not None and search[0].done():
                    phase2_theories += finish_search(ledger, search)
                    write_survey_feedback(ledger, attempt_ids)
                    search = None
                if search is None and not cfg.dry_run:
                    batch = ledger.pending()
                    if batch:
                        search = start_search(cfg, ledger, batch)

                if phase2_theories:
                    log(f"confirmed missing import(s) {phase2_theories} — "
                        f"stopping the run for phase 2")
                    kill_proc(proc)
                    # Kill REPL + host NOW: the AoA session lives inside the
                    # RPC host, not the evaluator — left alone it would burn
                    # DeepSeek spend for the whole phase-2 duration and write
                    # late claims attributed to the next case.
                    kill_repl_and_host()
                    killed_for_phase2 = True
                    break
                if proc.poll() is not None:
                    break

            # Drain: final scan + finish any in-flight / leftover searches.
            attempt_ids.update(
                e["id"] for e in scan_logs(log_dir, offsets, ledger, case))
            _save_json(STATE_DIR / "offsets.json", offsets)
            if search is not None:
                phase2_theories += finish_search(
                    ledger, search, wait_timeout=cfg.search_timeout)
                write_survey_feedback(ledger, attempt_ids)
            stale_rounds = 0
            while ledger.pending() and not cfg.dry_run:
                before = len(ledger.pending())
                s = start_search(cfg, ledger, ledger.pending())
                phase2_theories += finish_search(
                    ledger, s, wait_timeout=cfg.search_timeout)
                write_survey_feedback(ledger, attempt_ids)
                if len(ledger.pending()) >= before:
                    stale_rounds += 1
                    if stale_rounds >= 2:
                        log("WARNING: drain searches making no progress — "
                            "leaving remaining claims pending for the next case")
                        break
                else:
                    stale_rounds = 0
        finally:
            kill_proc(proc)

        # Re-feed theories confirmed in earlier rounds but never imported —
        # BEFORE the emptiness check: an aborted phase 2 (e.g. agent session
        # lost mid-build, 2026-06-11 23:32) leaves them status=missing_import
        # with no new confirmation coming, and they would otherwise linger
        # forever.
        lingering = {e["resolution"]["theory"] for e in ledger.entries
                     if e["status"] == "missing_import"
                     and e["resolution"].get("theory")}
        phase2_theories = sorted(set(phase2_theories) | lingering)
        if phase2_theories:
            if st["attempts"] >= cfg.max_attempts:
                # 用户拍板 16a + D4(a) 2026-06-12: no phase 2 inside the
                # closing case — the import is DEFERRED: the entries stay
                # missing_import, and the NEXT case's pre-attempt check
                # imports them (followed by that case's own attempt). This
                # case itself never re-runs.
                st["outcomes"].append(
                    f"attempt {attempt}: confirmed {phase2_theories} but "
                    f"attempt budget exhausted — recorded only")
                cstate.save()
                log(f"{case}: confirmed {phase2_theories} but attempt budget "
                    f"exhausted — skipping phase 2 (ledger keeps them)")
                if killed_for_phase2:
                    restart_repl(cfg)   # next case needs a live REPL
                return
            try:
                ok = run_phase2(cfg, ledger, phase2_theories)
            except RuntimeError:
                raise   # night-abort path; HEAP_SUSPECT/interlocks handle env
            except Exception:
                if killed_for_phase2:
                    restart_repl(cfg)   # restore service even on surprises
                raise
            st["outcomes"].append(
                f"attempt {attempt}: phase2({phase2_theories}) "
                f"{'ok' if ok else 'FAILED'}")
            st["rerun_owed"] = ok
            cstate.save()
            if ok:
                continue          # heap expanded → re-run the same case
            log("phase 2 failed/aborted — moving on")
            if killed_for_phase2:
                restart_repl(cfg)       # restore service for the next case
            return
        status = case_status(cfg, case)
        st["outcomes"].append(f"attempt {attempt}: {status}")
        cstate.save()
        log(f"{case} finished: {status}")
        emit_event("INFO", "case_finished", case=case, attempt=attempt,
                   status=status)
        return
    log(f"{case}: attempt limit reached")


# ---------------------------------------------------------------------------
# Multi-node fleet driver (--fleet)
#
# Proving runs as ONE long-lived slurmx distributed evaluator across the
# compute nodes named in config/evaluation_servers.csv. This login-node loop
# ingests surveys from the shared AoA log dir, runs the SAME serial batched
# adjudication as the single-host path, and on a confirmed missing_import does
# the barrier rebuild: kill the fleet → scancel (wait for the queue to clear)
# → run_phase2 (import / rebuild / goal-gate / collect, login-local) →
# relaunch a fresh fleet against the rebuilt heap (resume skips already-done
# cases). Everything except the proving layer is reused unchanged.
# ---------------------------------------------------------------------------

def launch_fleet_eval(cfg, extra_args: list | None = None) -> subprocess.Popen:
    """Spawn ONE `evaluator_top agent-putnam` over the whole test split as a
    killpg-able child. Its own launch_servers() self-allocates the slurmx fleet
    from the CSV. The survey switch + AoA log dir are exported here and reach
    every compute node via the eval's `srun --export=ALL`. B3: no per-attempt
    feedback file in the fleet — the AoA runtime memory + the dedup agent are
    the anti-repeat; the loader fail-opens to [] when the env is unset."""
    # The AoA Python (driver / retrieval / survey / logs) runs in the ONE
    # login-node RPC host the watcher pre-started; compute REPLs only run the
    # Isabelle ML and connect to it. Point them at it and forbid a local
    # lazy-spawn. The survey/log/feedback env lives on the LOGIN host, not here.
    rpc_port = RPC_HOST_ADDR.rsplit(":", 1)[1]
    env = dict(os.environ,
               CLUSTER="slurmx",
               SESSION="MathBench_Prover",
               SBATCH_JOB_NAME=cfg.job_name,
               RPC_Host=f"{cfg.rpc_host}:{rpc_port}",
               AUTO_START_RPC_SERVER="0")
    for _k in ("AOA_MISSING_LEMMA_SURVEY", "AOA_MISSING_LEMMA_FEEDBACK",
               "AoA_LOG_DIR"):
        env.pop(_k, None)
    cmd = [sys.executable, "evaluation/evaluator_top.py", "agent-putnam",
           cfg.driver, "--result", cfg.result, "--log-dir", cfg.log_dir,
           "--timeout-seconds", str(cfg.timeout_seconds)]
    # Honour an explicit case subset (targeted run / smoke); else the full split.
    if cfg.cases or cfg.case_file:
        for c in (cfg.cases or []):
            cmd += ["-c", c]
        if cfg.case_file:
            cmd += ["--case-file", cfg.case_file]
    else:
        cmd += ["--case-category", "test"]
    if extra_args:
        cmd += extra_args
    log(f"launching slurmx fleet eval (driver={cfg.driver}, job={cfg.job_name})")
    logf = open(STATE_DIR / "fleet_eval.log", "a", encoding="utf-8")
    proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=logf,
                            stderr=subprocess.STDOUT, start_new_session=True)
    logf.close()
    return proc


def _squeue_named(job_name: str, states: str | None = None) -> str:
    cmd = ["squeue", "-u", os.environ.get("USER", ""), "--name", job_name,
           "--noheader"]
    if states:
        cmd.append(f"--states={states}")
    try:
        return subprocess.run(cmd, capture_output=True, text=True,
                              timeout=60).stdout.strip()
    except (subprocess.SubprocessError, OSError) as e:
        log(f"WARNING: squeue failed: {e}")
        return ""


def scancel_fleet(cfg) -> None:
    """Cancel our slurmx jobs and WAIT until they leave the queue. scancel
    returns before a job leaves CG (completing) state, and slurm.run_server's
    check_node does a substring match on `squeue -u $USER` — a lingering job
    would make the NEXT fleet skip its srun and silently reuse a stale-heap
    REPL (B2 / F6 / F7). So poll until the queue is clear."""
    subprocess.run(["scancel", "--name", cfg.job_name],
                   capture_output=True, text=True)
    deadline = time.time() + cfg.scancel_timeout
    while time.time() < deadline:
        if not _squeue_named(cfg.job_name):
            return
        time.sleep(2)
    emit_event("WARN", "scancel_fleet_timeout", job=cfg.job_name,
               seconds=cfg.scancel_timeout)
    log(f"WARNING: jobs named {cfg.job_name} still in squeue after "
        f"{cfg.scancel_timeout}s — a relaunch may reuse a stale-heap REPL")


def _theory_imported(ledger: Ledger, theory: str) -> bool:
    return any(e["status"] == "imported"
               and e["resolution"].get("theory") == theory
               for e in ledger.entries)


def _filter_pending_theories(ledger: Ledger, theories: list[str]) -> list[str]:
    """Drop theories already in the heap (re-importing is a no-op that would
    just re-trigger the barrier) and theories the per-theory circuit breaker
    has given up on (M4) — so a re-reported dead theory cannot keep rebuilding."""
    return sorted({t for t in theories
                   if not _theory_imported(ledger, t) and not _theory_dead(t)})


def _lingering_theories(ledger: Ledger) -> list[str]:
    return sorted({e["resolution"]["theory"] for e in ledger.entries
                   if e["status"] == "missing_import"
                   and e["resolution"].get("theory")})


def _poll_fleet(cfg, proc, ledger, offsets, t_run_start) -> list[str]:
    """Poll a running fleet: ingest surveys from the shared log dir and run the
    serial batched adjudication. Return confirmed-importable theories as soon
    as a search confirms any (caller does the barrier rebuild); return [] when
    the fleet exits on its own (caller then drains)."""
    search = None
    phase2_theories: list[str] = []
    while True:
        time.sleep(cfg.poll_interval)
        scan_logs(Path(cfg.log_dir), offsets, ledger, case="?")
        _save_json(STATE_DIR / "offsets.json", offsets)

        if search is not None and search[0].done():
            phase2_theories += finish_search(ledger, search)
            search = None
        if search is None and not cfg.dry_run:
            batch = ledger.pending()
            if batch:
                search = start_search(cfg, ledger, batch)

        ready = _filter_pending_theories(ledger, phase2_theories)
        if ready:
            return ready

        if proc.poll() is not None:
            # Fleet ended. Let an in-flight search finish so its verdicts are
            # not dropped, then hand back whatever it confirmed (possibly []).
            if search is not None:
                phase2_theories += finish_search(
                    ledger, search, wait_timeout=cfg.search_timeout)
            return _filter_pending_theories(ledger, phase2_theories)


def _drain_adjudication(cfg, ledger, offsets) -> list[str]:
    """After the fleet exits: final scan + drain all remaining pending claims
    through the serial adjudicator (mirrors run_one_case's drain). Returns any
    newly confirmed importable theories."""
    scan_logs(Path(cfg.log_dir), offsets, ledger, case="?")
    _save_json(STATE_DIR / "offsets.json", offsets)
    theories: list[str] = []
    stale = 0
    while ledger.pending() and not cfg.dry_run:
        before = len(ledger.pending())
        s = start_search(cfg, ledger, ledger.pending())
        theories += finish_search(ledger, s, wait_timeout=cfg.search_timeout)
        if len(ledger.pending()) >= before:
            stale += 1
            if stale >= 2:
                log("WARNING: drain searches making no progress — leaving "
                    "remaining claims pending")
                break
        else:
            stale = 0
    return _filter_pending_theories(ledger, theories)


def _final_reverify(cfg) -> None:
    """M3: re-prove every currently-SUCCESS case against the FINAL heap. A
    phase-2 rebuild can break a passing proof WITHOUT changing its goal term —
    the goal gate cannot see that, and resume skips SUCCESS rows, so the result
    DB could carry a stale SUCCESS. Force-retrying the SUCCESSes once at the end
    flips any now-broken case to FAIL in the same DB, keeping the audit honest."""
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from sqlitedict import SqliteDict
    import evaluation.evaluator  # noqa: F401  (Result unpickling)
    succ = []
    with SqliteDict(cfg.result) as db:
        for k in db:
            try:
                if db[k].status.value == "SUCCESS":
                    succ.append(k)
            except Exception:
                continue
    if not succ:
        log("final re-verify: no SUCCESS cases to re-check")
        return
    frf = STATE_DIR / "final_reverify_cases.txt"
    frf.write_text("\n".join(str(c) for c in succ), encoding="utf-8")
    log(f"final re-verify: re-proving {len(succ)} SUCCESS case(s) against the "
        f"final heap (force-retry)")
    scancel_fleet(cfg)
    proc = launch_fleet_eval(cfg, extra_args=["--force-retry-file", str(frf)])
    try:
        proc.wait()
    finally:
        kill_proc(proc)
    scancel_fleet(cfg)
    log(f"final re-verify done (exit {proc.returncode})")


def cmd_run_fleet(cfg) -> None:
    for d in (STATE_DIR, STATE_DIR / "verdicts", STATE_DIR / "phase2"):
        d.mkdir(parents=True, exist_ok=True)
    Path(cfg.log_dir).mkdir(parents=True, exist_ok=True)
    marker = STATE_DIR / "HEAP_SUSPECT"
    if marker.exists():
        emit_event("FATAL", "run_refused_heap_suspect", marker=str(marker))
        raise RuntimeError(
            f"HEAP_SUSPECT interlock present — the MathBench heap failed its "
            f"post-rebuild goal gate and has not been repaired. See {marker}; "
            f"refusing to run.")
    ledger = Ledger(STATE_DIR / "ledger.json")
    offsets = _load_json(STATE_DIR / "offsets.json", {})

    stuck = [e for e in ledger.entries if e["status"] == "searching"]
    if stuck:
        for e in stuck:
            e["status"] = "pending"
        ledger.save()
        log(f"recovered {len(stuck)} claim(s) stuck in 'searching' → pending")

    init_embedding(ledger)
    if not (STATE_DIR / "heap_theories.txt").exists():
        refresh_heap_theories()

    # m2: import any lingering confirmed-but-unbuilt theories from a prior
    # crashed run BEFORE launching, so the fleet proves against a heap that
    # already has them.
    lingering = _lingering_theories(ledger)
    if lingering and not cfg.dry_run:
        log(f"lingering confirmed missing import(s) {lingering} — phase 2 "
            f"before launching the fleet")
        run_phase2(cfg, ledger, lingering, restart_proving=False)

    scancel_fleet(cfg)   # clear any stale fleet from a previous run (B2 / F7)

    # One login-node RPC host for the WHOLE fleet (用户方案 2026-06-17): every
    # compute REPL connects here (launch_fleet_eval points them at
    # cfg.rpc_host + AUTO_START_RPC_SERVER=0), so the semantic retrieval DB
    # on lustre is touched by a SINGLE process. Per-compute-node hosts each open
    # the shared SQLite/LMDB stores concurrently → "file is not a database".
    # Bind 0.0.0.0 so compute nodes can reach it; clear any leaked host first.
    subprocess.run(["pkill", "-9", "-f", "fork_and_launch__"], capture_output=True)
    time.sleep(1)
    rpc_port = RPC_HOST_ADDR.rsplit(":", 1)[1]
    log(f"starting login-node RPC host on 0.0.0.0:{rpc_port} "
        f"(compute REPLs connect to {cfg.rpc_host}:{rpc_port})")
    start_rpc_host(cfg, addr=f"0.0.0.0:{rpc_port}",
                   extra_env={"AoA_LOG_DIR": str(Path(cfg.log_dir).resolve())})

    rebuild_rounds = 0
    crash_relaunches = 0
    while True:
        proc = launch_fleet_eval(cfg)
        t_run_start = time.time()
        try:
            theories = _poll_fleet(cfg, proc, ledger, offsets, t_run_start)
        finally:
            kill_proc(proc)   # idempotent; an already-ended fleet is a no-op

        if not theories and proc.returncode not in (0, None):
            # Fleet exited nonzero WITHOUT confirming an import → a crash, not a
            # clean finish (M6). Bounded relaunch.
            crash_relaunches += 1
            if crash_relaunches > cfg.max_crash_relaunch:
                emit_event("FATAL", "fleet_crash_giveup",
                           rc=proc.returncode, relaunches=crash_relaunches)
                raise RuntimeError(
                    f"fleet eval crashed (rc={proc.returncode}) "
                    f"{crash_relaunches}x in a row — aborting")
            emit_event("WARN", "fleet_crashed_relaunch",
                       rc=proc.returncode, attempt=crash_relaunches)
            log(f"fleet eval exited rc={proc.returncode} with no confirmed "
                f"import — treating as crash, relaunch {crash_relaunches}/"
                f"{cfg.max_crash_relaunch}")
            scancel_fleet(cfg)
            continue
        crash_relaunches = 0

        if not theories:
            # Fleet finished cleanly. Drain remaining adjudication.
            theories = _drain_adjudication(cfg, ledger, offsets)
            if not theories:
                log("fleet complete and no confirmed imports pending — done")
                break

        # Barrier rebuild for the confirmed importable theories.
        rebuild_rounds += 1
        if rebuild_rounds > cfg.max_rebuilds:
            emit_event("FATAL", "rebuild_cap_exceeded", rounds=rebuild_rounds)
            raise RuntimeError(
                f"phase-2 rebuild cap ({cfg.max_rebuilds}) exceeded — likely a "
                f"non-converging import; aborting for inspection")
        log(f"confirmed missing import(s) {theories} — barrier rebuild "
            f"(round {rebuild_rounds}/{cfg.max_rebuilds})")
        scancel_fleet(cfg)
        run_phase2(cfg, ledger, theories, restart_proving=False)
        cmd_report(cfg)
        # loop: relaunch a fresh fleet against the rebuilt heap; resume skips
        # already-done cases and re-runs the not-run + interrupted ones.

    # M3: optional final re-verification of cached SUCCESSes against the final
    # heap (only meaningful if a rebuild happened).
    if cfg.final_reverify and rebuild_rounds > 0 and not cfg.dry_run:
        _final_reverify(cfg)
    cmd_report(cfg)
    # tear down the login RPC host (a FATAL exit leaks it; the next run's
    # pre-start pkill clears that).
    if _RPC_HOST_PID:
        try:
            os.kill(_RPC_HOST_PID, signal.SIGTERM)
            log(f"login RPC host {_RPC_HOST_PID} stopped")
        except ProcessLookupError:
            pass


def cmd_run(cfg) -> None:
    for d in (STATE_DIR, STATE_DIR / "verdicts", STATE_DIR / "phase2"):
        d.mkdir(parents=True, exist_ok=True)
    Path(cfg.log_dir).mkdir(parents=True, exist_ok=True)
    # D2 interlock (用户拍板: 解锁须 agent/人亲自判断修复，不机械自愈):
    marker = STATE_DIR / "HEAP_SUSPECT"
    if marker.exists():
        emit_event("FATAL", "run_refused_heap_suspect", marker=str(marker))
        raise RuntimeError(
            f"HEAP_SUSPECT interlock present — the MathBench heap failed its "
            f"post-rebuild goal gate and has not been repaired yet. See "
            f"{marker} for the recovery procedure; refusing to run.")
    ledger = Ledger(STATE_DIR / "ledger.json")
    offsets = _load_json(STATE_DIR / "offsets.json", {})
    cstate = CaseState()

    # Crash recovery: claims a dead watcher left mid-search would otherwise be
    # orphaned forever ("searching" is selected by nothing).
    stuck = [e for e in ledger.entries if e["status"] == "searching"]
    if stuck:
        for e in stuck:
            e["status"] = "pending"
        ledger.save()
        log(f"recovered {len(stuck)} claim(s) stuck in 'searching' → pending")

    # Survey feedback: clear BEFORE the host comes up (评审 H2) — a crashed
    # run's stale file would otherwise feed the first surveys cross-attempt
    # adjudications, which the user explicitly scoped out.
    write_survey_feedback(ledger, set())
    # Embedding candidate retrieval: probe + prewarm once, off the hot path.
    init_embedding(ledger)

    if not (STATE_DIR / "heap_theories.txt").exists():
        refresh_heap_theories()
    # The watcher OWNS the RPC host and the 6666 REPL: always (re)start both
    # so the survey env is deterministic (用户方案 2026-06-11), unless the
    # operator explicitly claims the running pair is already correct.
    if cfg.no_restart_repl and port_listening(REPL_PORT):
        log("WARNING: --no-restart-repl: reusing the running REPL/host — "
            "surveys fire only if the HOST's env already carries "
            "AOA_MISSING_LEMMA_SURVEY (cannot be guaranteed; canary still on)")
    else:
        restart_repl(cfg)

    explicit = set(cfg.cases or [])
    cases = list(cfg.cases or [])
    if cfg.case_file:
        file_cases = [ln.strip() for ln in open(cfg.case_file) if ln.strip()]
        cases += file_cases
        explicit |= set(file_cases)
    if not cases:
        if str(ROOT) not in sys.path:
            sys.path.insert(0, str(ROOT))
        from data.isabelle import PutnamBench_Data
        cases = list(PutnamBench_Data().cases_of("test"))

    # 已经跑过的不需要再跑 (skip prior SUCCESS/FAIL rows), EXCEPT:
    # explicitly named cases (naming one IS the intent to run it),
    # cases owed a re-run by an interrupted phase-2 round, and
    # CASE_NOT_AVAILABLE rows (transient env failures, not real attempts).
    queue = []
    for c in cases:
        s = case_status(cfg, c)
        if (s is None or s == "CASE_NOT_AVAILABLE" or c in explicit
                or cstate.of(c).get("rerun_owed")):
            queue.append(c)
    log(f"{len(queue)} case(s) to run ({len(cases) - len(queue)} skipped as already run)")

    for i, case in enumerate(queue):
        try:
            run_one_case(cfg, ledger, offsets, case, cstate,
                         canary_armed=(i == 0))
        except Exception as e:
            # One case's failure must not silently end the night — but env-
            # level failures (dead host/REPL, broken survey channel) must.
            marker = STATE_DIR / "FAILED"
            marker.write_text(f"{datetime.now().isoformat()} {case}: "
                              f"{type(e).__name__}: {e}\n", encoding="utf-8")
            cmd_report(cfg)
            if isinstance(e, RuntimeError):
                emit_event("FATAL", "night_aborted", case=case, error=str(e))
                raise
            emit_event("WARN", "case_crashed", case=case,
                       error=f"{type(e).__name__}: {e}")
            log(f"ERROR: {case} crashed ({type(e).__name__}: {e}) — continuing")
        cmd_report(cfg)


def cmd_scan(cfg) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    ledger = Ledger(STATE_DIR / "ledger.json")
    offsets = _load_json(STATE_DIR / "offsets.json", {})
    entries = scan_logs(Path(cfg.log_dir), offsets, ledger, case=cfg.scan_case or "?")
    _save_json(STATE_DIR / "offsets.json", offsets)
    log(f"ingested {len(entries)} new claim(s)")


def cmd_report(cfg) -> None:
    ledger = Ledger(STATE_DIR / "ledger.json")
    order = ["provided_but_unfindable", "import_failed", "missing_import",
             "imported", "already_in_heap", "not_found", "pending",
             "searching", "duplicate"]
    lines = [f"# Missing-lemma loop report — {datetime.now().isoformat()}",
             "", f"Total claims: {len(ledger.entries)}", ""]
    for status in order:
        group = [e for e in ledger.entries if e["status"] == status]
        if not group:
            continue
        lines += [f"## {status} ({len(group)})", ""]
        for e in group:
            r, res = e["report"], e["resolution"]
            name = r.get("name_guess") or r.get("name") or "?"
            lines.append(f"- **{e['id']}** `{name}` — case `{e['case']}` "
                         f"({e['trigger']})")
            if r.get("english"):
                lines.append(f"  - {r['english']}")
            for k in ("theory", "lemma_name", "evidence", "notes",
                      "imported_at", "semantic_collect_failed", "ref"):
                if res.get(k):
                    lines.append(f"  - {k}: {res[k]}")
        lines.append("")
    cstate = CaseState()
    if cstate.data:
        lines += ["## Per-case attempts", ""]
        for case, st in sorted(cstate.data.items()):
            owed = " (re-run owed)" if st.get("rerun_owed") else ""
            lines.append(f"- `{case}`: {st['attempts']} attempt(s){owed}")
            for o in st.get("outcomes", []):
                lines.append(f"  - {o}")
        lines.append("")
    (STATE_DIR / "report.md").write_text("\n".join(lines), encoding="utf-8")
    log(f"report → {STATE_DIR / 'report.md'}")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("command", nargs="?", default="run",
                   choices=["run", "scan", "report", "heap-dump"])
    p.add_argument("--driver", default="DeepSeek.V4-pro")
    p.add_argument("--result", default=str(ROOT / "result-missing-lemma-loop.db"))
    p.add_argument("--log-dir", default=str(ROOT / "missing_lemma_loop_logs"))
    p.add_argument("--cases", "-c", action="append")
    p.add_argument("--case-file")
    p.add_argument("--scan-case", help="case label for the `scan` subcommand")
    p.add_argument("--timeout-seconds", type=int, default=3600,
                   help="per-attempt budget (用户要求: 1 小时)")
    p.add_argument("--max-attempts", type=int, default=3,
                   help="max (re-)runs of one case across phase-2 rounds")
    p.add_argument("--poll-interval", type=int, default=15)
    p.add_argument("--survey-interval", type=int, default=10,
                   help="AOA_MISSING_LEMMA_SURVEY value for the REPL env")
    # 用户要求 (2026-06-11): 所有 Claude agent 一律 Opus 4.8；权限只用 Claude Code
    # 内置 auto mode（不可用即崩溃，绝无自制裁决/回落）。
    p.add_argument("--search-model", default="claude-opus-4-8[1m]",
                   help="model for the confirmation-search agent")
    p.add_argument("--phase2-model", default="claude-opus-4-8[1m]",
                   help="model for the phase-2 import/reconcile agent")
    p.add_argument("--search-timeout", type=int, default=1800)
    p.add_argument("--phase2-timeout", type=int, default=4 * 3600,
                   help="phase-2 AGENT session cap (judgment + edits only; "
                        "the heap rebuild is outside the session)")
    p.add_argument("--build-timeout", type=int, default=2 * 3600,
                   help="deterministic heap-rebuild step cap")
    p.add_argument("--collect-timeout", type=int, default=6 * 3600,
                   help="semantic-collect step cap (fresh AFP sessions can "
                        "need hours of interpretation)")
    p.add_argument("--repl-ready-timeout", type=int, default=1800)
    p.add_argument("--canary-seconds", type=int, default=1200,
                   help="abort if the first case runs this long without ANY "
                        "survey doc appearing (survey-channel canary)")
    p.add_argument("--no-restart-repl", action="store_true",
                   help="reuse the already-running REPL/host instead of the "
                        "default kill+restart (env then NOT guaranteed)")
    p.add_argument("--dry-run", action="store_true",
                   help="no claude calls, no phase 2 — just run + scan")
    # --- multi-node fleet driver ---
    p.add_argument("--fleet", action="store_true",
                   help="distributed slurmx fleet driver: one long eval across "
                        "the CSV's compute nodes with login-node orchestration "
                        "(instead of the single-host serial run)")
    p.add_argument("--job-name", default="mlloop",
                   help="SBATCH_JOB_NAME for the fleet's slurmx jobs; scancel "
                        "is scoped to this name (default: mlloop)")
    p.add_argument("--rpc-host", default="cscc-login-2.ib0.cscc-new.mbzuai.ac.ae",
                   help="login-node host the compute REPLs connect to for the "
                        "one shared RPC host — the compute-facing (ib0) name so "
                        "the high-speed network is used (default: "
                        "cscc-login-2.ib0.cscc-new.mbzuai.ac.ae)")
    p.add_argument("--max-rebuilds", type=int, default=30,
                   help="hard cap on total phase-2 rebuild rounds — aborts a "
                        "non-converging import loop (default: 30)")
    p.add_argument("--max-crash-relaunch", type=int, default=3,
                   help="consecutive fleet-crash relaunches before aborting "
                        "(default: 3)")
    p.add_argument("--scancel-timeout", type=int, default=180,
                   help="seconds to wait for scancel'd jobs to leave squeue "
                        "before relaunch (default: 180)")
    p.add_argument("--max-claims-per-batch", type=int, default=60,
                   help="cap on claims sent to one adjudication batch; the rest "
                        "stay pending for the next round (default: 60)")
    p.add_argument("--no-final-reverify", dest="final_reverify",
                   action="store_false", default=True,
                   help="skip the end-of-run re-verification of cached "
                        "SUCCESSes against the final heap (M3)")
    cfg = p.parse_args()

    if cfg.command == "run":
        (cmd_run_fleet if cfg.fleet else cmd_run)(cfg)
    elif cfg.command == "scan":
        cmd_scan(cfg)
    elif cfg.command == "report":
        cmd_report(cfg)
    elif cfg.command == "heap-dump":
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        refresh_heap_theories()


if __name__ == "__main__":
    main()
