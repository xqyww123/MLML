#!/usr/bin/env python3
"""Orchestrator (watcher) for the MathBench missing-lemma loop.

Runs PutnamBench cases one at a time through the AoA agent (DeepSeekV4.pro by
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

REPL_ADDR = "127.0.0.1:6666"
REPL_PORT = 6666
# Bind 0.0.0.0 so the evaluator reaches it via the configured hostname
# (config/evaluation_servers.csv uses `cslcw2u`, which resolves to 127.0.1.1 —
# a 127.0.0.1-bound socket would refuse it).
REPL_START_CMD = ("./contrib/Isa-REPL/repl_server.sh 0.0.0.0:6666 "
                  "MathBench_Prover /tmp/repl_outputs -o threads=10 -o document=false")
# Default address AoA's RPC layer connects to when the RPC_Host env var is
# unset (contrib/Isabelle_RPC/Tools/RPC.ML:74-75). The watcher OWNS this host:
# it pre-starts it with AOA_MISSING_LEMMA_SURVEY in its environment (用户方案
# 2026-06-11) so the lazy-spawn race ("whichever Isabelle process reconnects
# first donates its env") can never decide the survey switch.
RPC_HOST_ADDR = "127.0.0.1:27182"
SEMANTIC_COLLECT_CMD = ("./contrib/Semantic_Embedding/semantics_manage.py collect "
                        "MathBench_Prover.MathBench_Prover "
                        "--embed-models qwen3-embedding-8b --model claude-opus-4-8")
# Dump MathBench_Prover (covers MathBench_ProverBase + the source-loaded
# MathBench_Prover.thy layer) AND Minilang_Agent — facts living in the
# source-loaded layers must not be misjudged as missing imports.
HEAP_LIST_CMD = "isabelle build -n -l MathBench_Prover Minilang_Agent"

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
        # Collection records EVERYTHING as pending — duplicate detection is the
        # SEARCH AGENT's job (用户决定 2026-06-11): it sees the adjudicated
        # ledger digest in its prompt and returns verdict "duplicate" with a
        # duplicate_of reference; apply_verdicts() then inherits the prior
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

    def adjudicated_digest(self, limit: int = 300) -> list[dict]:
        """Compact view of previously adjudicated claims, handed to the search
        agent so it can flag duplicates instead of re-searching. Deduplicated
        by claim key (latest adjudication wins) so the cap packs distinct
        facts, not repetitions."""
        by_key: dict[str, dict] = {}
        for e in self.entries:
            if e["status"] in ("pending", "searching", "duplicate"):
                continue
            r = e["report"]
            by_key[e["key"]] = {
                "id": e["id"],
                "name": r.get("name_guess") or r.get("name") or "",
                "english": (r.get("english") or "")[:200],
                "status": e["status"],
                "theory": e["resolution"].get("theory"),
                "lemma_name": e["resolution"].get("lemma_name"),
            }
        return list(by_key.values())[-limit:]

    def pending(self) -> list[dict]:
        return [e for e in self.entries if e["status"] == "pending"]

    def by_id(self, eid: str) -> dict:
        return next(e for e in self.entries if e["id"] == eid)


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
    new_entries: list[dict] = []
    for f in sorted(log_dir.glob("*/missing_lemmas.yaml")):
        if ".old_" in f.parent.name:
            continue  # renamed stale invocation dirs — never re-ingest
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
            _ingest_doc(doc, ledger, case, f.parent.name, new_entries)
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
                              answer_tool=None) -> None:
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
    )

    # ClaudeSDKClient (not one-shot query()): permission/control answers
    # travel on the bidirectional control channel, which query() closes after
    # the prompt iterator is exhausted ("Stream closed").
    async def _drive() -> None:
        with open(transcript_path, "a", encoding="utf-8") as t:
            async with ClaudeSDKClient(options=options) as client:
                # Options-level "auto" silently degrades to default mode when
                # unavailable (leaving headless permission requests
                # unanswered) — set it explicitly so unavailability RAISES.
                await client.set_permission_mode("auto")
                await client.query(prompt)
                async for message in client.receive_response():
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

    if timeout is not None:
        await asyncio.wait_for(_drive(), timeout=timeout)
    else:
        await _drive()


def run_claude_agent(prompt: str, *, model: str | None,
                     transcript_path: Path,
                     timeout: float | None = None,
                     mission: str = "",
                     answer_tool=None) -> None:
    """Blocking wrapper (the watcher itself is synchronous)."""
    asyncio.run(_claude_agent_async(prompt, model=model,
                                    transcript_path=transcript_path,
                                    timeout=timeout, mission=mission,
                                    answer_tool=answer_tool))


_VERDICT_VALUES = ("missing_import", "already_in_heap", "not_found", "duplicate")


def _make_verdict_tool(claim_ids: list[str]):
    """In-process MCP tool the search agent MUST call to submit its verdicts
    (structured output as a forced tool call, not parsed from chat/file).
    Each item is validated; invalid items are rejected with an immediate error
    message so the agent corrects and resubmits. Returns (tool, holder) —
    accepted verdicts accumulate in *holder* keyed by claim_id."""
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
               "heap_rebuilt": {"type": "boolean"},
           },
           "required": ["imported", "failed", "heap_rebuilt"]})
    async def submit_result(args: dict):
        errors = []
        imported = args.get("imported")
        if not isinstance(imported, list) or any(
                not (isinstance(i, dict) and i.get("theory")) for i in imported):
            errors.append("`imported` must be an array of objects with `theory`")
        if not isinstance(args.get("failed"), list):
            errors.append("`failed` must be an array")
        if not isinstance(args.get("heap_rebuilt"), bool):
            errors.append("`heap_rebuilt` must be a boolean — report what "
                          "`isabelle build` actually did")
        if errors:
            return {"content": [{"type": "text", "text": "; ".join(errors)}],
                    "is_error": True}
        holder.clear()
        holder.update(args)
        return {"content": [{"type": "text",
                             "text": "Result recorded. You may stop."}]}

    return submit_result, holder


def start_search(cfg, ledger: 'Ledger', claims: list[dict]) \
        -> tuple[concurrent.futures.Future, Path, list[str], dict]:
    """Launch the confirmation-search agent for *claims* (non-blocking: runs
    in a worker thread so the evaluator keeps being polled meanwhile)."""
    for c in claims:
        c["status"] = "searching"
    out = STATE_DIR / "verdicts" / f"verdict_{claims[0]['id']}_{int(time.time())}.json"
    template = (PROMPT_DIR / "search_prompt.md").read_text(encoding="utf-8")
    payload = [{"claim_id": c["id"], **c["report"]} for c in claims]
    prompt = (template
              .replace("HEAP_THEORIES_FILE", str(STATE_DIR / "heap_theories.txt"))
              + "\n## Claims\n\n```json\n"
              + json.dumps(payload, indent=2, ensure_ascii=False) + "\n```\n")
    digest = ledger.adjudicated_digest()
    if digest:
        prompt += ("\n## Previously adjudicated claims (duplicate check)\n\n"
                   "```json\n"
                   + json.dumps(digest, indent=2, ensure_ascii=False)
                   + "\n```\n")
    log(f"search agent → {len(claims)} claim(s), verdicts at {out.name}")
    from permission_gate import SEARCH_MISSION
    answer_tool, holder = _make_verdict_tool([c["id"] for c in claims])
    fut = _AGENT_POOL.submit(
        run_claude_agent, prompt, model=cfg.search_model,
        transcript_path=out.with_suffix(".log"), timeout=cfg.search_timeout,
        mission=SEARCH_MISSION, answer_tool=answer_tool)
    return fut, out, [c["id"] for c in claims], holder


def finish_search(ledger: Ledger,
                  search: tuple[concurrent.futures.Future, Path, list[str], dict],
                  wait_timeout: float | None = None) -> list[str]:
    """Collect a finished (or awaited) search; returns confirmed theories."""
    fut, out, ids, holder = search
    try:
        fut.result(timeout=wait_timeout)
    except Exception as e:
        log(f"WARNING: search agent failed: {type(e).__name__}: {e}")
    # Persist whatever the answer tool accepted (audit trail), then adjudicate
    # from that same file. Claims the agent never answered fall back to
    # pending inside apply_verdicts.
    out.write_text(json.dumps({"verdicts": list(holder.values())},
                              indent=2, ensure_ascii=False), encoding="utf-8")
    return apply_verdicts(ledger, out, ids)


def apply_verdicts(ledger: Ledger, out: Path, claim_ids: list[str]) -> list[str]:
    """Read a verdict file; update the ledger. Returns confirmed-missing
    theories (deduped) needing phase 2."""
    theories: list[str] = []
    try:
        data = json.loads(out.read_text(encoding="utf-8"))
        verdicts = {v["claim_id"]: v for v in data.get("verdicts", [])}
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as e:
        log(f"WARNING: unreadable verdict file {out}: {e} — claims back to pending")
        verdicts = {}
    for cid in claim_ids:
        e = ledger.by_id(cid)
        v = verdicts.get(cid)
        if v is None:
            e["status"] = "pending"  # search agent skipped it — retry later
            continue
        verdict = v.get("verdict")
        if verdict == "duplicate" and v.get("duplicate_of"):
            # Same fact as a prior ledger entry (the search agent judged the
            # duplicate) — inherit that entry's adjudication. A duplicate of an
            # IMPORTED entry means "provided yet still unfindable": a
            # retrieval/visibility problem to surface, not an import gap.
            try:
                ref = ledger.by_id(v["duplicate_of"])
            except StopIteration:
                e["status"] = "pending"
                continue
            if ref["status"] == "imported":
                e["status"] = "provided_but_unfindable"
                e["resolution"] = dict(ref["resolution"], ref=ref["id"])
            elif ref["status"] in ("already_in_heap", "not_found",
                                   "import_failed", "provided_but_unfindable"):
                e["status"] = ref["status"]
                e["resolution"] = dict(ref["resolution"], ref=ref["id"])
            else:
                e["status"] = "duplicate"
                e["resolution"] = {"ref": ref["id"]}
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
    ledger.save()
    return theories


def run_phase2(cfg, ledger: Ledger, theories: list[str]) -> bool:
    """Import *theories* into MathBench (claude agent following the
    mathbench-import-reconcile skill), then restart the 6666 REPL and run the
    semantic collect. Returns True iff the heap was rebuilt."""
    stamp = int(time.time())
    out = STATE_DIR / "phase2" / f"phase2_{stamp}.json"
    template = (PROMPT_DIR / "phase2_prompt.md").read_text(encoding="utf-8")
    prompt = template.replace("THEORIES_PLACEHOLDER",
                              "\n".join(f"- {t}" for t in theories))
    log(f"PHASE 2: importing {theories}")
    if cfg.dry_run:
        log("dry-run: skipping phase 2")
        return False
    from permission_gate import PHASE2_MISSION
    answer_tool, holder = _make_result_tool()
    try:
        run_claude_agent(prompt, model=cfg.phase2_model,
                         transcript_path=out.with_suffix(".log"),
                         timeout=cfg.phase2_timeout,
                         mission=PHASE2_MISSION, answer_tool=answer_tool)
    except Exception as e:
        log(f"WARNING: phase-2 agent raised {type(e).__name__}: {e} — "
            f"judging by its submitted result anyway")
    # Persist the submitted result (audit trail).
    out.write_text(json.dumps(holder, indent=2, ensure_ascii=False),
                   encoding="utf-8")
    if not holder:
        log("ERROR: phase-2 agent never called submit_result; aborting phase 2")
        return False
    result = holder
    imported = {i["theory"] for i in result.get("imported", []) if i.get("theory")}
    failed = {i["theory"]: i.get("reason", "?") for i in result.get("failed", [])}
    if not result.get("heap_rebuilt") or not imported:
        log(f"phase 2 did not rebuild the heap (imported={imported}, failed={failed})")
        for e in ledger.entries:
            if e["status"] == "missing_import" and e["resolution"].get("theory") in failed:
                e["status"] = "import_failed"
                e["resolution"]["notes"] = failed[e["resolution"]["theory"]]
        ledger.save()
        return False

    # Deterministic tail: restart host+REPL (fresh heap, survey env verified),
    # then semantically collect the new theories so `query` can find them.
    # A collect failure must NOT crash the watcher with half-updated state:
    # the heap DID change, so the heap list is refreshed and entries are still
    # marked imported — flagged so the report surfaces the degraded indexing.
    restart_repl(cfg)
    log("semantic collect (this can take a while)…")
    collect_ok = True
    try:
        bash(SEMANTIC_COLLECT_CMD, check=True)
    except subprocess.CalledProcessError as e:
        collect_ok = False
        log(f"ERROR: semantic collect failed ({e}) — new lemmas will be "
            f"invisible to `query` until collected; flagged in the ledger")
    refresh_heap_theories()

    for e in ledger.entries:
        if e["status"] == "missing_import":
            th = e["resolution"].get("theory")
            if th in imported:
                e["status"] = "imported"
                e["resolution"]["imported_at"] = datetime.now().isoformat()
                if not collect_ok:
                    e["resolution"]["semantic_collect_failed"] = True
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
    return True


# ---------------------------------------------------------------------------
# REPL + heap helpers
# ---------------------------------------------------------------------------

def port_listening(port: int) -> bool:
    r = subprocess.run(["ss", "-tln"], capture_output=True, text=True)
    return bool(re.search(rf":{port}\b", r.stdout))


def kill_repl_and_host() -> None:
    """Stop the 6666 REPL server (LISTEN side only — not clients of the port)
    and the shared Isabelle_RPC_Host. WARNING: terminates every session other
    agents may have on them — by design the watcher owns both during a run."""
    global _RPC_HOST_PID
    subprocess.run(["bash", "-c",
                    f"lsof -ti tcp:{REPL_PORT} -s TCP:LISTEN | xargs -r kill"],
                   cwd=ROOT)
    subprocess.run(["pkill", "-f", "fork_and_launch__"])
    _RPC_HOST_PID = None
    time.sleep(3)


def start_rpc_host(cfg) -> int:
    """Pre-start the Isabelle_RPC_Host with AOA_MISSING_LEMMA_SURVEY in its
    environment (watcher owns the host — 用户方案 2026-06-11). Verifies via
    /proc/<pid>/environ that the variable actually reached the daemon, which
    is the deterministic replacement for the lazy-spawn env race."""
    global _RPC_HOST_PID
    env = dict(os.environ, AOA_MISSING_LEMMA_SURVEY=str(cfg.survey_interval))
    logp = STATE_DIR / "rpc_host.log"
    r = subprocess.run(
        [sys.executable, "-c",
         "import Isabelle_RPC_Host\nIsabelle_RPC_Host.fork_and_launch__()",
         RPC_HOST_ADDR, str(logp)],
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
            if RPC_HOST_ADDR.encode() in cmdline:
                pid = cand
                break
    if pid is None:
        raise RuntimeError(f"Isabelle_RPC_Host did not appear (see {logp})")
    want = f"AOA_MISSING_LEMMA_SURVEY={cfg.survey_interval}".encode()
    environ = Path(f"/proc/{pid}/environ").read_bytes()
    if want not in environ.split(b"\0"):
        raise RuntimeError(
            f"Isabelle_RPC_Host pid {pid} is running WITHOUT "
            f"AOA_MISSING_LEMMA_SURVEY={cfg.survey_interval} in its environment "
            f"— the survey channel is broken; refusing to continue")
    _RPC_HOST_PID = pid
    log(f"Isabelle_RPC_Host pid {pid} up with survey interval "
        f"{cfg.survey_interval} (verified via /proc)")
    return pid


def check_rpc_host_alive() -> None:
    """Fail loudly if the watcher-owned RPC host died (its env — and thus the
    survey switch — would be decided by whoever respawns it)."""
    if _RPC_HOST_PID is not None and not Path(f"/proc/{_RPC_HOST_PID}").exists():
        raise RuntimeError(
            f"watcher-owned Isabelle_RPC_Host (pid {_RPC_HOST_PID}) died — "
            f"aborting so a foreign respawn can't silently disable surveys")


def restart_repl(cfg) -> None:
    """Kill REPL + host, pre-start the host with the survey env (verified),
    then start the REPL server and wait until the port listens."""
    log("restarting Isabelle_RPC_Host + REPL on 6666")
    kill_repl_and_host()
    start_rpc_host(cfg)
    # The REPL also gets the env var: if the host ever dies and the REPL's
    # Isabelle respawns it lazily, the respawn inherits a CORRECT environment.
    env = dict(os.environ, AOA_MISSING_LEMMA_SURVEY=str(cfg.survey_interval))
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
        st["attempts"] += 1
        attempt = st["attempts"]
        force = attempt > 1 or st["rerun_owed"] or case_status(cfg, case) is not None
        st["rerun_owed"] = False
        cstate.save()
        log(f"=== {case} attempt {attempt}/{cfg.max_attempts} ===")
        proc = start_eval(cfg, case, force_retry=force)
        t_start = time.time()
        search: tuple[concurrent.futures.Future, Path, list[str], dict] | None = None
        phase2_theories: list[str] = []
        killed_for_phase2 = False
        try:
            while True:
                time.sleep(cfg.poll_interval)
                check_rpc_host_alive()
                scan_logs(log_dir, offsets, ledger, case)
                _save_json(STATE_DIR / "offsets.json", offsets)

                # Survey-channel canary (last line of defense behind the
                # /proc env check): a long-running first attempt that never
                # produced a single survey doc — not even an empty one —
                # means the channel is broken; abort rather than burn a
                # whole night collecting nothing.
                if (canary_armed and attempt == 1
                        and SCAN_STATS["missing_lemmas_docs"] == 0
                        and time.time() - t_start > cfg.canary_seconds):
                    raise RuntimeError(
                        f"survey canary: {cfg.canary_seconds}s into the first "
                        f"case and no MISSING_LEMMAS doc ever appeared — the "
                        f"AOA_MISSING_LEMMA_SURVEY channel looks broken")

                if search is not None and search[0].done():
                    phase2_theories += finish_search(ledger, search)
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
            scan_logs(log_dir, offsets, ledger, case)
            _save_json(STATE_DIR / "offsets.json", offsets)
            if search is not None:
                phase2_theories += finish_search(
                    ledger, search, wait_timeout=cfg.search_timeout)
            while ledger.pending() and not cfg.dry_run:
                s = start_search(cfg, ledger, ledger.pending())
                phase2_theories += finish_search(
                    ledger, s, wait_timeout=cfg.search_timeout)
        finally:
            kill_proc(proc)

        if phase2_theories:
            # Re-feed theories confirmed in earlier rounds but never imported
            # (e.g. a phase 2 that failed midway) so they don't linger.
            lingering = {e["resolution"]["theory"] for e in ledger.entries
                         if e["status"] == "missing_import"
                         and e["resolution"].get("theory")}
            phase2_theories = sorted(set(phase2_theories) | lingering)
            if st["attempts"] >= cfg.max_attempts:
                # 用户拍板 16a: a phase 2 on the last attempt would never be
                # followed by a re-run — record instead of spending hours.
                st["outcomes"].append(
                    f"attempt {attempt}: confirmed {phase2_theories} but "
                    f"attempt budget exhausted — recorded only")
                cstate.save()
                log(f"{case}: confirmed {phase2_theories} but attempt budget "
                    f"exhausted — skipping phase 2 (ledger keeps them)")
                if killed_for_phase2:
                    restart_repl(cfg)   # next case needs a live REPL
                return
            ok = run_phase2(cfg, ledger, phase2_theories)
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
        return
    log(f"{case}: attempt limit reached")


def cmd_run(cfg) -> None:
    for d in (STATE_DIR, STATE_DIR / "verdicts", STATE_DIR / "phase2"):
        d.mkdir(parents=True, exist_ok=True)
    Path(cfg.log_dir).mkdir(parents=True, exist_ok=True)
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
                raise
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
    p.add_argument("--driver", default="DeepSeekV4.pro")
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
    p.add_argument("--search-model", default="claude-opus-4-8",
                   help="model for the confirmation-search agent")
    p.add_argument("--phase2-model", default="claude-opus-4-8",
                   help="model for the phase-2 import/reconcile agent")
    p.add_argument("--search-timeout", type=int, default=1800)
    p.add_argument("--phase2-timeout", type=int, default=4 * 3600)
    p.add_argument("--repl-ready-timeout", type=int, default=1800)
    p.add_argument("--canary-seconds", type=int, default=1200,
                   help="abort if the first case runs this long without ANY "
                        "survey doc appearing (survey-channel canary)")
    p.add_argument("--no-restart-repl", action="store_true",
                   help="reuse the already-running REPL/host instead of the "
                        "default kill+restart (env then NOT guaranteed)")
    p.add_argument("--dry-run", action="store_true",
                   help="no claude calls, no phase 2 — just run + scan")
    cfg = p.parse_args()

    if cfg.command == "run":
        cmd_run(cfg)
    elif cfg.command == "scan":
        cmd_scan(cfg)
    elif cfg.command == "report":
        cmd_report(cfg)
    elif cfg.command == "heap-dump":
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        refresh_heap_theories()


if __name__ == "__main__":
    main()
