#!/usr/bin/env python3
"""AoA-learning driver (parallel / fleet).

Mirrors tasks/extraction/theorem-relevance/premise-extraction.py: the target
theories are distributed, work-stealing, across a FLEET of Isa-REPL servers
(config/evaluation_servers.csv) that this script brings up via
`tools.server.launch_servers()` — under `CLUSTER=slurmx` onto slurm nodes, on the
`SESSION` heap (set `SESSION=MathBench_Prover` for the real corpus). Each REPL
server drives the `Minilang.AoA_Learning` App: for a target theory the App replays
it from source and, at every goal, runs AoA with a LearningTask (goal + original
Isar proof). Progress streams over a tiny tagged-tuple protocol (see learning.ML);
`control.db` records completed theories/goals so a re-run resumes.

The AoA agent itself executes in the SHARED `IsaMini.AoA` RPC host on the login
node, which is started SEPARATELY by the operator (NOT by this script); every fleet
REPL server must have `RPC_Host` pointing at it. This script owns only the REPL
fleet — exactly like premise-extraction, which likewise never starts an RPC host.
Since 0.4.0 the operator really must pre-launch it: a set `RPC_Host` is external-only,
so Isabelle never launches there and errors out if nothing is listening. (Leaving
`RPC_Host` unset is the other option — then each REPL gets its own ephemeral host,
bound to that REPL's lifetime, and no login-node host is involved.)

Concurrency per server = the csv's `num-evaluator` (the AoA workload matches the
agent evaluators). Cache is bypassed on the ML side (AoA_read_proof_store /
AoA_write_proof_store both false), so reconstructed proofs never touch the shared
production cache. Experience memories land directly in the shared Semantic_Embedding
DB.
"""

import argparse
import asyncio
import io
import json
import logging
import os
import re
import time
import traceback
from collections import Counter
from dataclasses import dataclass, field

import msgpack as mp
from sqlitedict import SqliteDict

from tools.server import SERVERS, launch_servers, test_server
from IsaREPL import Client, REPLFail

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger("aoa-learn")

# `write_memory`'s reply, as built by mcp_http_server._persist: "Saved" is a fresh
# key (a new experience, or an agent-confirmed non-duplicate); "Updated" overwrites
# an authorized same-name memory. Anything else is the dedup rejection
# ("**The memory was NOT written.** ..."), i.e. the write did not land.
_MEMORY_RE = re.compile(r"^(Saved|Updated) experience `([^`]+)`")

# A goal that keeps failing for a REAL reason (the agent ran but timed out, or an
# exception other than an infrastructure outage) is retried across resume passes up
# to this many times, then given up so a genuinely hard/broken goal cannot block its
# theory from ever completing. Infrastructure failures (RPC host unreachable) do NOT
# count — see the "infra" outcome in learn_one.
MAX_GOAL_ATTEMPTS = 3

# control.db value scheme (goal keys are "file:line", theory keys end ".thy"):
#   True        goal finished (terminal; also the legacy value written before this
#               scheme, read back correctly)
#   "skipped"   original proof unparsable (sorry/oops) — terminal, never retried
#   "givenup"   failed MAX_GOAL_ATTEMPTS times — terminal
#   int n       failed n (< MAX) real attempts so far — retried on the next pass
#   True (.thy) theory fully resolved (every goal terminal)


def _goal_terminal(v) -> bool:
    """A goal is terminal (skip it on this/next pass) iff finished, permanently
    skipped, or given up. Deliberately NOT a `v in (True, ...)` membership test:
    Python's `==` makes `1 == True`, so the int 1 — the value written after the
    FIRST real failure, which MUST be retried — would be misread as terminal and
    the goal permanently skipped. `is True` avoids that; ints fall through to
    non-terminal (retry)."""
    return v is True or v == "skipped" or v == "givenup"

# One work-stealing worker per (server x num-evaluator), exactly like
# premise-extraction (which uses num-translator) and evaluator.py (num-evaluator).
SERVER_INSTANCES = []
for _server, _data in SERVERS.items():
    SERVER_INSTANCES.extend([_server] * _data["num-evaluator"])


def parse_args():
    p = argparse.ArgumentParser(description="AoA-learning driver (parallel/fleet)")
    p.add_argument("--targets", default="targets",
                   help="Path to a targets file (one theory path per line), OR a "
                        "single .thy path. Default: ./targets")
    p.add_argument("--driver", default="ClaudeCode",
                   help="AoA driver (default: ClaudeCode)")
    p.add_argument("--log-dir", default="",
                   help="AoA log directory (empty = no logging)")
    p.add_argument("--timeout-seconds", type=int, default=900,
                   help="Per-goal AoA wall-clock budget (default 900 = 15 min; the "
                        "App hard-kills at this + 300s). Much smaller than the AoA "
                        "default 14400 so a hard goal cannot run for hours.")
    p.add_argument("--max-tool-calls", type=int, default=200,
                   help="Per-goal AoA tool-call budget (default 200)")
    p.add_argument("--max-retries", type=int, default=5,
                   help="Per-goal AoA max retries (default 5)")
    p.add_argument("--control-db", default="./cache/aoa_learning_control.db")
    p.add_argument("--dry-run", action="store_true",
                   help="Answer 'skip' to every goal: exercises the harness "
                        "(App/collector/protocol/replay) without running AoA (no LLM cost).")
    p.add_argument("--app-theory", default="AoA_Learning_Base.AoA_Learning_App",
                   help="Qualified name of the App theory to load from source")
    return p.parse_args()


def load_targets(spec: str) -> list[str]:
    if spec.endswith(".thy"):
        return [spec]
    out = []
    with open(spec, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                out.append(line)
    return out


@dataclass
class Stats:
    """What a run/theory/goal produced. Summable, so the same type serves all
    three reporting levels."""
    goals: int = 0
    goals_finished: int = 0
    created: list[str] = field(default_factory=list)   # names of NEW experiences
    updated: list[str] = field(default_factory=list)   # names of OVERWRITTEN ones
    rejected: int = 0                                  # dedup-rejected write attempts
    write_calls: int = 0                               # write_memory calls ATTEMPTED
    tool_calls: int = 0
    tokens: Counter = field(default_factory=Counter)
    seconds: float = 0.0
    # Goals whose AoA log could not be read. Tracked separately so "this goal
    # wrote no memory" is never confused with "we could not tell" — the two look
    # identical in the counters, and the second means the reporting is broken
    # (e.g. a stale RPC host that predates write_memory's response logging).
    no_log: int = 0

    def __iadd__(self, o: "Stats") -> "Stats":
        self.goals += o.goals
        self.goals_finished += o.goals_finished
        self.created += o.created
        self.updated += o.updated
        self.rejected += o.rejected
        self.write_calls += o.write_calls
        self.tool_calls += o.tool_calls
        self.tokens.update(o.tokens)
        self.no_log += o.no_log
        return self

    @property
    def unaccounted_writes(self) -> int:
        """`write_memory` calls whose outcome never reached the log. Nonzero means
        the AoA host predates the fix that logs write_memory's response, so its
        memories are invisible here — NOT that no memory was written."""
        return max(0, self.write_calls
                   - len(self.created) - len(self.updated) - self.rejected)

    def memory_str(self) -> str:
        """Plain-English summary of the experience memories this scope produced,
        e.g. `created: alpha, beta; updated: gamma; 1 rejected`."""
        bits = []
        if self.created:
            bits.append("created: " + ", ".join(self.created))
        if self.updated:
            bits.append("updated: " + ", ".join(self.updated))
        if self.rejected:
            bits.append(f"{self.rejected} rejected as duplicate")
        if self.unaccounted_writes:
            bits.append(f"{self.unaccounted_writes} UNACCOUNTED "
                        f"(stale AoA host: write_memory response not logged)")
        return "; ".join(bits)


def fmt_hms(seconds: float) -> str:
    s = int(seconds)
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m{s % 60:02d}s"
    return f"{s // 3600}h{(s % 3600) // 60:02d}m"


def fmt_tokens(t: Counter) -> str:
    def k(n):
        return f"{n / 1000:.1f}k" if n >= 1000 else str(n)
    return (f"tokens in {k(t['input_tokens'])} out {k(t['output_tokens'])} "
            f"cached {k(t['cached_tokens'])}")


def _iter_meta(path: str):
    """Yield the JSON records of one goal's meta.jsonl.zst.

    `Session._log_meta` flushes every record with FLUSH_FRAME, so the file is a
    sequence of complete zstd frames and a concurrently-written log always reads
    back cleanly up to the last flush. `read_across_frames` must be set: on the
    zstandard versions where it defaults to False, only the FIRST record would be
    returned — silently, which would look like a goal that did nothing."""
    import zstandard
    dctx = zstandard.ZstdDecompressor()
    with open(path, "rb") as fh:
        try:
            reader = dctx.stream_reader(fh, read_across_frames=True)
        except TypeError:                     # zstandard too old for the kwarg
            reader = dctx.stream_reader(fh)
        for line in io.TextIOWrapper(reader, encoding="utf-8", errors="replace"):
            line = line.strip()
            if line:
                try:
                    yield json.loads(line)
                except json.JSONDecodeError:  # torn final frame; nothing follows
                    return


def goal_stats(log_dir: str, iid: str) -> Stats:
    """Mine one goal's AoA log for what it produced. Best-effort: with
    `--log-dir ""` (logging off) or a missing/corrupt log this returns zeros and
    the goal is still counted — reporting must never take the run down."""
    s = Stats(goals=1)
    if not log_dir or not iid:
        s.no_log = 1
        return s
    path = os.path.join(log_dir, iid, "meta.jsonl.zst")
    if not os.path.exists(path):
        s.no_log = 1
        return s
    try:
        for o in _iter_meta(path):
            event = o.get("event")
            if event == "TOOL_CALL":
                s.tool_calls += 1
                if (o.get("tool_name") or "").endswith("write_memory"):
                    s.write_calls += 1
            elif event == "USAGE":
                for k in ("input_tokens", "output_tokens",
                          "cached_tokens", "cache_creation_tokens"):
                    s.tokens[k] += o.get(k, 0)
            elif (event == "TOOL_RESPONSE"
                  and (o.get("tool_name") or "").endswith("write_memory")):
                m = _MEMORY_RE.match(o.get("response") or "")
                if not m:
                    s.rejected += 1
                elif m.group(1) == "Saved":
                    s.created.append(m.group(2))
                else:
                    s.updated.append(m.group(2))
    except Exception as e:                     # noqa: BLE001 - reporting is advisory
        logger.warning("could not read AoA log %s: %s", path, e)
        s.no_log = 1
    return s


async def learn(args):
    targets = load_targets(args.targets)
    logger.info("targets: %d theories; fleet: %d workers over %d servers",
                len(targets), len(SERVER_INSTANCES), len(SERVERS))
    os.makedirs(os.path.dirname(args.control_db) or ".", exist_ok=True)

    total_theories = len(targets)
    finished_theories = 0
    run = Stats()                 # whole-run totals
    given_up = []                 # theories abandoned after 3 attempts
    t_run = time.monotonic()

    task_queue = asyncio.Queue()
    for target in targets:
        task_queue.put_nowait(target)
    remaining = total_theories

    with SqliteDict(args.control_db) as control_db:

        async def learn_one(server, target):
            # Fresh REPL session per theory (mirrors premise-extraction's
            # translate_one): a crashed theory can't poison the next one.
            nonlocal run
            rpath = os.path.abspath(target)
            if rpath in control_db:
                logger.info("[%d/%d] skip (done): %s",
                            finished_theories, total_theories, rpath)
                return True, False    # already resolved; no infra failure
            thy = Stats()         # this theory's own totals
            t_thy = time.monotonic()
            # A theory is resolved only when every goal it opens ends terminal. A goal
            # left non-terminal this pass — an infra failure, or a real failure still
            # under its retry cap — keeps the theory unresolved so the worker requeues
            # it; already-terminal goals are skipped on that pass, so no work repeats.
            theory_resolved = True
            infra_this_pass = 0
            async with Client(server, "HOL", timeout=None) as c:
                await c.set_register_thy(False)
                await c.set_trace(False)
                await c.load_theory([args.app_theory])
                await c.run_app("Minilang.AoA_Learning")
                # header: (driver, log_dir, path, (timeout_s, max_tool_calls, max_retries))
                c.writer.write(mp.packb((
                    args.driver, args.log_dir, rpath,
                    (args.timeout_seconds, args.max_tool_calls, args.max_retries))))
                await c.writer.drain()

                t_goal = time.monotonic()
                while True:
                    match await c._feed_and_unpack():
                        case (0, pos):
                            # Run this goal unless it is already terminal — finished on
                            # a prior pass, permanently skipped, or given up after the
                            # cap. A goal recorded as an int (failed < cap real times) is
                            # retried. Also skip everything in dry-run.
                            v = control_db.get(pos)
                            do_run = (not args.dry_run) and not _goal_terminal(v)
                            logger.info("  [%s] goal %s -> %s", server, pos,
                                        "run" if do_run else "skip")
                            c.writer.write(mp.packb(bool(do_run)))
                            await c.writer.drain()
                            t_goal = time.monotonic()
                        case (1, pos, outcome, iid):
                            # `iid` names this goal's AoA log dir; mine it for the
                            # experience memories written and the token cost.
                            # extraction_skipped carries iid="" — no agent ran, so
                            # there is no log to read and nothing to attribute; build
                            # empty stats directly rather than letting goal_stats flag
                            # a (nonexistent) missing log as no_log, which would fire a
                            # spurious "broken pipeline" warning for every sorry/oops goal.
                            g = (Stats(goals=1) if outcome == "extraction_skipped"
                                 else goal_stats(args.log_dir, iid))
                            g.seconds = time.monotonic() - t_goal
                            finished = outcome == "finished"
                            g.goals_finished = 1 if finished else 0
                            # Accumulate per GOAL, not per theory: if this theory
                            # later crashes and is retried, its already-finished
                            # goals are skipped on the retry (control.db) and would
                            # otherwise never be counted anywhere.
                            thy += g
                            run += g

                            if finished:
                                control_db[pos] = True
                                control_db.commit()
                                status = "finished"
                            elif outcome == "extraction_skipped":
                                # sorry/oops proof — nothing to learn; terminal.
                                control_db[pos] = "skipped"
                                control_db.commit()
                                status = "skipped (no parsable proof)"
                            elif outcome == "infra":
                                # The agent never ran (RPC host unreachable). Do NOT
                                # count it: leave the goal untouched and keep the theory
                                # unresolved so it is retried once infra is back.
                                infra_this_pass += 1
                                theory_resolved = False
                                status = "INFRA — will retry (not counted)"
                            else:
                                # "timeout" / "error": a real failed attempt. Count it,
                                # and give up once it has failed MAX_GOAL_ATTEMPTS times
                                # so a hard/broken goal cannot block its theory forever.
                                v = control_db.get(pos)
                                n = (v if isinstance(v, int) else 0) + 1
                                if n >= MAX_GOAL_ATTEMPTS:
                                    control_db[pos] = "givenup"
                                    control_db.commit()
                                    status = f"GAVE UP after {n} attempts ({outcome})"
                                else:
                                    control_db[pos] = n
                                    control_db.commit()
                                    theory_resolved = False
                                    status = f"{outcome}, attempt {n}/{MAX_GOAL_ATTEMPTS}"

                            # Always print the memory field, even when empty: most goals
                            # teach the agent nothing worth saving, and an omitted field
                            # is indistinguishable from broken reporting.
                            logger.info(
                                "  [%s] goal %s: %s in %.0fs, %d tool calls, "
                                "memory %s [run total: %d created, %d updated]",
                                server, pos, status, g.seconds, g.tool_calls,
                                "n/a (no AoA log)" if g.no_log
                                else (g.memory_str() or "none"),
                                len(run.created), len(run.updated))
                        case (2, errs):
                            logger.error("  [%s] error(s): %s", server, "\n".join(errs))
                        case (9, diag):
                            logger.info("  [%s] [DIAG] %s", server, diag)
                        case 5:
                            break
                        case (None, err):
                            raise REPLFail(f"REPL failed on {rpath}: {err}")
                        case other:
                            raise REPLFail(f"unexpected message on {rpath}: {other!r}")

                # Mark the theory done ONLY when every goal reached a terminal state.
                # An unresolved theory (an infra failure, or a goal still under its
                # retry cap) is left unmarked so the worker requeues it for another
                # pass. Never in dry-run: every goal was answered "skip", so persisting
                # completion would make a later REAL run skip the whole corpus.
                if not args.dry_run and theory_resolved:
                    control_db[rpath] = True
                    control_db.commit()

            thy.seconds = time.monotonic() - t_thy
            logger.info("[%s] THEORY %s: %s (%d/%d goals finished) in %s; "
                        "memory: %d created, %d updated, %d rejected%s; %s",
                        server, os.path.basename(rpath),
                        "RESOLVED" if theory_resolved
                        else f"unresolved, requeue ({infra_this_pass} infra)",
                        thy.goals_finished, thy.goals, fmt_hms(thy.seconds),
                        len(thy.created), len(thy.updated), thy.rejected,
                        f", {thy.no_log} goals unreadable" if thy.no_log else "",
                        fmt_tokens(thy.tokens))
            if thy.created or thy.updated:
                logger.info("[%s]   memories: %s", server, thy.memory_str())
            return theory_resolved, infra_this_pass > 0

        async def worker(server):
            nonlocal finished_theories, remaining
            while True:
                if not await test_server(server):
                    logger.error("[%s] server down, waiting...", server)
                    await asyncio.sleep(60)
                    continue
                try:
                    target = task_queue.get_nowait()
                except asyncio.QueueEmpty:
                    if remaining == 0:
                        break
                    await asyncio.sleep(30)
                    continue

                # ConnectionError == the SERVER is the problem: requeue the theory
                # for another worker/server (remaining unchanged, so the run keeps
                # waiting for it). Any other error is theory-level: retry a few
                # times on this server, then GIVE UP on it for this run so the fleet
                # can terminate — it stays unmarked in control.db, so a resume run
                # retries it fresh.
                result = None          # (resolved, infra) once a pass completes
                requeue = False
                for attempt in range(3):
                    try:
                        result = await learn_one(server, target)
                        break
                    except ConnectionError:
                        logger.error("[%s] connection error on %s; requeueing",
                                     server, target)
                        requeue = True
                        break
                    except Exception as e:
                        traceback.print_exc()
                        logger.error("[%s] error on %s (attempt %d/3): %s",
                                     server, target, attempt + 1, e)

                if result is not None:
                    resolved, infra = result
                    if resolved:
                        finished_theories += 1
                        remaining -= 1
                        logger.info("[%d/%d theories] %d goals learned, "
                                    "%d memories (%d created, %d updated), elapsed %s",
                                    finished_theories, total_theories,
                                    run.goals_finished,
                                    len(run.created) + len(run.updated),
                                    len(run.created), len(run.updated),
                                    fmt_hms(time.monotonic() - t_run))
                    else:
                        # Not every goal reached a terminal state this pass (an infra
                        # outage, or goals still under their retry cap). Requeue for
                        # another pass; `remaining` stays put so the run keeps waiting.
                        # Back off first on an infra outage so the fleet does not spin
                        # hammering a down RPC host.
                        task_queue.put_nowait(target)
                        if infra:
                            await asyncio.sleep(60)
                elif requeue:
                    task_queue.put_nowait(target)
                else:
                    remaining -= 1
                    given_up.append(os.path.abspath(target))
                    logger.error("[%s] giving up on %s after 3 attempts",
                                 server, target)

        await asyncio.gather(*(worker(s) for s in SERVER_INSTANCES))

        # Terminal goal tallies straight from control.db (authoritative across
        # resumes, unlike the in-memory `run` which only covers this session's passes).
        gv = sum(1 for k, v in control_db.items()
                 if not k.endswith(".thy") and v == "givenup")
        sk = sum(1 for k, v in control_db.items()
                 if not k.endswith(".thy") and v == "skipped")
        fin = sum(1 for k, v in control_db.items()
                  if not k.endswith(".thy") and v is True)

    run.seconds = time.monotonic() - t_run
    logger.info("=" * 72)
    logger.info("ALL DONE in %s", fmt_hms(run.seconds))
    logger.info("  theories : %d/%d completed, %d given up",
                finished_theories, total_theories, len(given_up))
    logger.info("  goals    : this run %d/%d finished; control.db totals: "
                "%d finished, %d gave up, %d skipped (unparsable proof)",
                run.goals_finished, run.goals, fin, gv, sk)
    logger.info("  memory   : %d created, %d updated, %d dedup-rejected",
                len(run.created), len(run.updated), run.rejected)
    # Zero memories across a whole run is normal (most goals teach nothing worth
    # saving); zero memories because the logs were unreadable, or because the AoA
    # host never recorded write_memory's outcome, is a broken pipeline. Never let
    # the two look alike.
    if run.no_log:
        logger.warning("  %d/%d goals had no readable AoA log — their memory "
                       "counts are MISSING, not zero", run.no_log, run.goals)
    if run.unaccounted_writes:
        logger.warning("  %d write_memory calls have no logged outcome — the AoA "
                       "host predates the response-logging fix; restart it",
                       run.unaccounted_writes)
    logger.info("  AoA      : %d tool calls, %s",
                run.tool_calls, fmt_tokens(run.tokens))
    # Names, not just counts: this is the run's actual product, and a duplicate
    # name across theories means the same lesson was re-learned (or overwritten).
    for verb, names in (("created", run.created), ("updated", run.updated)):
        for name, n in Counter(names).most_common():
            logger.info("    %s %s%s", verb, name, f" (x{n})" if n > 1 else "")
    for t in given_up:
        logger.info("    given up: %s", t)
    logger.info("=" * 72)


async def main_async():
    args = parse_args()
    # Bring up the REPL fleet (CLUSTER=slurmx -> slurm nodes on the SESSION heap).
    # The shared IsaMini.AoA RPC host is NOT started here — the operator pre-launches
    # it on the login node and every fleet REPL points RPC_Host at it.
    await launch_servers()
    await learn(args)


if __name__ == "__main__":
    asyncio.run(main_async())
