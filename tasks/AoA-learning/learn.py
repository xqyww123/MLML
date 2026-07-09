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

Concurrency per server = the csv's `num-evaluator` (the AoA workload matches the
agent evaluators). Cache is bypassed on the ML side (AoA_use_proof_cache /
AoA_store_proof_cache both false), so reconstructed proofs never touch the shared
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
    tool_calls: int = 0
    tokens: Counter = field(default_factory=Counter)
    seconds: float = 0.0

    def __iadd__(self, o: "Stats") -> "Stats":
        self.goals += o.goals
        self.goals_finished += o.goals_finished
        self.created += o.created
        self.updated += o.updated
        self.rejected += o.rejected
        self.tool_calls += o.tool_calls
        self.tokens.update(o.tokens)
        return self

    def memory_str(self) -> str:
        """`+a,b ~c` — created are prefixed `+`, updated `~`. Empty when nothing
        was written, so a quiet goal stays a quiet log line."""
        bits = []
        if self.created:
            bits.append("+" + ",".join(self.created))
        if self.updated:
            bits.append("~" + ",".join(self.updated))
        if self.rejected:
            bits.append(f"{self.rejected} rejected")
        return " ".join(bits)


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
        return s
    path = os.path.join(log_dir, iid, "meta.jsonl.zst")
    if not os.path.exists(path):
        return s
    try:
        for o in _iter_meta(path):
            event = o.get("event")
            if event == "TOOL_CALL":
                s.tool_calls += 1
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
                return
            thy = Stats()         # this theory's own totals
            t_thy = time.monotonic()
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
                            # Skip a goal already learned (resume), or every goal in
                            # dry-run. A goal is keyed by "file:line" as sent by App.
                            do_run = (not args.dry_run) and (pos not in control_db)
                            logger.info("  [%s] goal %s -> %s", server, pos,
                                        "run" if do_run else "skip")
                            c.writer.write(mp.packb(bool(do_run)))
                            await c.writer.drain()
                            t_goal = time.monotonic()
                        case (1, pos, finished, iid):
                            # `iid` names this goal's AoA log dir; mine it for the
                            # experience memories written and the token cost.
                            g = goal_stats(args.log_dir, iid)
                            g.seconds = time.monotonic() - t_goal
                            g.goals_finished = 1 if finished else 0
                            # Accumulate per GOAL, not per theory: if this theory
                            # later crashes and is retried, its already-finished
                            # goals are skipped on the retry (control.db) and would
                            # otherwise never be counted anywhere.
                            thy += g
                            run += g
                            # Record ONLY finished goals, so a resume (which replays
                            # the theory from the start) retries goals AoA failed to
                            # reconstruct; the skip-check is presence-only.
                            if finished:
                                control_db[pos] = True
                                control_db.commit()
                            mem = g.memory_str()
                            logger.info(
                                "  [%s] goal %s: %s in %.0fs, %d tool calls%s",
                                server, pos,
                                "finished" if finished else "UNFINISHED",
                                g.seconds, g.tool_calls,
                                f", memory {mem}" if mem else "")
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

                # Do NOT mark the theory done in dry-run: every goal was answered
                # "skip", so persisting completion would make a later REAL run
                # (same control-db) skip the whole corpus and never invoke AoA.
                if not args.dry_run:
                    control_db[rpath] = True
                    control_db.commit()

            thy.seconds = time.monotonic() - t_thy
            logger.info("[%s] THEORY %s: %d/%d goals finished in %s; "
                        "memory +%d new ~%d updated (%d rejected); %s",
                        server, os.path.basename(rpath),
                        thy.goals_finished, thy.goals, fmt_hms(thy.seconds),
                        len(thy.created), len(thy.updated), thy.rejected,
                        fmt_tokens(thy.tokens))
            if thy.created or thy.updated:
                logger.info("[%s]   memories: %s", server, thy.memory_str())

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
                done = False
                requeue = False
                for attempt in range(3):
                    try:
                        await learn_one(server, target)
                        done = True
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
                if done:
                    finished_theories += 1
                    remaining -= 1
                    logger.info("[%d/%d theories] %d goals learned, "
                                "%d memories (+%d ~%d), elapsed %s",
                                finished_theories, total_theories,
                                run.goals_finished,
                                len(run.created) + len(run.updated),
                                len(run.created), len(run.updated),
                                fmt_hms(time.monotonic() - t_run))
                elif requeue:
                    task_queue.put_nowait(target)
                else:
                    remaining -= 1
                    given_up.append(os.path.abspath(target))
                    logger.error("[%s] giving up on %s after 3 attempts",
                                 server, target)

        await asyncio.gather(*(worker(s) for s in SERVER_INSTANCES))

    run.seconds = time.monotonic() - t_run
    logger.info("=" * 72)
    logger.info("ALL DONE in %s", fmt_hms(run.seconds))
    logger.info("  theories : %d/%d completed, %d given up",
                finished_theories, total_theories, len(given_up))
    logger.info("  goals    : %d/%d finished", run.goals_finished, run.goals)
    logger.info("  memory   : %d created, %d updated, %d dedup-rejected",
                len(run.created), len(run.updated), run.rejected)
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
    # The shared IsaMini.AoA RPC host is NOT started here — the operator runs it on
    # the login node and every fleet REPL points RPC_Host at it.
    await launch_servers()
    await learn(args)


if __name__ == "__main__":
    asyncio.run(main_async())
