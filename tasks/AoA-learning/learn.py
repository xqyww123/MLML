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
import logging
import os
import traceback

import msgpack as mp
from sqlitedict import SqliteDict

from tools.server import SERVERS, launch_servers, test_server
from IsaREPL import Client, REPLFail

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger("aoa-learn")

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


async def learn(args):
    targets = load_targets(args.targets)
    logger.info("targets: %d theories; fleet: %d workers over %d servers",
                len(targets), len(SERVER_INSTANCES), len(SERVERS))
    os.makedirs(os.path.dirname(args.control_db) or ".", exist_ok=True)

    total_theories = len(targets)
    finished_theories = 0
    total_goals = 0
    finished_goals = 0

    task_queue = asyncio.Queue()
    for target in targets:
        task_queue.put_nowait(target)
    remaining = total_theories

    with SqliteDict(args.control_db) as control_db:

        async def learn_one(server, target):
            # Fresh REPL session per theory (mirrors premise-extraction's
            # translate_one): a crashed theory can't poison the next one.
            nonlocal total_goals, finished_goals
            rpath = os.path.abspath(target)
            if rpath in control_db:
                logger.info("[%d/%d] skip (done): %s",
                            finished_theories, total_theories, rpath)
                return
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

                while True:
                    match await c._feed_and_unpack():
                        case (0, pos):
                            # Skip a goal already learned (resume), or every goal in
                            # dry-run. A goal is keyed by "file:line" as sent by App.
                            run = (not args.dry_run) and (pos not in control_db)
                            logger.info("  [%s] goal %s -> %s", server, pos,
                                        "run" if run else "skip")
                            c.writer.write(mp.packb(bool(run)))
                            await c.writer.drain()
                        case (1, pos, finished):
                            total_goals += 1
                            # Record ONLY finished goals, so a resume (which replays
                            # the theory from the start) retries goals AoA failed to
                            # reconstruct; the skip-check is presence-only.
                            if finished:
                                finished_goals += 1
                                control_db[pos] = True
                                control_db.commit()
                            logger.info("  [%s] goal %s: %s (%d/%d finished)",
                                        server, pos,
                                        "finished" if finished else "unfinished",
                                        finished_goals, total_goals)
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
                    logger.info("[%d/%d] done: %s", finished_theories,
                                total_theories, os.path.abspath(target))
                elif requeue:
                    task_queue.put_nowait(target)
                else:
                    remaining -= 1
                    logger.error("[%s] giving up on %s after 3 attempts",
                                 server, target)

        await asyncio.gather(*(worker(s) for s in SERVER_INSTANCES))

    logger.info("ALL DONE: %d/%d goals finished across %d/%d theories",
                finished_goals, total_goals, finished_theories, total_theories)


async def main_async():
    args = parse_args()
    # Bring up the REPL fleet (CLUSTER=slurmx -> slurm nodes on the SESSION heap).
    # The shared IsaMini.AoA RPC host is NOT started here — the operator runs it on
    # the login node and every fleet REPL points RPC_Host at it.
    await launch_servers()
    await learn(args)


if __name__ == "__main__":
    asyncio.run(main_async())
