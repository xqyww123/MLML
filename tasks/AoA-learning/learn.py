#!/usr/bin/env python3
"""AoA-learning driver.

Runs, in one process:
  * an Isabelle_RPC host (provides the `IsaMini.AoA` RPC + all its callbacks — the
    AoA agent actually executes here), and
  * a REPL client that drives the `Minilang.AoA_Learning` App on an already-running
    Isa-REPL server (started separately, on the AoA_Learning_Base heap for the toy
    smoke test, or on the MathBench_Prover heap for the real corpus, and configured
    with RPC_Host = this host's address).

For each target theory the App replays it from source and, at every goal, calls back
into this host to run AoA with a LearningTask (goal + original Isar proof). Progress
is reported over a tiny tagged-tuple protocol (see learning.ML); `control.db` records
completed theories/goals so a re-run resumes instead of re-learning.

Cache is bypassed on the ML side (AoA_use_proof_cache / AoA_store_proof_cache both
false), so reconstructed proofs never touch the shared production cache. Experience
memories land directly in the shared Semantic_Embedding DB.
"""

import argparse
import asyncio
import logging
import os
import threading
import time

import msgpack as mp
from sqlitedict import SqliteDict

import Isabelle_RPC_Host
import Isabelle_RPC_Host.dialogue  # ensure Connection.dialogue exists before override
from Isabelle_RPC_Host.rpc import Connection as _Connection
import IsaMini.AoA  # noqa: F401 — registers the IsaMini.AoA handler + callbacks
from IsaREPL import Client, REPLFail

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger("aoa-learn")


def parse_args():
    p = argparse.ArgumentParser(description="AoA-learning driver")
    p.add_argument("--targets", default="targets",
                   help="Path to a targets file (one theory path per line), OR a "
                        "single .thy path. Default: ./targets")
    p.add_argument("--repl-addr", default="127.0.0.1:6666",
                   help="Isa-REPL server address (host:port)")
    p.add_argument("--rpc-addr", default="127.0.0.1:27183",
                   help="Address this process serves the IsaMini.AoA RPC host on. "
                        "Must match the target REPL server's RPC_Host.")
    p.add_argument("--driver", default="ClaudeCode",
                   help="AoA driver (default: ClaudeCode)")
    p.add_argument("--log-dir", default="",
                   help="AoA log directory (empty = no logging)")
    p.add_argument("--timeout-seconds", type=int, default=900,
                   help="Per-goal AoA wall-clock budget (default 900 = 15 min; the "
                        "App hard-kills at this + 300s). Much smaller than the AoA "
                        "default 14400 so a hard pilot goal cannot run for hours.")
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
    logger.info("targets: %d theories", len(targets))
    os.makedirs(os.path.dirname(args.control_db) or ".", exist_ok=True)
    total_goals = 0
    finished_goals = 0

    with SqliteDict(args.control_db) as control_db:
        async with Client(args.repl_addr, "HOL", timeout=None) as c:
            await c.set_register_thy(False)
            await c.set_trace(False)
            await c.load_theory([args.app_theory])

            for ti, target in enumerate(targets):
                rpath = os.path.abspath(target)
                if rpath in control_db:
                    logger.info("[%d/%d] skip (done): %s", ti + 1, len(targets), rpath)
                    continue
                logger.info("[%d/%d] learning: %s", ti + 1, len(targets), rpath)
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
                            logger.info("  goal opened %s -> %s", pos,
                                        "run" if run else "skip")
                            c.writer.write(mp.packb(bool(run)))
                            await c.writer.drain()
                        case (1, pos, finished):
                            total_goals += 1
                            if finished:
                                finished_goals += 1
                            control_db[pos] = bool(finished)
                            control_db.commit()
                            logger.info("  goal %s: %s (%d/%d finished)",
                                        pos, "finished" if finished else "unfinished",
                                        finished_goals, total_goals)
                        case (2, errs):
                            logger.error("  error(s): %s", "\n".join(errs))
                        case (9, diag):
                            logger.info("  [DIAG] %s", diag)
                        case 5:
                            break
                        case (None, err):
                            raise REPLFail(f"REPL failed on {rpath}: {err}")
                        case other:
                            raise REPLFail(f"unexpected message on {rpath}: {other!r}")

                control_db[rpath] = True
                control_db.commit()
                logger.info("[%d/%d] done: %s", ti + 1, len(targets), rpath)

    logger.info("ALL DONE: %d/%d goals finished across %d theories",
                finished_goals, total_goals, len(targets))


def main():
    args = parse_args()

    # Headless: auto-answer PIDE dialogues (e.g. Semantic_Embedding's
    # "N entities to embed. Proceed?" gate, which fires after a heap rebuild) with
    # their first option, so nothing blocks forever. Mirrors test_AoA.py.
    _rpc_logger = Isabelle_RPC_Host.mk_logger_(args.rpc_addr, None)

    async def _auto_dialogue(self, question: str, options: list) -> str:
        _rpc_logger.warning("[auto-dialogue] %r -> %r", question, options[0])
        return options[0]

    _Connection.dialogue = _auto_dialogue  # type: ignore[method-assign]

    def run_server():
        Isabelle_RPC_Host.launch_server_(args.rpc_addr, _rpc_logger, debugging=True)

    threading.Thread(target=run_server, daemon=True).start()
    time.sleep(1)
    asyncio.run(learn(args))


if __name__ == "__main__":
    main()
