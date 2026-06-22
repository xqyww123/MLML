#!/usr/bin/env python3
"""Run the AoA agent over PutnamBench against a single, externally-managed REPL.

This is a thin, resumable wrapper around ``evaluation.evaluate_and_save`` that
deliberately bypasses ``tools.server.launch_servers`` (which would ssh-launch
REPLs from ``config/evaluation_servers.csv``). Instead it points the evaluator
at the one REPL that ``start_servers.sh`` brought up (127.0.0.1:6699), so the
whole run is single-REPL / serial and its logs stay clean.

Equivalent in spirit to::

    evaluation/evaluator_top.py agent-putnam DeepSeekV4.pro --result DB --case-category test

but with an explicit ``server_instances`` list and no CSV / ssh dependency.

Resumable: ``--result`` is a SqliteDict; SUCCESS and (unless ``--retry-failure``)
FAIL cases already in it are skipped, so re-running continues where it left off.
"""
import argparse
import asyncio
import logging
import os
import sys

from evaluation import Case, evaluate_and_save, MinilangAgent_PutnamBench, pick_putnam_cls
from data.isabelle import PutnamBench_Data

logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO,
                    format='%(asctime)s - %(levelname)s - %(message)s',
                    handlers=[logging.StreamHandler()])


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--result", "-o", required=True,
                   help="SqliteDict result DB (resumes if it exists)")
    p.add_argument("--log-dir", required=True,
                   help="Directory for per-invocation agent logs (interaction.yaml etc.)")
    p.add_argument("--repl-addr", default="127.0.0.1:6699",
                   help="Address of the externally-managed REPL (default: 127.0.0.1:6699)")
    p.add_argument("--driver", default="DeepSeekV4.pro",
                   help="AoA driver string (default: DeepSeekV4.pro)")
    p.add_argument("--cases-file",
                   help="Optional file of case names (one per line) to restrict the run")
    p.add_argument("--limit", type=int, default=None,
                   help="Optional: only the first N cases (smoke runs)")
    p.add_argument("--pass", type=int, dest="pass_num", default=1,
                   help="pass@N independent attempts per case (default: 1)")
    p.add_argument("--timeout-seconds", type=int, default=14400,
                   help="Per-case wall-clock budget in seconds (default: 14400 = 4h)")
    p.add_argument("--max-tool-calls", type=int, default=10000)
    p.add_argument("--max-retries", type=int, default=8)
    p.add_argument("--retry-failure", action="store_true", default=False,
                   help="Re-run cases that previously FAILED (default: skip them)")
    args = p.parse_args()

    data = PutnamBench_Data()
    if args.cases_file:
        with open(args.cases_file, encoding="utf-8") as f:
            names = [ln.strip() for ln in f if ln.strip()]
    else:
        names = list(data.cases_of("test"))
    if args.limit is not None:
        names = names[:args.limit]
    if not names:
        logger.error("No cases to evaluate")
        sys.exit(1)

    cases = [Case(name, [args.driver] * args.pass_num) for name in names]
    os.makedirs(args.log_dir, exist_ok=True)
    logger.info(f"Evaluating {len(cases)} PutnamBench cases with driver "
                f"{args.driver} via REPL {args.repl_addr}; logs -> {args.log_dir}")

    def make_evaluator(addr):
        return pick_putnam_cls(MinilangAgent_PutnamBench)(
            addr,
            timeout_seconds=args.timeout_seconds,
            max_tool_calls=args.max_tool_calls,
            max_retries=args.max_retries,
            log_dir=args.log_dir,
        )

    async def _run():
        await evaluate_and_save(
            args.result, cases, make_evaluator,
            retry_failure=args.retry_failure,
            server_instances=[args.repl_addr],
        )

    asyncio.run(_run())


if __name__ == "__main__":
    main()
