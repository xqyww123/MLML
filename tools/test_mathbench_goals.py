#!/usr/bin/env python3
"""
Test that adding MathBench_Prover as a lib does not alter proof goal terms
in PutnamBench problems.

For each problem in putnamBench.json, compares the sexpr-serialized goal terms
(fully qualified, structural) with and without
add_lib(['MathBench_Prover.MathBench_Prover']).

Requires: an Isa-REPL server on MathBench_Prover session.
  ./contrib/Isa-REPL/repl_server.sh <addr> MathBench_Prover /tmp/repl_outputs

Usage:
    python -m tools.test_mathbench_goals [--addr HOST:PORT] [--limit N] [--start KEY]
"""

import asyncio
import json
import re
import sys
import os
import argparse

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from IsaREPL import Client, REPLFail

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_PATH = os.path.join(PROJECT_ROOT, "data", "putnamBench.json")


def load_problems():
    with open(DATA_PATH, "r") as f:
        return json.load(f)


# Per-phase suffixes appended to each theory name to dodge Isabelle's theory
# cache collisions between the two phases.
PHASE_BARE = "bare"
PHASE_WITHLIB = "withlib"


def rename_theory(src: str, suffix: str) -> str:
    """Append suffix to the theory name to avoid Isabelle's theory cache collisions."""
    return re.sub(r'^(theory\s+)(\S+)', rf'\1\2_{suffix}', src, count=1)


def strip_theory_suffix(goals, key: str, suffix: str):
    """Undo the rename_theory artifact in serialized goal terms.

    The per-phase theory suffix leaks into the qualifier of a problem's own
    local definitions (e.g. ``{key}_bare.foo`` vs ``{key}_withlib.foo``), which
    otherwise makes two semantically identical goals compare unequal. Normalize
    ``{key}_{suffix}.`` back to ``{key}.`` so the two phases are comparable."""
    if not isinstance(goals, list):
        return goals
    needle, repl = f"{key}_{suffix}.", f"{key}."
    return [g.replace(needle, repl) if isinstance(g, str) else g for g in goals]


async def get_goals(repl: Client, src: str, timeout=120000):
    """Eval theory source and return (status, goals) where goals is the sexpr list.

    Theory-level errors (undefined constant, ambiguous/failed parse, ...) do NOT
    raise — they come back in CommandOutput.errors. We must inspect them, else a
    statement that fails to elaborate under the lib would be silently reported as
    a clean goal state (a false pass for the authoritative gate)."""
    try:
        outs = await repl.eval(src, timeout=timeout)
    except REPLFail as e:
        return ("eval_error", str(e))
    except TimeoutError as e:
        return ("timeout", str(e))
    errs = [e for cmd in (outs or []) for e in cmd.errors]
    if errs:
        return ("eval_error", '; '.join(errs))
    try:
        raw = await repl.context('sexpr')
        parsed = Client.parse_ctxt(raw)
        return ("ok", parsed['goals'])
    except Exception as e:
        return ("context_error", str(e))


_FLAKE_MARKERS = ("reset by peer", "Broken pipe", "EPIPE", "ECONNRESET",
                  "Connection reset", "Connection refused")


def is_flake(status, data) -> bool:
    """A socket/transport error from the REPL — an infrastructure hiccup, not a
    real divergence. Such results must be retried, never trusted."""
    return status != "ok" and any(m in str(data) for m in _FLAKE_MARKERS)


async def recollect(addr: str, problems: dict, keys: list, suffix: str, lib):
    """Re-evaluate a small set of keys on a fresh connection (for retrying flakes)."""
    out = {}
    repl = Client(addr, 'HOL', timeout=300)
    async with repl:
        await repl.record_state("init")
        if lib:
            await repl.add_lib([lib])
        for k in keys:
            await repl.rollback("init")
            out[k] = await get_goals(repl, rename_theory(problems[k], suffix))
    return out


async def collect_goals(repl: Client, problems: dict, keys: list[str], phase_suffix: str):
    """Iterate over all keys, rollback + eval + context each time."""
    results = {}
    for i, key in enumerate(keys):
        await repl.rollback("init")
        src = rename_theory(problems[key], phase_suffix)
        status, data = await get_goals(repl, src)
        results[key] = (status, data)
        if status != "ok":
            print(f"  [{i+1}/{len(keys)}] {key}: {status}: {str(data)[:120]}")
        elif (i + 1) % 50 == 0:
            print(f"  [{i+1}/{len(keys)}] processed...")
    return results


async def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--addr", type=str, default="127.0.0.1:7777",
                        help="REPL server address (default: 127.0.0.1:7777, the pipeline's dedicated port)")
    parser.add_argument("--limit", type=int, default=0,
                        help="Limit number of problems (0 = all)")
    parser.add_argument("--start", type=str, default="",
                        help="Start from this key (inclusive, lexicographic)")
    parser.add_argument("--lib", type=str, default="MathBench_Prover.MathBench_Prover",
                        help="Fully-qualified lib to test (default: MathBench_Prover.MathBench_Prover)")
    parser.add_argument("--retries", type=int, default=2,
                        help="rounds of retrying socket-flaky results on fresh connections")
    args = parser.parse_args()

    problems = load_problems()
    keys = sorted(problems.keys())

    if args.start:
        idx = next((i for i, k in enumerate(keys) if k >= args.start), 0)
        keys = keys[idx:]
    if args.limit > 0:
        keys = keys[:args.limit]

    print(f"Testing {len(keys)} problems against lib {args.lib}")
    print(f"REPL server: {args.addr}")

    # Phase 1: without the lib
    print(f"\n=== Phase 1: WITHOUT {args.lib} ({len(keys)} problems) ===")
    repl_bare = Client(args.addr, 'HOL', timeout=300)
    async with repl_bare:
        await repl_bare.record_state("init")
        goals_without = await collect_goals(repl_bare, problems, keys, PHASE_BARE)
    print(f"  Phase 1 complete.")

    # Phase 2: with the lib
    print(f"\n=== Phase 2: WITH {args.lib} ({len(keys)} problems) ===")
    repl_lib = Client(args.addr, 'HOL', timeout=300)
    async with repl_lib:
        await repl_lib.record_state("init")
        await repl_lib.add_lib([args.lib])
        goals_with = await collect_goals(repl_lib, problems, keys, PHASE_WITHLIB)
    print(f"  Phase 2 complete.")

    # Retry socket-flaky results on fresh connections — these are REPL transport
    # hiccups (broken pipe / connection reset), not real divergences.
    for attempt in range(args.retries):
        flaky = [k for k in keys
                 if is_flake(*goals_without[k]) or is_flake(*goals_with[k])]
        if not flaky:
            break
        print(f"\n=== Retry {attempt + 1}: {len(flaky)} flaky key(s) ===")
        goals_without.update(await recollect(args.addr, problems, flaky, PHASE_BARE, None))
        goals_with.update(await recollect(args.addr, problems, flaky, PHASE_WITHLIB, args.lib))

    # Phase 3: compare
    match_count = 0
    mismatch_count = 0
    skip_count = 0
    mismatches = []
    new_errors = []

    for key in keys:
        s1, d1 = goals_without[key]
        s2, d2 = goals_with[key]

        if s1 != "ok" and s2 != "ok":
            skip_count += 1
            continue
        if s1 == "ok" and s2 != "ok":
            new_errors.append((key, f"was ok without lib, now {s2}: {str(d2)[:200]}"))
            continue
        if s1 != "ok" and s2 == "ok":
            new_errors.append((key, f"was {s1} without lib, now ok with lib"))
            continue
        # Normalize away the per-phase theory-rename suffix before comparing,
        # otherwise a problem's local definitions diff only by qualifier.
        n1 = strip_theory_suffix(d1, key, PHASE_BARE)
        n2 = strip_theory_suffix(d2, key, PHASE_WITHLIB)
        if n1 == n2:
            match_count += 1
        else:
            mismatch_count += 1
            mismatches.append((key, n1, n2))

    # Report
    print(f"\n{'='*60}")
    print(f"  Total:      {len(keys)}")
    print(f"  Match:      {match_count}")
    print(f"  Mismatch:   {mismatch_count}")
    print(f"  Skipped:    {skip_count}  (eval errors in both phases)")
    print(f"  New errors: {len(new_errors)}  (status changed between phases)")
    print(f"{'='*60}")

    if mismatches:
        print(f"\n=== Mismatched goals ({len(mismatches)}) ===")
        for key, d1, d2 in mismatches:
            print(f"\n--- {key} ---")
            for i, (g1, g2) in enumerate(zip(d1, d2)):
                if g1 != g2:
                    print(f"  goal {i+1} differs:")
                    print(f"    WITHOUT: {g1[:400]}")
                    print(f"    WITH:    {g2[:400]}")

    if new_errors:
        print(f"\n=== Eval-status changes ({len(new_errors)}) ===")
        for key, msg in new_errors:
            print(f"  {key}: {msg}")

    # Persist full results
    output = {
        "summary": {
            "total": len(keys),
            "match": match_count,
            "mismatch": mismatch_count,
            "skip": skip_count,
            "new_errors": len(new_errors),
        },
        "mismatches": {k: {"without": d1, "with": d2} for k, d1, d2 in mismatches},
        "new_errors": {k: msg for k, msg in new_errors},
    }
    out_path = os.path.join(PROJECT_ROOT, "mathbench_goal_comparison.json")
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nFull results saved to {out_path}")

    if mismatch_count > 0 or len(new_errors) > 0:
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
