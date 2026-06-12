#!/usr/bin/env python3
"""Build per-problem audit packets for the PutnamBench formalization audit
(用户提案 2026-06-12: desugar first, then per-problem agent review).

For every problem in data/putnamBench.json, evaluates the theory as written
(its own native imports) on the dedicated 7777 REPL and captures the goal
terms in TWO forms: pretty (readable, sugar-laden) and sexpr (fully
desugared: qualified constants, explicit types — the ground truth of what
the statement actually says). Reuses the goal-gate machinery
(tools.test_mathbench_goals.get_goals / Client).

Each packet (putnam_audit/packets/<name>.json):
  problem_name, informal_statement, informal_solution, tags   (PutnamBench)
  theory_src                                  (formalization incl. solution)
  goals_pretty[], goals_sexpr[]               (desugared statement)
  const_inventory[]                           (qualified names in the sexpr)
"""
import asyncio
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'contrib' / 'Isa-REPL'))

from tools.test_mathbench_goals import (get_goals, rename_theory,
                                        load_problems, is_flake)
from IsaREPL.IsaREPL import Client

ADDR = '127.0.0.1:7777'
OUT = ROOT / 'putnam_audit' / 'packets'
INFORMAL = ROOT / 'data' / 'PutnamBench' / 'informal' / 'putnam.json'

_QUALIFIED = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+")


def const_inventory(sexprs: list[str]) -> list[str]:
    names: set[str] = set()
    for s in sexprs:
        names.update(_QUALIFIED.findall(s))
    return sorted(names)


async def grab(repl: Client, src: str):
    """Eval + capture both pretty and sexpr goals (context() is stateless)."""
    status, sexpr_goals = await get_goals(repl, src)
    if status != 'ok':
        return status, None, None
    pretty = Client.parse_ctxt(await repl.context('pretty'))['goals']
    return 'ok', pretty, sexpr_goals


async def sweep(problems: dict, keys: list[str], suffix: str) -> dict:
    out = {}
    repl = Client(ADDR, 'HOL', timeout=300)
    async with repl:
        await repl.record_state('init')
        for i, k in enumerate(keys):
            await repl.rollback('init')
            out[k] = await grab(repl, rename_theory(problems[k], suffix))
            if out[k][0] != 'ok':
                print(f'  [{i+1}/{len(keys)}] {k}: {out[k][0]}')
            elif (i + 1) % 50 == 0:
                print(f'  [{i+1}/{len(keys)}] ...')
    return out


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    problems = load_problems()
    informal = {e['problem_name']: e
                for e in json.loads(INFORMAL.read_text(encoding='utf-8'))}
    keys = sorted(problems)
    missing_informal = [k for k in keys if k not in informal]
    if missing_informal:
        print(f'WARNING: {len(missing_informal)} problems lack informal '
              f'statements: {missing_informal[:5]} ...')
    print(f'sweeping {len(keys)} problems on {ADDR}')
    results = asyncio.run(sweep(problems, keys, '_audit'))

    # one retry round on a fresh connection for flaky/failed ones
    bad = [k for k in keys if results[k][0] != 'ok']
    if bad:
        print(f'retrying {len(bad)} failed problem(s) on a fresh connection')
        results.update(asyncio.run(sweep(problems, bad, '_audit_r2')))

    n_ok = 0
    for k in keys:
        status, pretty, sexprs = results[k]
        info = informal.get(k, {})
        packet = {
            'problem_name': k,
            'informal_statement': info.get('informal_statement'),
            'informal_solution': info.get('informal_solution'),
            'tags': info.get('tags', []),
            'theory_src': problems[k],
            'eval_status': status,
            'goals_pretty': pretty,
            'goals_sexpr': sexprs,
            'const_inventory': const_inventory(sexprs) if sexprs else None,
        }
        (OUT / f'{k}.json').write_text(
            json.dumps(packet, indent=1, ensure_ascii=False), encoding='utf-8')
        n_ok += status == 'ok'
    print(f'wrote {len(keys)} packets ({n_ok} ok, {len(keys) - n_ok} failed) '
          f'to {OUT}')


if __name__ == '__main__':
    main()
