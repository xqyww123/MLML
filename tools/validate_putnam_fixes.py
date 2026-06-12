#!/usr/bin/env python3
"""Deterministic validation of the proposed PutnamBench fixes: every corrected
theory must elaborate in its own import environment; capture the corrected
goal in pretty + sexpr form for the adversarial fidelity review."""
import asyncio
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'contrib' / 'Isa-REPL'))

from tools.test_mathbench_goals import rename_theory
from tools.build_putnam_audit_packets import grab, const_inventory
from IsaREPL.IsaREPL import Client

FIXES = ROOT / 'putnam_audit' / 'fixes'


def strip_proof_closers(src: str) -> str:
    """Some proposed fixes append `sorry` (closing the proof and dropping us
    back into theory mode, where context() has no goal to report). PutnamBench
    sources deliberately stop at `shows ...`; normalize the fixes the same
    way: strip trailing `end`/`sorry`/`oops` lines."""
    lines = src.rstrip().split('\n')
    while lines and lines[-1].strip() in ('', 'end', 'sorry', 'oops'):
        lines.pop()
    return '\n'.join(lines)


async def main():
    files = sorted(FIXES.glob('*.json'))
    repl = Client('127.0.0.1:7777', 'HOL', timeout=300)
    n_ok = 0
    async with repl:
        await repl.record_state('init')
        for i, p in enumerate(files):
            fix = json.loads(p.read_text())
            await repl.rollback('init')
            status, pretty, sexprs = await grab(
                repl, rename_theory(strip_proof_closers(fix['fixed_theory']),
                                    '_fixchk2'))
            fix['validation'] = {
                'status': status,
                'new_goals_pretty': pretty,
                'new_goals_sexpr': sexprs,
                'new_const_inventory': const_inventory(sexprs) if sexprs else None,
            }
            p.write_text(json.dumps(fix, indent=1, ensure_ascii=False))
            if status != 'ok':
                print(f'  [{i+1}/{len(files)}] {p.stem}: {status}')
            else:
                n_ok += 1
    print(f'{n_ok}/{len(files)} fixed theories elaborate cleanly')


if __name__ == '__main__':
    asyncio.run(main())
