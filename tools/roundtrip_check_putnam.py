#!/usr/bin/env python3
r"""Round-trip check: regenerate the putnamBench dataset from the (synced)
data/PutnamBench/isabelle/*.thy sources using the same logic as
data.isabelle.preprocess_PutnamBench, and byte-compare every entry against
data/putnamBench.json. Zero differences proves the .thy sync is faithful."""
import asyncio
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'contrib' / 'Isa-REPL'))

from data.isabelle import _extract_solution_comment
from IsaREPL.IsaREPL import Client

BASE = ROOT / 'data' / 'PutnamBench' / 'isabelle'


async def regen(addr='127.0.0.1:7777'):
    dataset, skipped = {}, []
    repl = Client(addr, 'HOL', timeout=300)
    async with repl:
        for file in sorted(os.listdir(BASE)):
            if not file.endswith('.thy'):
                continue
            name = file[:-4]
            content = (BASE / file).read_text(encoding='utf-8')
            commands = await repl.fast_lex(content)
            theorem_index = next(
                (i for i, (_, t) in enumerate(commands)
                 if t.strip().startswith('theorem')), -1)
            if theorem_index == -1:
                skipped.append(name)
                continue
            sol = f'{name}_solution'
            defn_index = next(
                (i for i, (_, t) in enumerate(commands[:theorem_index])
                 if f'definition {sol}' in t or f'fun {sol}' in t), None)
            if defn_index is None or 'undefined' not in commands[defn_index][1]:
                dataset[name] = '\n'.join(c[1] for c in commands[:theorem_index + 1])
                continue
            answer = _extract_solution_comment(commands[defn_index][1])
            if answer is None:
                skipped.append(name)
                continue
            remaining = [c for i, c in enumerate(commands[:theorem_index + 1])
                         if i != defn_index]
            dataset[name] = '\n'.join(c[1] for c in remaining).replace(
                sol, f'({answer})')
    return dataset, skipped


def main():
    dataset, skipped = asyncio.run(regen())
    cur = json.loads((ROOT / 'data' / 'putnamBench.json').read_text(encoding='utf-8'))
    print(f'regenerated {len(dataset)} (skipped {len(skipped)}), current {len(cur)}')
    diffs = []
    for k in sorted(set(dataset) | set(cur)):
        a, b = dataset.get(k), cur.get(k)
        if a is None or b is None:
            diffs.append((k, 'missing-on-one-side'))
        elif a.strip() != b.strip():
            diffs.append((k, 'content'))
    if diffs:
        print(f'{len(diffs)} DIFFERENCES:')
        for k, why in diffs[:20]:
            print(' ', k, why)
        Path('/tmp/putnam_roundtrip_regen.json').write_text(
            json.dumps(dataset, indent=4, ensure_ascii=False))
        print('regen dump: /tmp/putnam_roundtrip_regen.json')
    else:
        print('ROUND-TRIP CLEAN: all entries identical (modulo outer whitespace)')


if __name__ == '__main__':
    main()
