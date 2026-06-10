#!/usr/bin/env python3
"""
Detect conflicting short names in PutnamBench Isabelle environments.

For each unique import set found in PutnamBench .thy files, loads a theory
with those imports and finds all short names that resolve ambiguously.

Usage:
    python tools/detect_putnam_conflicts.py [REPL_ADDRESS]

    REPL_ADDRESS defaults to 127.0.0.1:6666
"""

import asyncio
import sys
import os
import re
import glob
import tempfile
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'contrib', 'Isa-REPL'))
from IsaREPL import Client, REPLFail

PUTNAM_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'PutnamBench', 'isabelle')


def make_conflict_ml(out_file):
    r"""Generate ML code that writes conflicts to a file."""
    return r'''
val ctxt = @{context};
val thy = Proof_Context.theory_of ctxt;
val {const_space, constants, ...} = Consts.dest (Sign.consts_of thy);

fun all_accessible space base =
  let val result = Name_Space.intern space base
  in
    if Long_Name.is_hidden result then []
    else result :: all_accessible (Name_Space.hide false result space) base
  end
  handle ERROR _ => [];

val by_base = fold (fn (long_name, _) =>
    Symtab.map_default (Long_Name.base_name long_name, []) (cons long_name)
  ) constants Symtab.empty;

val conflicts = Symtab.dest by_base
  |> map_filter (fn (base, _) =>
    (case try (all_accessible const_space) base of
      SOME accessible =>
        if length accessible > 1 then SOME (base, accessible) else NONE
    | NONE => NONE))
  |> sort (string_ord o apply2 fst);

val out = TextIO.openOut "''' + out_file + r'''";
val _ = List.app (fn (base, accessible) =>
  let val current = Name_Space.intern const_space base
  in List.app (fn long_name =>
    let val mark = if long_name = current then "*" else ""
    in TextIO.output (out, base ^ "\t" ^ long_name ^ "\t" ^ mark ^ "\n") end
  ) accessible end
) conflicts;
val _ = TextIO.closeOut out
'''


def parse_imports_str(content):
    """Extract the import list from a theory's source text (a sorted tuple)."""
    m = re.search(r'theory\s+\S+\s+imports\s+(.*?)\s+begin', content, re.DOTALL)
    if not m:
        return None
    raw = m.group(1)
    raw = re.sub(r'\(\*.*?\*\)', '', raw, flags=re.DOTALL)
    return tuple(sorted(re.findall(r'"[^"]*"|\S+', raw)))


def parse_imports(thy_file):
    """Extract the import list from a .thy file header."""
    with open(thy_file) as f:
        return parse_imports_str(f.read())


def read_conflicts(path):
    """Read conflict lines from a TSV file written by ML."""
    if not os.path.exists(path):
        return []
    conflicts = []
    with open(path) as f:
        for line in f:
            parts = line.rstrip('\n').split('\t')
            if len(parts) >= 2:
                base = parts[0]
                long_name = parts[1]
                is_current = len(parts) >= 3 and parts[2] == '*'
                conflicts.append((base, long_name, is_current))
    return conflicts


async def check_conflicts(client, imports, tmp_file):
    """Run conflict detection ML code under the given imports."""
    imports_str = ' '.join(imports)
    ml_code = make_conflict_ml(tmp_file)
    thy_src = (
        f'theory Conflict_Check imports {imports_str}\n'
        f'begin\n\n'
        f'ML \\<open>\n{ml_code}\n\\<close>\n\n'
        f'end'
    )

    if os.path.exists(tmp_file):
        os.unlink(tmp_file)

    try:
        outputs = await client.eval(thy_src, timeout=300_000, import_dir=PUTNAM_DIR)
    except REPLFail as e:
        return None, str(e)
    except Exception as e:
        return None, str(e)

    for cmd in (outputs or []):
        if cmd.errors:
            return None, '; '.join(cmd.errors)

    return read_conflicts(tmp_file), None


async def main():
    addr = sys.argv[1] if len(sys.argv) > 1 else '127.0.0.1:6666'

    thy_files = sorted(glob.glob(os.path.join(PUTNAM_DIR, '*.thy')))
    if not thy_files:
        print(f"No .thy files found in {PUTNAM_DIR}", file=sys.stderr)
        sys.exit(1)

    import_to_files = defaultdict(list)
    for f in thy_files:
        imports = parse_imports(f)
        if imports:
            import_to_files[imports].append(os.path.basename(f))

    unique_imports = sorted(import_to_files.items(), key=lambda x: -len(x[1]))
    print(f"Found {len(thy_files)} theory files, {len(unique_imports)} unique import sets\n")

    all_conflicts = {}
    tmp_file = tempfile.mktemp(prefix='putnam_conflicts_', suffix='.tsv')

    async with Client(addr, 'HOL') as client:
        await client.set_register_thy(False)
        await client.record_state('base')

        for i, (imports, files) in enumerate(unique_imports):
            label = ' '.join(imports)
            print(f'[{i+1}/{len(unique_imports)}] {label}')
            print(f'  {len(files)} files: {", ".join(files[:3])}{"..." if len(files) > 3 else ""}')

            conflicts, error = await check_conflicts(client, imports, tmp_file)

            if error:
                print(f'  SKIP: {error[:120]}')
            elif conflicts:
                bases = set(b for b, _, _ in conflicts)
                print(f'  {len(bases)} conflicting short names')
                all_conflicts[imports] = (files, conflicts)
            else:
                print(f'  No conflicts')

            await client.rollback('base')

    if os.path.exists(tmp_file):
        os.unlink(tmp_file)

    out_path = '/tmp/putnam_conflicts.tsv'
    with open(out_path, 'w') as f:
        f.write('imports\tshort_name\tlong_name\tcurrent\n')
        for imports, (files, conflicts) in sorted(all_conflicts.items()):
            imp_label = ' '.join(imports)
            for base, long_name, is_current in conflicts:
                f.write(f'{imp_label}\t{base}\t{long_name}\t{"*" if is_current else ""}\n')

    print(f'\nResults written to {out_path}')

    all_bases = defaultdict(lambda: defaultdict(set))
    for imports, (_, conflicts) in all_conflicts.items():
        for base, long_name, is_current in conflicts:
            all_bases[base][long_name].update(
                ['*'] if is_current else []
            )

    print(f'\n{"="*80}')
    print(f'SUMMARY: {len(all_bases)} unique conflicting short names')
    print(f'{"="*80}\n')
    for base in sorted(all_bases):
        names = sorted(all_bases[base])
        current = [n for n in names if '*' in all_bases[base][n]]
        others = [n for n in names if '*' not in all_bases[base][n]]
        cur_str = current[0] if current else '?'
        print(f'  {base}')
        print(f'    resolves to: {cur_str}')
        for o in others:
            print(f'    also exposed: {o}')


if __name__ == '__main__':
    asyncio.run(main())
