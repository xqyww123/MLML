#!/usr/bin/env python3
"""
Check whether MathBench_Prover's environment diverges from PutnamBench's.

A PutnamBench problem is written in its own import context. When proved under
MathBench_Prover instead, a short name or a piece of concrete syntax may resolve
to something different (or become unavailable), silently changing the meaning of
the statement or breaking the proof. This tool detects every such divergence
along three dimensions:

  1. constant short-name resolution   (base name -> long const)
  2. type short-name resolution       (base name -> long type)
  3. notation / 符号                   (mixfix grammar productions, parse & print
                                       rules; a subkind of syntax distinct from
                                       name resolution)

How it works
------------
The MathBench_Prover side is the *reference*: load `Env_Dump.thy` once in a
MathBench-capable session to emit

  /tmp/mathbench_const.tsv   /tmp/mathbench_type.tsv   /tmp/mathbench_notation.txt

The PutnamBench side is produced here: for every unique import combination found
in data/PutnamBench, this connects to a plain-HOL Isabelle REPL, loads a theory
with those imports, and runs the *same* dump logic (tasks/MathBench_Prover/
env_dump.ML, inlined) so both sides are byte-comparable.

Usage
-----
    python tools/check_putnam_divergence.py [REPL_ADDRESS] [--report FILE]

    REPL_ADDRESS defaults to 127.0.0.1:6666 (must be a plain HOL session)
"""

import argparse
import asyncio
import os
import re
import sys
import glob
import tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'contrib', 'Isa-REPL'))
sys.path.insert(0, HERE)

from IsaREPL import Client, REPLFail
from detect_putnam_conflicts import parse_imports
import divergence_golden as golden

PUTNAM_DIR = os.path.join(ROOT, 'data', 'PutnamBench', 'isabelle')
ENV_DUMP_ML = os.path.join(ROOT, 'tasks', 'MathBench_Prover', 'env_dump.ML')
MATHBENCH_THY = os.path.join(ROOT, 'tasks', 'MathBench_Prover', 'MathBench_Prover.thy')

REF_CONST = '/tmp/mathbench_const.tsv'
REF_TYPE = '/tmp/mathbench_type.tsv'
REF_NOTATION = '/tmp/mathbench_notation.txt'


def _mktemp(prefix, suffix):
    fd, path = tempfile.mkstemp(prefix=prefix, suffix=suffix)
    os.close(fd)
    return path


def _putnam_commit():
    import subprocess
    try:
        return subprocess.check_output(
            ['git', '-C', PUTNAM_DIR, 'rev-parse', 'HEAD'],
            text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return 'unknown'


# --------------------------------------------------------------------------- #
#  Reading resolution maps (base -> winner long name)
# --------------------------------------------------------------------------- #

def read_resolution(path):
    """Read a `base \\t winner` TSV into {base: winner}."""
    mapping = {}
    with open(path) as f:
        for line in f:
            parts = line.rstrip('\n').split('\t')
            if len(parts) >= 2:
                mapping[parts[0]] = parts[1]
    return mapping


# --------------------------------------------------------------------------- #
#  Syntax parsing / normalization (strips Pretty markup so content compares)
# --------------------------------------------------------------------------- #

def normalize_syntax_line(line):
    # Pretty markup embeds control bytes *inside* words (e.g. "block\x06indent=2",
    # "break\x06width=1"), so control bytes must be stripped BEFORE the markup
    # regexes can match.
    s = re.sub(r'[\x00-\x09\x0b-\x1f]', '', line)
    for prefix in ('text_fold', 'itemblock'):
        s = s.replace(prefix, '')
    s = re.sub(r'blockindent=\d+', '', s)
    s = re.sub(r'breakwidth=\d+', '', s)
    s = re.sub(r'"keyword1block([^"]*)"', r' \1 ', s)
    s = re.sub(r'\s+', ' ', s).strip()
    return s


SYNTAX_HEADERS = ['productions', 'parse_rules', 'print_rules',
                  'parse_ast_translation', 'parse_translation',
                  'print_translation', 'print_ast_translation', 'lexicon']


def split_syntax_sections(text):
    """Return {section: [normalized lines]} for the grammar/rule sections."""
    sections = defaultdict(list)
    current = None
    for raw in text.split('\n'):
        raw = raw.strip()
        if not raw:
            continue
        matched = False
        for hdr in SYNTAX_HEADERS:
            if hdr + ':' in raw:
                current = hdr
                matched = True
                break
        if matched:
            continue
        if current in ('productions', 'parse_rules', 'print_rules'):
            norm = normalize_syntax_line(raw)
            if norm and not norm.startswith('consts:') and not norm.startswith('print modes:'):
                sections[current].append(norm)
    return sections


def rule_lhs(item):
    idx = item.find(r'\<leadsto>')
    return item[:idx].strip() if idx >= 0 else item


def consts_in(item):
    """Extract long const/type names referenced in a syntax item."""
    return set(re.findall(r'\^(?:const|type)>(\S+?)"', item))


# --------------------------------------------------------------------------- #
#  MathBench no_notation / no_syntax heuristic (for "intentional" flagging)
# --------------------------------------------------------------------------- #

def mathbench_removed_bases():
    """Base names whose notation MathBench_Prover explicitly removes."""
    bases = set()
    try:
        with open(MATHBENCH_THY) as f:
            for line in f:
                m = re.match(r'\s*no_(?:notation|syntax)(?:\s*\(\w+\))?\s+(\S+)', line)
                if m:
                    bases.add(m.group(1).split('.')[-1])
    except OSError:
        pass
    return bases


# --------------------------------------------------------------------------- #
#  The dump theory + reading back
# --------------------------------------------------------------------------- #

def build_probe_theory(env_dump_ml, imports, const_f, type_f, notation_f):
    imports_str = ' '.join(imports)
    call = (
        'Env_Dump.dump_all @{context}\n'
        f'  {{const = "{const_f}", typ = "{type_f}", notation = "{notation_f}"}}'
    )
    return (
        f'theory Env_Probe imports {imports_str}\nbegin\n\n'
        f'ML \\<open>\n{env_dump_ml}\n\\<close>\n\n'
        f'ML \\<open>\n{call}\n\\<close>\n\n'
        f'end'
    )


# --------------------------------------------------------------------------- #
#  Comparison
# --------------------------------------------------------------------------- #

def compare_resolution(mb_map, pu_map):
    """Return (differs, inaccessible).

    differs:       base -> (mathbench_winner, putnam_winner) where they disagree
    inaccessible:  base -> putnam_winner   accessible in Putnam, absent in MathBench
    """
    differs = {}
    inaccessible = {}
    for base, pu_win in pu_map.items():
        if base in mb_map:
            if mb_map[base] != pu_win:
                differs[base] = (mb_map[base], pu_win)
        else:
            inaccessible[base] = pu_win
    return differs, inaccessible


def compare_syntax(mb_sections, pu_sections):
    """Return {section: [(item, kind, mb_counterpart)]} for items in Putnam
    but not MathBench. kind in {'missing', 'redefined'}."""
    out = {}
    for section in ('productions', 'parse_rules', 'print_rules'):
        mb_items = set(mb_sections.get(section, []))
        pu_items = pu_sections.get(section, [])
        findings = []
        for item in pu_items:
            if item in mb_items:
                continue
            if section in ('parse_rules', 'print_rules'):
                lhs = rule_lhs(item)
                mb_match = [r for r in mb_items if rule_lhs(r) == lhs]
                if mb_match:
                    findings.append((item, 'redefined', mb_match[0]))
                else:
                    findings.append((item, 'missing', None))
            else:
                findings.append((item, 'missing', None))
        if findings:
            out[section] = findings
    return out


# --------------------------------------------------------------------------- #
#  Main
# --------------------------------------------------------------------------- #

async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('addr', nargs='?', default='127.0.0.1:7777',
                    help='REPL address (default 127.0.0.1:7777, the pipeline''s dedicated port)')
    ap.add_argument('--report', default='/tmp/putnam_divergence_report.md',
                    help='write a detailed markdown report here')
    ap.add_argument('--limit', type=int, default=0,
                    help='only check the first N import sets (0 = all)')
    ap.add_argument('--full', action='store_true',
                    help='report ALL divergences, not just the delta vs the golden ledger')
    ap.add_argument('--accept-new', action='store_true',
                    help='append the newly-found divergences to the golden ledger '
                         '(use only after the goal-term check is green)')
    ap.add_argument('--rationale', default='',
                    help='rationale recorded for entries added by --accept-new')
    args = ap.parse_args()

    # Each dimension is checked only if its reference dump is present; this lets
    # a syntax-only run proceed when the const/type references (which need a
    # MathBench heap to generate) are not yet available.
    do_const = os.path.exists(REF_CONST)
    do_type = os.path.exists(REF_TYPE)
    do_notation = os.path.exists(REF_NOTATION)
    if not (do_const or do_type or do_notation):
        print("No MathBench reference dumps found. Generate them by loading "
              "tasks/MathBench_Prover/Env_Dump.thy in a MathBench-capable Isabelle "
              "session (jEdit or a MathBench REPL).", file=sys.stderr)
        sys.exit(1)
    for label_, present in (('const', do_const), ('type', do_type), ('notation', do_notation)):
        if not present:
            print(f"NOTE: skipping {label_} dimension (reference dump missing).",
                  file=sys.stderr)

    mb_const = read_resolution(REF_CONST) if do_const else {}
    mb_type = read_resolution(REF_TYPE) if do_type else {}
    mb_notation = split_syntax_sections(open(REF_NOTATION).read()) if do_notation else {}
    removed_bases = mathbench_removed_bases()

    env_dump_ml = open(ENV_DUMP_ML).read()

    thy_files = sorted(glob.glob(os.path.join(PUTNAM_DIR, '*.thy')))
    import_to_files = defaultdict(list)
    for f in thy_files:
        imp = parse_imports(f)
        if imp:
            import_to_files[imp].append(os.path.basename(f))
    unique_imports = sorted(import_to_files.items(), key=lambda x: -len(x[1]))
    if args.limit:
        unique_imports = unique_imports[:args.limit]
    print(f"MathBench reference: {len(mb_const)} consts, {len(mb_type)} types, "
          f"notation sections {[ (k, len(v)) for k, v in mb_notation.items() ]}")
    print(f"PutnamBench: {len(thy_files)} files, {len(unique_imports)} unique import sets\n")

    # Aggregated divergences: key -> set(import label) and file totals
    const_diff = defaultdict(set)      # (base, mb_win, pu_win) -> labels
    const_inacc = defaultdict(set)     # (base, pu_win) -> labels
    type_diff = defaultdict(set)
    type_inacc = defaultdict(set)
    notation_div = defaultdict(set)      # (section, kind, item) -> labels
    label_files = {}

    tmp_c = _mktemp('pd_const_', '.tsv')
    tmp_t = _mktemp('pd_type_', '.tsv')
    tmp_s = _mktemp('pd_syntax_', '.txt')

    async with Client(args.addr, 'HOL') as client:
        await client.set_register_thy(False)
        await client.record_state('base')

        for i, (imports, files) in enumerate(unique_imports):
            label = ' '.join(imports)
            label_files[label] = len(files)
            print(f'[{i+1}/{len(unique_imports)}] {label} ({len(files)} files)')

            for p in (tmp_c, tmp_t, tmp_s):
                if os.path.exists(p):
                    os.unlink(p)

            thy = build_probe_theory(env_dump_ml, imports, tmp_c, tmp_t, tmp_s)
            try:
                outs = await client.eval(thy, timeout=600_000, import_dir=PUTNAM_DIR)
                errs = [e for cmd in (outs or []) for e in cmd.errors]
            except (REPLFail, Exception) as e:
                errs = [str(e)]

            if errs:
                print(f'  SKIP: {errs[0][:120]}')
                await client.rollback('base')
                continue

            pu_const = read_resolution(tmp_c) if do_const else {}
            pu_type = read_resolution(tmp_t) if do_type else {}
            pu_notation = split_syntax_sections(open(tmp_s).read()) if do_notation else {}

            if do_const:
                d, inacc = compare_resolution(mb_const, pu_const)
                for base, (mw, pw) in d.items():
                    const_diff[(base, mw, pw)].add(label)
                for base, pw in inacc.items():
                    const_inacc[(base, pw)].add(label)

            if do_type:
                d, inacc = compare_resolution(mb_type, pu_type)
                for base, (mw, pw) in d.items():
                    type_diff[(base, mw, pw)].add(label)
                for base, pw in inacc.items():
                    type_inacc[(base, pw)].add(label)

            notation_findings = compare_syntax(mb_notation, pu_notation) if do_notation else {}
            for section, findings in notation_findings.items():
                for item, kind, _ in findings:
                    notation_div[(section, kind, item)].add(label)

            print(f'  const: {len(pu_const)}  type: {len(pu_type)}  '
                  f'notation diffs: {sum(len(v) for v in notation_findings.values())}')

            await client.rollback('base')

    for p in (tmp_c, tmp_t, tmp_s):
        if os.path.exists(p):
            os.unlink(p)

    records = build_records(const_diff, const_inacc, type_diff, type_inacc,
                            notation_div, removed_bases, label_files)
    meta, by_key = golden.load_golden()
    new, known, resolved = golden.diff_against_golden(records, by_key)

    shown = records if args.full else new
    title = "ALL divergences" if args.full else "NEW divergences (delta vs golden ledger)"
    # "no longer present" is only meaningful on a full sweep; under --limit most
    # golden entries simply weren't exercised.
    report = render_records(shown, title, len(known), [] if args.limit else resolved)
    print('\n' + report)
    with open(args.report, 'w') as f:
        f.write(report)
    print(f"\n(Report written to {args.report})")
    print(f"Summary: {len(new)} new | {len(known)} known/golden-suppressed | "
          f"{len(resolved)} golden entries no longer present")

    if args.accept_new:
        if not new:
            print("Nothing new to accept.")
        else:
            import datetime
            today = datetime.date.today().isoformat()
            for rec in new:
                e = {k: rec[k] for k in ('dim', 'base', 'putnam', 'mathbench',
                                         'section', 'item') if k in rec}
                e['rationale'] = args.rationale or '(no rationale given)'
                e['accepted'] = today
                by_key[golden.entry_key(rec)] = e
            meta['updated'] = today
            meta.setdefault('putnam_version', _putnam_commit())
            golden.save_golden(meta, by_key)
            print(f"Accepted {len(new)} new entries into {golden.GOLDEN_PATH}")


def _files_for(labels, label_files):
    return sum(label_files.get(l, 0) for l in labels)


def build_records(const_diff, const_inacc, type_diff, type_inacc,
                  notation_div, removed_bases, label_files):
    """Flatten the aggregation dicts into stable divergence records."""
    recs = []

    def add_res(d, dim, hidden):
        for key, labels in d.items():
            if hidden:
                base, pw, mw = key[0], key[1], '(hidden)'
            else:
                base, mw, pw = key            # const_diff key = (base, mathbench, putnam)
            recs.append({'dim': dim, 'base': base, 'putnam': pw, 'mathbench': mw,
                         'nfiles': _files_for(labels, label_files), 'nsets': len(labels)})

    add_res(const_diff, 'const', False)
    add_res(const_inacc, 'const_hidden', True)
    add_res(type_diff, 'type', False)
    add_res(type_inacc, 'type_hidden', True)

    for (section, kind, item), labels in notation_div.items():
        cs = consts_in(item)
        recs.append({
            'dim': 'notation', 'section': section, 'kind': kind, 'item': item,
            'names': ', '.join(sorted(c.split('.')[-1] for c in cs)) or '?',
            'intentional': any(c.split('.')[-1] in removed_bases for c in cs),
            'nfiles': _files_for(labels, label_files), 'nsets': len(labels)})
    return recs


def render_records(records, title, n_known, resolved):
    L = ["# MathBench_Prover vs PutnamBench environment divergences\n",
         f"\n_{title}_\n"]
    groups = [('const', '1. Constant resolves differently'),
              ('const_hidden', '1b. Constant exposed by Putnam, hidden in MathBench'),
              ('type', '2. Type resolves differently'),
              ('type_hidden', '2b. Type exposed by Putnam, hidden in MathBench')]
    for dim, dim_title in groups:
        rs = [r for r in records if r['dim'] == dim]
        L.append(f"\n## {dim_title} ({len(rs)})\n")
        for r in sorted(rs, key=lambda r: r['base']):
            if dim.endswith('hidden'):
                L.append(f"\n- **`{r['base']}`** -> `{r['putnam']}`  [{r['nfiles']}f/{r['nsets']}s]")
            else:
                L.append(f"\n- **`{r['base']}`**  Putnam=`{r['putnam']}`  "
                         f"MathBench=`{r['mathbench']}`  [{r['nfiles']}f/{r['nsets']}s]")
        L.append("\n")

    nrec = [r for r in records if r['dim'] == 'notation']
    L.append(f"\n## 3. Notation 符号 ({len(nrec)})\n")
    for r in sorted(nrec, key=lambda r: r.get('item', '')):
        flag = "  _(likely intentional: no_notation)_" if r.get('intentional') else ""
        L.append(f"\n- [{r.get('kind')}] **{r.get('names', '?')}** "
                 f"[{r['nfiles']}f/{r['nsets']}s]{flag}")
        L.append(f"\n    `{r['item'][:200]}`")

    L.append(f"\n\n---\n{n_known} known divergence(s) suppressed by the golden ledger.\n")
    if resolved:
        L.append(f"{len(resolved)} golden entr(ies) no longer produced (prunable):\n")
        for e in resolved[:60]:
            L.append(f"  - {golden.entry_key(e)}\n")
    return ''.join(L)


if __name__ == '__main__':
    asyncio.run(main())
