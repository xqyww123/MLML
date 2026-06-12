#!/usr/bin/env python3
r"""Sync the 63 corrected formalizations from data/putnamBench.json back into
the data/PutnamBench/isabelle/*.thy sources, restoring the upstream
convention: `definition putnam_X_solution ... \<equiv> undefined` + the answer
in a `(* ... *)` comment, with the theorem referencing the constant.

Also repairs the three JSON entries whose fix kept an `undefined` solution
definition (Easy Mode needs the answer inlined): putnam_2017_b4,
putnam_2018_a1, putnam_2019_b5.

Verification is the round-trip: tools/roundtrip_check_putnam.py regenerates
the JSON from the synced .thy files and byte-compares all 639 entries.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'tools'))
from validate_putnam_fixes import strip_proof_closers
from data.isabelle import _extract_solution_comment

THY_DIR = ROOT / 'data' / 'PutnamBench' / 'isabelle'
FIX_DIR = ROOT / 'putnam_audit' / 'fixes'
JSON_PATH = ROOT / 'data' / 'putnamBench.json'

# Fixes that changed/reformatted the inlined answer expression: the NEW answer
# (goes into the .thy comment; its parenthesized form is un-inlined back to
# the solution constant). Extracted from each fix's `shows` clause.
NEW_ANSWERS = {
    'putnam_1976_b5': r'\<lambda>n. \<lambda>x::real. fact n',
    'putnam_1978_b2': r'(real_of_nat 7)/4',
    'putnam_2007_a4': (
        r'{f :: real poly. \<exists> d :: nat. \<exists> c :: int. '
        r'c \<ge> 1 - int d \<and> (\<forall> n :: real. poly f n = '
        r'(1 / 9) * ((10 powr c) * (9 * n + 1) ^ d - 1))}'),
    'putnam_2022_a1': (
        r'{(a, b). (a = 0 \<and> b = 0) \<or> ((abs a) \<ge> 1) \<or> '
        r'(0 < (abs a) \<and> (abs a) < 1 \<and> '
        r'(b < ln (1 + ((1 - sqrt (1 - a^2))/a)^2) - a * ((1 - sqrt (1 - a^2))/a) '
        r'\<or> b > ln (1 + ((1 + sqrt (1 - a^2))/a)^2) - a * ((1 + sqrt (1 - a^2))/a)))}'),
    'putnam_2023_b5': r'{n::int. n > 0 \<and> (n = 1 \<or> [n = 2] (mod 4))}',
}
# Fixes that kept the solution CONSTANT (with an undefined def) in the fixed
# theory: their .thy is near-verbatim, and their JSON entry must be re-inlined.
NAME_KEEPING = ('putnam_2017_b4', 'putnam_2018_a1', 'putnam_2019_b5')


def split_at_theorem(src: str) -> tuple[str, str]:
    m = re.search(r'(?m)^theorem ', src)
    assert m, 'no theorem command'
    return src[:m.start()], src[m.start():]


def original_parts(name: str):
    """(header_before_def, def_block(or None), answer(or None), theorem, tail)
    of the pristine .thy."""
    thy = (THY_DIR / f'{name}.thy').read_text(encoding='utf-8')
    mt = re.search(r'(?m)^theorem ', thy)
    assert mt, name
    pre, rest = thy[:mt.start()], thy[mt.start():]
    msor = re.search(r'(?m)^\s*sorry\b', rest)
    assert msor, f'{name}: no sorry tail'
    theorem, tail = rest[:msor.start()], rest[msor.start():]
    md = re.search(rf'(?m)^(definition|fun)\s+{name}_solution\b', pre)
    if not md:
        return pre, None, None, theorem, tail
    defblock = pre[md.start():]
    answer = _extract_solution_comment(defblock)
    return pre[:md.start()], defblock, answer, theorem, tail


def sync_one(name: str, data: dict) -> None:
    fix = json.loads((FIX_DIR / f'{name}.json').read_text(encoding='utf-8'))
    fixed = strip_proof_closers(fix['fixed_theory'])
    _, defblock, old_answer, old_theorem, tail = original_parts(name)
    sol = f'{name}_solution'

    if defblock is None or old_answer is None:
        # plain problem: the JSON form IS the .thy form (minus the tail)
        new_thy = fixed + '\n' + tail
        (THY_DIR / f'{name}.thy').write_text(new_thy, encoding='utf-8')
        return

    # inlined-type problem
    if name in NAME_KEEPING:
        # fixed theory already carries the undefined def + constant reference;
        # .thy is near-verbatim. Re-inline the JSON entry for Easy Mode.
        new_thy = fixed + '\n' + tail
        (THY_DIR / f'{name}.thy').write_text(new_thy, encoding='utf-8')
        fh, ft = split_at_theorem(fixed)
        md = re.search(rf'(?m)^(definition|fun)\s+{sol}\b', fh)
        assert md, name
        defb = fh[md.start():]
        ans = _extract_solution_comment(defb)
        assert ans, f'{name}: no answer comment in fixed def'
        json_src = (fh[:md.start()] + ft).replace(sol, f'({ans})')
        assert sol not in json_src
        data[name] = json_src + '\n  '
        return

    answer = NEW_ANSWERS.get(name, old_answer)
    inl = f'({answer})'
    fh, ft = split_at_theorem(fixed)
    n_orig = old_theorem.count(sol)
    n_inl = ft.count(inl)
    assert n_inl == n_orig > 0, \
        f'{name}: {n_inl} inlined-answer occurrence(s) vs {n_orig} in original'
    assert sol not in fixed, f'{name}: unexpected constant name in fixed text'
    # restore: theorem references the constant; def block carries the answer
    new_theorem = ft.replace(inl, sol)
    sig = defblock[:defblock.index('where')]
    new_def = (f'{sig}where "{sol} \\<equiv> undefined"\n(* {answer} *)\n')
    new_thy = fh + new_def + new_theorem + '\n' + tail
    (THY_DIR / f'{name}.thy').write_text(new_thy, encoding='utf-8')


def main():
    data = json.loads(JSON_PATH.read_text(encoding='utf-8'))
    names = sorted(p.stem for p in FIX_DIR.glob('*.json'))
    for name in names:
        sync_one(name, data)
    JSON_PATH.write_text(
        json.dumps(data, indent=4, ensure_ascii=False), encoding='utf-8')
    print(f'synced {len(names)} .thy files; JSON re-inlined for '
          f'{len(NAME_KEEPING)} name-keeping entries')


if __name__ == '__main__':
    main()
