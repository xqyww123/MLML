#!/usr/bin/env python3
"""
Golden ledger for accepted MathBench_Prover vs PutnamBench environment divergences.

The declared-level divergence check (tools/check_putnam_divergence.py) reports
many divergences that are benign or unavoidable (code-gen internal names,
deliberately `no_notation`-removed operators, names no PutnamBench problem ever
uses, etc.). Re-judging all of them on every run is noise. Instead we keep a
*golden ledger* of already-accepted divergences, each with a rationale, and only
surface the DELTA (newly introduced divergences) for review.

Guardrail (enforced by the playbook, not this module): a divergence may only be
accepted into the golden when the authoritative goal-term check
(tools/test_mathbench_goals.py) is green — i.e. it provably changes no problem's
goal proposition. This module just stores/loads/diffs; it does not judge.

Identity of a divergence is the stable tuple below — counts, import-set labels
and rationale are NOT part of identity (they fluctuate run to run):

  const / type (resolves differently):  (dim, base, putnam, mathbench)
  const_hidden / type_hidden:           (dim, base, putnam, "(hidden)")
  notation:                             ("notation", section, item)
"""

import json
import os

GOLDEN_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'divergence_golden.json')


def entry_key(rec: dict) -> str:
    """Stable identity string for a divergence record."""
    dim = rec['dim']
    if dim == 'notation':
        return f"notation\t{rec.get('section', '')}\t{rec['item']}"
    return f"{dim}\t{rec['base']}\t{rec.get('putnam', '')}\t{rec.get('mathbench', '')}"


def load_golden(path: str = GOLDEN_PATH):
    """Return (meta: dict, by_key: {key: entry}). Missing file -> empty ledger."""
    if not os.path.exists(path):
        return {}, {}
    with open(path) as f:
        data = json.load(f)
    meta = data.get('meta', {})
    by_key = {entry_key(e): e for e in data.get('entries', [])}
    return meta, by_key


def save_golden(meta: dict, by_key: dict, path: str = GOLDEN_PATH):
    """Write the ledger, entries sorted by key for stable diffs."""
    entries = [by_key[k] for k in sorted(by_key)]
    with open(path, 'w') as f:
        json.dump({'meta': meta, 'entries': entries}, f, indent=2, ensure_ascii=False)
        f.write('\n')


def diff_against_golden(records: list, by_key: dict):
    """Partition current records vs the golden ledger.

    Returns (new, known, resolved):
      new      -- records whose key is NOT in the golden (need review)
      known    -- records already accepted (suppressed from the delta report)
      resolved -- golden entries whose key is no longer produced (benign; prunable)
    """
    cur_keys = set()
    new, known = [], []
    for rec in records:
        k = entry_key(rec)
        cur_keys.add(k)
        (known if k in by_key else new).append(rec)
    resolved = [by_key[k] for k in by_key if k not in cur_keys]
    return new, known, resolved
