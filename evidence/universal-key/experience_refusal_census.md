# EXPERIENCE-record refusal census (read-only, production store on `cslh19`)

Measured 2026-08-13 against `cslh19:~/.cache/Isabelle_Semantic_Embedding/semantics.lmdb`
(the CURRENT, post-re-key store; `mtime` 2026-08-13 16:55, swapped in at 17:05 per
`/tmp/rekey/SWAP_TS`). Every LMDB environment was opened `readonly=True, lock=False`.
Nothing was written on `cslh19` outside `/tmp`, nothing in the repo was edited, no
`isabelle build` was run, and the Isa-REPL port 6666 was never touched.

This census serves `BUG_UNIVERSAL_KEY_SHORT_NAME_FIX_PLAN.md` §B.10. It bounds, from
record contents alone, how many EXPERIENCE records the planned migration would have to
report as REFUSALS. The full dry run is not possible yet (the `Experience.constituents`
callback has no external-context variant), and was not attempted.

---

## Verdict

**The store holds 6,861 EXPERIENCE records. Guaranteed refusals: 0. Upper bound if every
undecidable record turned out to refuse: 6,857.**

Both guaranteed-refusal buckets are empty, and they are empty for a strong reason rather
than by luck. Every one of the 403 distinct theory long names that the whole EXPERIENCE
corpus names is a theory that was simultaneously loaded in one single Isabelle image —
the `AFP-ALL-4` image the re-key dumped its dependency table from. Coexisting in one
image is exactly the property "these theories can be merged into one context", so §B.10's
"build the context by merging the theories the old constituent list names" step is
feasible for **all** 6,861 records, not merely for most of them. No record names two
theories that share a base name, and no record names a theory that does not exist.

Four records are free: their constituent list is empty, so they are GLOBAL experiences,
their prefix is the all-zero `xor_theory_prefix([])`, and no context is needed to
recompute it. The remaining 6,857 are undecidable without actually parsing their goal
patterns, which is the honest residue.

So the refusal count lies in **[0, 6857]**, and the width of that interval is not a sign
that the situation is bad — it is a sign that nothing about a refusal is visible in the
record contents. The only refusal condition that can still fire is "a stored goal pattern
fails to re-parse in the merged context". Everything checkable offline is clean. My
reading is that this needs an eyeball on the eventual dry-run output rather than a policy
decided in advance: there is no identifiable sub-population to write a policy about.

One caveat about the second half of §B.10's refusal criterion, "whose recomputed
constituent set names a theory outside that merge". If "the merge" means the merged
theory (hence its whole ancestor cone), that condition can never fire: a term parsed in a
context can only mention constants declared somewhere in that context's cone, so the
recomputed constituent set is a subset of the cone by construction. If "the merge" means
literally the theories the old list names, the condition is a real and probably
frequently-firing test, because the antichain can legitimately move to an ancestor. The
plan should say which it means before the dry run is written; the two readings give very
different refusal counts.

---

## Totals and shape

| Quantity | Value | Exact or bound |
| --- | --- | --- |
| EXPERIENCE records in the store | 6,861 | exact |
| Tombstoned EXPERIENCE records | 0 | exact |
| Records with the WIP bit set (key byte 0 LSB = 1) | 93 | exact |
| Records with the WIP bit clear | 6,768 | exact |
| Distinct theory long names named across all records | 403 | exact |
| Total goal patterns across all records | 16,125 | exact |

All 6,861 are 8-field records; none needs the 13-field tail, none carries locale
provenance, none has its patterns still JSON-packed in `expr` (the legacy form `_decode`
unpacks), and every record's stored key prefix equals `xor_theory_prefix` of its stored
constituent hashes — I re-derived all 6,861 prefixes and found zero disagreement.

The EXPERIENCE kind is `EntityKind.EXPERIENCE = 8`
(`contrib/Isabelle_RPC/Isabelle_RPC_Host/universal_key.py:19`), and an experience key is
the 32-byte XOR-prefixed form: 16-byte prefix, tag byte `0x08`, 15-byte content hash. To
be sure the key shape is the whole population, I also scanned the *values* of all
1,378,960 keys in the store for `kind == 8`: every such record sits under a 32-byte key
with tag byte 8, so there are exactly 6,861 and no odd shapes hiding elsewhere. There is
no system-DB layer installed on `cslh19` (`validated_system_db()` returns `None`), so the
user store is the whole store.

**Constituent-list length distribution** (exact):

| Length | Records |
| --- | --- |
| 0 | 4 |
| 1 | 6,613 |
| 2 | 237 |
| 3 | 7 |

**Reconciliation with §B.10's stated 6,862 / 6,769 / 93.** The store now holds one record
fewer than the plan records, and the missing one is accounted for exactly. The re-key
dropped it: key
`12efb1d4323c4127e59491daf6f9d423082d6b96771be4eb044e611b7201ef4d`, name
`llist_admissibility_ball_lset_imp_filter_eq_via_Bex_and_mcont`, constituents
`['Minilang.Minilang', 'Coinductive.Coinductive_List']`, listed in
`cslh19:/tmp/rekey/dropped_keys.tsv` with reason `xor: constituent Minilang.Minilang
unreproducible` — `Minilang.Minilang` is not in the `AFP-ALL-4` image. It is the only
EXPERIENCE key in that 1,534-row drop list. I confirmed the pre-re-key copy
(`semantics.lmdb.pre-rekey-20260813-170504`) holds 6,862 with the same 4 empty-list
records. So §B.10's counts should read **6,861 / 6,768 / 93**.

Also worth recording against §B.10: the plan's "71 records name a constituent long name
the reached population never resolves to, spread over 11 theories" is **no longer true of
the current store**. All 403 names resolve in the `AFP-ALL-4` image. The re-key's D5 rule
(re-point an experience's unmappable constituents by name to the current generation)
repaired them, and the one name it could not repair produced the single drop above.

---

## Bucket 1 — empty constituent list (free, no refusal possible)

**Exactly 4 records.** All four have the all-zero key prefix, all four therefore test as
persistent by the LSB rule (which is why bucket 1 has to be handled explicitly rather than
folded into the WIP count), and all four are GLOBAL experiences whose patterns are a bare
schematic variable or a wildcard:

```
00000000000000000000000000000000082daeb149697970d2e12365223940ab
    have_premises_are_already_assumed_no_intro            patterns: ['?Q']
000000000000000000000000000000000840f8e835dc28ba66f5622b492cd7c9
    shadowed_local_assms_cite_by_proposition              patterns: ['?P']
0000000000000000000000000000000008b21dc3a1730f5162e32c73a9422532
    cite_manual_facts_by_base_name_not_bracket_suffix     patterns: ['?P']
0000000000000000000000000000000008eafbcbfb9226ae327be86b874df2b5
    define_operation_names_must_be_ascii                  patterns: ['_']
```

These four are also the *only* records whose every pattern is a bare schematic variable or
`_`; every other record's patterns carry real term structure. So there is no larger
"trivially parses anywhere" population to peel off the residue.

---

## Bucket 2 — guaranteed refusal, the named theories cannot form one cone

**Exactly 0 records.**

The test is the one the plan names: two constituent long names sharing a base name
(`Long_Name.base_name`) cannot both live in one context, because
`Context.eq_thy_consistent` rejects it. No record trips it. Stronger, the base-name
collision does not exist anywhere in the corpus's name inventory either: the 403 distinct
long names have 403 distinct base names, so no two records could even be made to collide
by merging their lists.

And stronger still, as noted in the verdict: all 403 names appear as rows of
`cslh19:/tmp/rekey/deps.tsv`, which is the theory list dumped from one *running*
`AFP-ALL-4` image (10,598 theories, every one flagged `L` = `Resources.loaded_theory`
true). Coexistence in a single image is direct evidence — not an inference from base names
— that any subset of them merges.

---

## Bucket 3 — guaranteed refusal, a named theory does not exist

**Exactly 0 records.** Breakdown of the 403 names against the three oracles:

- **403 of 403** appear in `cslh19:/tmp/rekey/deps.tsv` (the `AFP-ALL-4` image closure,
  10,598 theories including `Pure`, `HOL.*`, `HOL-Library.*` and the AFP sessions).
- **119** are AFP theories, and **all 119** are in
  `tools/Build_AFP_Image/afp_all4_theories.txt` (9,331 entries). Zero AFP theories are
  named that the target list omits.
- **284** are absent from `afp_all4_theories.txt` — and all 284 are Isabelle-distribution
  theories, whose `deps.tsv` file path is under `contrib/Isabelle2025-2/`. The target list
  is an AFP theory list, so their absence from it is correct, not a defect. Examples:
  `HOL.Topological_Spaces` (named by 227 records), `HOL.Real` (202),
  `HOL-Computational_Algebra.Polynomial` (148), `HOL-Library.Word` (140).
- **403 of 403** `.thy` files exist on disk in the *local* checkout
  (`/home/qiyuan/Current/MLML`) at the path `deps.tsv` records, after rewriting the
  `cslh19` home prefix. So there is no "not in the target list and no such file" case, and
  no "not in the target list but the file exists" case that is not simply an Isabelle
  distribution theory.

The most-named theories, for a sense of the corpus's centre of gravity:
`HOL.Topological_Spaces` 227, `HOL.Real` 202, `Coinductive.Coinductive_List` 164,
`HOL.Transcendental` 161, `HOL-Computational_Algebra.Polynomial` 148, `HOL-Library.Word`
140, `HOL.Complex` 115, `HOL.Real_Vector_Spaces` 110, `HOL-Library.Extended_Real` 103.

---

## Bucket 4 — suspect, stored hash does not match the theory's current hash

**0 genuine mismatches. 93 records (19 names) carry a hash that is not comparable to a
file-content hash at all, by design, and I explain them below rather than counting them
as suspect.**

I did not have to skip this bucket: the re-key's artefacts survive on `cslh19`. I used
`/tmp/rekey/deps.tsv` (the dependency table §9.1 dumps: 10,598 rows of
name / loaded-flag / file path / parents) and cross-checked against
`/tmp/rekey/live_hashes.tsv` (10,598 hashes dumped by the live Isabelle at re-key time).

I rebuilt the hash table offline exactly as §9.2 prescribes, importing
`theory_xxhash128` from `Isabelle_RPC_Host.theory_hash` on `cslh19` and folding the parent
DAG bottom-up. **All 10,598 offline-recomputed hashes agree with `live_hashes.tsv`,
byte for byte, with zero disagreements** — so the offline table and the live prover agree,
and either can be used as the reference.

Against that reference:

- **384 of the 403 names carry a stored hash equal to the recomputed current hash.** Zero
  persistent mismatches.
- **19 names carry a stored hash whose byte-0 LSB is set — a WIP theory hash**, and those
  19 are precisely the names whose stored hash differs from the recomputed one. A WIP hash
  is not a content hash: `contrib/Isabelle_RPC/Tools/theory_hash.ML:194-212` takes the
  `Resources.loaded_theory = false` branch and computes an FNV-1a-128 digest of the theory
  *long name alone*, then sets the LSB, deliberately making the identity
  content-independent. I reimplemented that digest in Python (both `Hasher_Lo` and
  `Hasher_Hi` instances from `contrib/Isabelle_RPC/Tools/Term_Digest.ML:172-180`, big-endian
  packing per `digest128_to_array`) and **all 19 stored hashes reproduce exactly**. So they
  are not corrupt; they are records written by an AoA session that had loaded those
  theories from source instead of from a heap image.

  The 19 are the whole of `Abstract-Rewriting.*` (7 theories),
  `Affine_Arithmetic.*` (11) and `Algebraic_Numbers.Interval_Arithmetic`.

- The 93 records with the WIP key bit are exactly the records touching one of those 19
  names — the two populations coincide, which is the expected consistency (the prefix's
  LSB is the OR of the constituents' LSBs). 41 of the 93 mix a WIP-hashed constituent with
  a persistent one (e.g. `['HOL.Product_Type', 'Abstract-Rewriting.Abstract_Rewriting']`);
  every one of the 403 names has exactly one stored hash across the whole corpus, so a
  given name is consistently WIP-hashed or consistently content-hashed, never both.

**A policy question this raises for §B.10, which is not a refusal.** If the migration
builds its context in a session where `Abstract-Rewriting` and `Affine_Arithmetic` come
from a heap image, those 19 theories will be `loaded_theory = true`, so the recomputed
constituents will be content hashes with the LSB clear, and these 93 records will migrate
from WIP keys to persistent keys. That changes what `is_WIP` says about them and what the
CI export filter does with them. The plan does not say whether that is intended. It should
decide, because the alternative — reproducing the WIP hashes — is only possible by
building the context from source rather than from a heap.

---

## Bucket 5 — cannot be decided without parsing

**6,857 records** (every record except the four in bucket 1). This is the honest residue
and the upper bound on refusals.

For each of these, the merge step is known to succeed (bucket 2 and 3 are empty, and the
named theories demonstrably coexist in one image), the stored constituent hashes are known
to be either the current content hash or a correctly-formed WIP name hash (bucket 4), and
the record's content-derived key tail is recomputable offline without any of this. What
remains unknown is only whether `Syntax.parse_term` accepts each stored `goal_patterns`
entry in the merged context — and, depending on how §B.10's second criterion is read,
whether the recomputed antichain stays inside the literally-named theory set.

What I can say about the patterns without parsing them, all exact counts:

- 16,125 patterns over 6,857 records; per-record counts run 1 (985 records), 2 (3,171),
  3 (2,187), 4 (406), 5 (79), 6 (20), 7 (7), 8 (5), 9 (1).
- **0 patterns contain a non-ASCII character.** They are all in Isabelle's ASCII notation
  as the field's contract requires; 8,719 of them use `\<...>` symbol escapes.
- **0 patterns are empty or whitespace-only**, and **0 have unbalanced parentheses** — the
  two cheapest lexical ways a pattern could be obviously unparseable.
- 15,693 of 16,125 contain a schematic variable `?`.
- Pattern length: minimum 1 character, median 45, maximum 642.

None of these is evidence that a pattern *will* parse — parsing depends on constant and
type resolution in the merged context, which no lexical check can anticipate. They only
say that no record is unparseable for a trivially visible reason.

Representative residue records, to show the range:

```
1 constituent   symmetric_poly_roots_constant_polynomial_lift
                ['Polynomials.MPoly_Type', 'HOL-Computational_Algebra.Polynomial']   (2)
2 constituents  eval_fds_iterated_derivative_by_funpow_induction
                ['HOL-Analysis.Derivative', 'Dirichlet_Series.Dirichlet_Series']
3 constituents  sum_list_permutation_invariance_via_flip_sum_mset_sum_list
                ['HOL.Real', 'Affine_Arithmetic.Affine_Form', 'HOL-Combinatorics.Permutations']
3 constituents  fds_zero_from_frequent_zeros_first_coefficient_tail_bound
                ['HOL-Analysis.Inner_Product', 'HOL-Library.Going_To_Filter',
                 'Dirichlet_Series.Dirichlet_Series']
```

All seven 3-constituent records mix an Isabelle-distribution theory with AFP theories from
one or two sessions; none is anywhere near a cone conflict.

---

## Exactly what I ran

Source reading, in `/home/qiyuan/Current/MLML`:
`BUG_UNIVERSAL_KEY_SHORT_NAME_FIX_PLAN.md` §B.10 and Part C;
`THEORY_HASH_REKEY_PLAN.md` §9.1–§9.3;
`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/semantics.py` (the `Record`
NamedTuple, `_decode`, `record_constituent_hashes`);
`contrib/Isabelle_RPC/Isabelle_RPC_Host/universal_key.py` (`EntityKind`,
`xor_theory_prefix`, `is_WIP`);
`contrib/Isabelle_RPC/Isabelle_RPC_Host/theory_hash.py` (`theory_xxhash128`);
`contrib/Isabelle_RPC/Tools/theory_hash.ML` (the loaded/WIP branch);
`contrib/Isabelle_RPC/Tools/Term_Digest.ML` (`Hasher_Fn`, `string128`,
`digest128_to_array`).

On `cslh19`, three scripts, each opening every environment `readonly=True, lock=False` and
writing only under `/tmp`:

1. `/tmp/exp_census_extract.py` — one cursor pass over
   `~/.cache/Isabelle_Semantic_Embedding/semantics.lmdb`; selects the 32-byte keys with
   tag byte 8, decodes each value with the same positional layout as `_Semantic_DB._decode`
   (including the legacy JSON-in-`expr` fallback), re-derives every key prefix with
   `xor_theory_prefix`, and dumps the result to `/tmp/exp_census_records.json`. It also
   reported the whole-store key-length and tag histograms (1,378,960 keys; 1,166,291
   32-byte keys; tag 8 = 6,861).
2. `/tmp/exp_census_recompute.py` — rebuilds the theory-hash table bottom-up from
   `/tmp/rekey/deps.tsv` using `theory_xxhash128` imported from the `cslh19` checkout, and
   diffs all 10,598 results against `/tmp/rekey/live_hashes.tsv`.
3. Two short inline `python3 - <<EOF` probes: one counting EXPERIENCE records in
   `semantics.lmdb.pre-rekey-20260813-170504` and diffing the pre/post key sets to find the
   single lost record; one scanning every value in the live store for `kind == 8` to prove
   no experience hides under a non-32-byte key. Plus
   `validated_system_db()` to confirm no system DB layer exists.

Locally, in the session scratchpad, `analyse1.py` … `analyse7.py` over the fetched
`exp_records.json`, `deps.tsv` and `live_hashes.tsv`: the bucket tests, the name inventory,
the length and WIP distributions, the three existence oracles, the live-hash comparison,
the Python reimplementation of the WIP FNV-1a-128 name digest, and the pattern statistics.

I did **not** connect to `cslh19:6666`, did not run any `isabelle` command, and did not
attempt the §B.10 dry run.

### Which numbers are exact and which are bounds

Exact, in the sense of a complete enumeration of the store: the 6,861 record total, the
93 / 6,768 WIP split, the 4 empty-constituent records, the 403 distinct theory long names,
the constituent-length distribution, the 16,125 patterns and all pattern statistics, the
0 base-name collisions, the 0 non-existent theories, the 384 / 19 hash split and the 0
disagreements between the offline and live hash tables.

Bounds: the refusal count itself. **0 is a hard lower bound** (both guaranteed-refusal
buckets are provably empty from record contents). **6,857 is a hard upper bound** (every
non-GLOBAL record could in principle fail to parse). Nothing measurable offline narrows
the interval further; only the dry run can, once the external-context unpacker exists.
