# Theories to re-interpret after the theory-hash re-key

Companion to `THEORY_HASH_REKEY_PLAN.md`. Scope: the `cslh19` store, migrated to
theory hashes that fold in the theory long name.

Derived on 2026-08-13 from the `AFP-ALL-4` image itself (all 10,598 theories it
holds, `Pure` included), not from the store: a pair of theories that share a
hash today is invisible in the store whenever only one side was ever
interpreted, so the store cannot produce this list.

Of 1,380,494 entries, **1,378,960 migrate and 1,534 (0.111%) are dropped** —
and 736 of those 1,534 are duplicates of a record that stays, so the genuine
loss is 798.

## A. Re-interpret — the theory shared its hash with another

**52 records dropped**, not the 110 an earlier revision of this document
claimed. These 20 theories share a 16-byte hash with a partner. A record whose
key carries nothing but that hash — a name-addressed key, a theory-status key —
cannot be attributed to either theory and is discarded: 42 and 10 respectively.
A theorem record is different: it stores its constituents as (long name, hash)
pairs, so the name is on record and resolves the collision exactly. **All 58
such records are rescued** — 41 naming
`CryptoBasedCompositionalProperties.ListExtras`, 13
`Core_DOM.Core_DOM_Basic_Datatypes`, 4 `Core_SC_DOM.Core_DOM_Basic_Datatypes`.

After the migration each name gets its own hash and the pair separates. The
theories needing re-interpretation are unchanged; only the counts move.

Seven groups are genuinely distinct `.thy` files that happen to be byte
identical:

| theory | partner | dropped | (rescued by name) |
| --- | --- | --- | --- |
| `CryptoBasedCompositionalProperties.ListExtras` | `FocusStreamsCaseStudies.ListExtras` | 4 | 41 |
| `Core_DOM.Core_DOM_Basic_Datatypes` | `Core_SC_DOM.Core_DOM_Basic_Datatypes` | 6 | 17 |
| `Lowe_Ontological_Argument.Relations` | `Types_Tableaus_and_Goedels_God.Relations` | 16 | 0 |
| `Core_DOM.Testing_Utils` | `Core_SC_DOM.Testing_Utils` | 4 | 0 |
| `Superposition_Calculus.Relation_Extra` | `Typed_Ordered_Resolution.Relation_Extra` | 1 | 0 |
| `Separation_Logic_Imperative_HOL.Imperative_HOL_Add` | `Van_Emde_Boas_Trees.Imperative_HOL_Add` | 1 | 0 |
| `Conditional_Simplification.Reference_Prerequisites` | `Intro_Dest_Elim.Reference_Prerequisites` | 1 | 0 |

Three groups are **one `.thy` file loaded under two long names** — a
session-qualified name and a dotless global one — so Isabelle holds two distinct
theory values for one file. Two of the three are artefacts of the image
generator: `tools/Build_AFP_Image/AFP-DEP0/all_theories.lst:825,962` lists the
session-qualified spelling of a theory declared `(global)`, while the `sessions`
block pulls the same file in under its bare name, and deleting those two lines
removes both duplicates. `HOL-CSP.HOL-CSP` is not removable — it comes from AFP
source, `CSP_RefTK/Process_norm.thy:48`.

| file | the two names | dropped | (rescued by name) |
| --- | --- | --- | --- |
| `afp/thys/Restriction_Spaces-Examples/HOLCF/Restriction_Spaces-HOLCF.thy` | `Restriction_Spaces-HOLCF` / `Restriction_Spaces-HOLCF.Restriction_Spaces-HOLCF` | 17 | 0 |
| `Isabelle2025-2/src/HOL/HOLCF/HOLCF.thy` | `HOLCF` / `HOLCF.HOLCF` | 1 | 0 |
| `afp/thys/HOL-CSP/HOL-CSP.thy` | `HOL-CSP` / `HOL-CSP.HOL-CSP` | 1 | 0 |

`HOLCF.thy` and `HOL-CSP.thy` are pure collector theories — imports plus
`default_sort` — that define **zero** entities and appear in **zero** constituent
lists, so their duplicate costs one theory-status record and no LLM spend. Only
`Restriction_Spaces-HOLCF` has real entities (16 of them).

## B. Re-interpret — lost every record

**No theory.** 736 records are dropped because they hang off a superseded
content generation (13 theories, all under `Gauss_Jordan` and
`Rank_Nullity_Theorem`) whose `.thy` bytes had changed when they were written,
so the old hash can never be recomputed. **Every one of the 736 is a duplicate
of a record that stays**: re-pointing it by long name to the current generation
lands it on a key the current generation's record already holds. Measured by
running the migration with the revival rule widened to exactly that (plan D5a).
So nothing is lost and none of these theories needs re-interpretation.

**But 43 EXPERIENCE records are a different matter**, and are handled by the
plan's D5 rather than by re-interpretation: they are agent-authored proof
strategies, and no interpretation run recreates them, and — unlike the 736 —
they have no counterpart under the current generation. 42 are revived by
re-pointing their superseded constituents to the current generation by name,
which a per-record check of all 775 references they make confirmed is sound; 1,
naming `Minilang.Minilang`, is dropped with the rest of §C.

## C. Dropped, out of scope

**733 records belonging to 13 theories `AFP-ALL-4` does not hold.** Out of scope
by the plan's D6, and not re-interpretable under that image. Counted per
offending theory, so a record naming two of them appears twice:

| theory | records dropped |
| --- | --- |
| `NTP4Verif.NTP4Verif` | 398 |
| `MathBench_ProverBase.Geo_Real2` | 277 |
| `Auto_Sledgehammer.Auto_Sledgehammer` | 20 |
| `MathBench_Prover.MathBench_Prover` | 15 |
| `Minilang.Minilang` | 6 |
| `MathBench_ProverBase.MathBench_ProverBase` | 3 |
| `Performant_Isabelle_ML.Performant_Isabelle_ML` | 3 |
| `Semantic_Embedding.Semantic_Embedding` | 3 |
| `Isabelle_RPC.Remote_Procedure_Calling` | 2 |
| `Minilang_Agent.Minilang_Agent` | 2 |
| `Minilang_AoA.Minilang_AoA` | 2 |
| `Isa_REPL.Isa_REPL` | 1 |
| `MiniF2F_MyProver.MiniF2F_MyProver` | 1 |

An earlier revision of this document said "29 theories" with "25 hashes with no
recoverable name". There are no unrecoverable names: `theory_hash.lmdb` maps
every one of them to a long name, and the 13 above is what that resolves to.

28 of these are theory-status records; see the plan's §4 for why keeping the
flag would be worse than dropping it.

## What happens to `phi-system`, `Why3STD` and `pearl_*`

Their **theory hashes** do not move: those theories are WIP-hashed (FNV-128 of
the long name, already name-addressed), and this change does not touch the WIP
branch.

**Their record keys do move, and an earlier revision of this document said
otherwise.** A theorem key's 16-byte prefix is the XOR of *all* its
constituents' hashes, and only bit 0 of byte 0 carries the WIP flag. Almost
every proposition also names `Pure`, `HOL.HOL` or `HOL.Set`, which are
persistent and do move. Measured: of the 1,163,015 XOR-prefixed records, 23,000
mix WIP and persistent constituents and only **52** are wholly WIP and
stationary; **all 4,908 records naming a `Phi_BI.*` theory move.**

Some of those records are nonetheless dropped — not because of the WIP
constituent but because they also name a persistent theory that is out of
scope, `NTP4Verif.NTP4Verif` or `Auto_Sledgehammer.Auto_Sledgehammer`. They are
already counted in §C.
