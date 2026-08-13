# Theories to re-interpret after the theory-hash re-key

Companion to `THEORY_HASH_REKEY_PLAN.md`. Scope: the `cslh19` store, migrated to
theory hashes that fold in the theory long name.

**This is the working list. Keep the status column current** — it is the only
place that says which of these have been done.

Derived on 2026-08-13 from the `AFP-ALL-4` image itself (all 10,598 theories it
holds, `Pure` included), not from the store: a pair of theories that share a
hash today is invisible in the store whenever only one side was ever
interpreted, so the store cannot produce this list.

Of 1,380,494 entries, **1,378,960 migrate and 1,534 (0.111%) are dropped**. Of
those 1,534, 736 are duplicates of a record that stays and 13 are superseded
theory-status records whose current generation is present, so the genuine loss
is **785**, and only the theories below need anything done.

## The list

Status values: `pending` · `done` · `n/a` (nothing to do, kept so the row is not
mistaken for an oversight).

### Group 1 — must be re-interpreted

Their records stood on a hash two theories shared, and the key carried nothing
else, so nothing can say which theory they belonged to. Re-interpretation is
the only way back. All are held by `AFP-ALL-4`, so one collection run covers
them; their theory-status records are among the dropped, so a collection that
reaches them re-enumerates without being told to.

| # | theory | shares its hash with | records to regenerate | status |
| --- | --- | --- | --- | --- |
| 1 | `Restriction_Spaces-HOLCF` | `Restriction_Spaces-HOLCF.Restriction_Spaces-HOLCF` | 17 | pending |
| 2 | `Restriction_Spaces-HOLCF.Restriction_Spaces-HOLCF` | `Restriction_Spaces-HOLCF` | (same 17) | pending |
| 3 | `Lowe_Ontological_Argument.Relations` | `Types_Tableaus_and_Goedels_God.Relations` | 16 | pending |
| 4 | `Types_Tableaus_and_Goedels_God.Relations` | `Lowe_Ontological_Argument.Relations` | (same 16) | pending |
| 5 | `Core_DOM.Core_DOM_Basic_Datatypes` | `Core_SC_DOM.Core_DOM_Basic_Datatypes` | 6 | pending |
| 6 | `Core_SC_DOM.Core_DOM_Basic_Datatypes` | `Core_DOM.Core_DOM_Basic_Datatypes` | (same 6) | pending |
| 7 | `Core_DOM.Testing_Utils` | `Core_SC_DOM.Testing_Utils` | 4 | pending |
| 8 | `Core_SC_DOM.Testing_Utils` | `Core_DOM.Testing_Utils` | (same 4) | pending |
| 9 | `CryptoBasedCompositionalProperties.ListExtras` | `FocusStreamsCaseStudies.ListExtras` | 4 | pending |
| 10 | `FocusStreamsCaseStudies.ListExtras` | `CryptoBasedCompositionalProperties.ListExtras` | (same 4) | pending |
| 11 | `Superposition_Calculus.Relation_Extra` | `Typed_Ordered_Resolution.Relation_Extra` | 1 | pending |
| 12 | `Typed_Ordered_Resolution.Relation_Extra` | `Superposition_Calculus.Relation_Extra` | (same 1) | pending |
| 13 | `Separation_Logic_Imperative_HOL.Imperative_HOL_Add` | `Van_Emde_Boas_Trees.Imperative_HOL_Add` | 1 | pending |
| 14 | `Van_Emde_Boas_Trees.Imperative_HOL_Add` | `Separation_Logic_Imperative_HOL.Imperative_HOL_Add` | (same 1) | pending |
| 15 | `Conditional_Simplification.Reference_Prerequisites` | `Intro_Dest_Elim.Reference_Prerequisites` | 1 | pending |
| 16 | `Intro_Dest_Elim.Reference_Prerequisites` | `Conditional_Simplification.Reference_Prerequisites` | (same 1) | pending |
| 17 | `HOLCF` | `HOLCF.HOLCF` | 1 status record only | n/a |
| 18 | `HOLCF.HOLCF` | `HOLCF` | 1 status record only | n/a |
| 19 | `HOL-CSP` | `HOL-CSP.HOL-CSP` | 1 status record only | n/a |
| 20 | `HOL-CSP.HOL-CSP` | `HOL-CSP` | 1 status record only | n/a |

Rows 17–20 are `n/a` because `HOLCF.thy` and `HOL-CSP.thy` are pure collector
theories — imports plus `default_sort` — that define **zero** entities and
appear in **zero** constituent lists. Their duplicate costs one theory-status
record and no LLM spend.

**Total to regenerate: 52 records over 16 theories**, of which 42 are entity
records and 10 are theory-status records.

### Group 2 — re-interpret only if we choose not to migrate them instead

`AFP-ALL-4` does not hold these, so their records could not be re-hashed and
were dropped. **Re-interpretation is the expensive fallback, not the plan**:
the records still exist in the untouched original store, so dumping a
dependency table from an image that does hold the theory and re-running the
migration's classification for those keys brings them across for no LLM spend.
Whichever route is taken, it must happen before anything triggers a collection
over these theories, because their theory-status records are gone and a
collection would re-interpret them at full price without asking.

| # | theory | records dropped | which image holds it | status |
| --- | --- | --- | --- | --- |
| 21 | `NTP4Verif.NTP4Verif` | 398 | `NTP4Verif` | pending |
| 22 | `MathBench_ProverBase.Geo_Real2` | 277 | `MathBench_ProverBase` | pending |
| 23 | `Auto_Sledgehammer.Auto_Sledgehammer` | 20 | `Auto_Sledgehammer` | pending |
| 24 | `MathBench_Prover.MathBench_Prover` | 15 | `MathBench_Prover` | pending |
| 25 | `Minilang.Minilang` | 6 | `Minilang` | pending |
| 26 | `MathBench_ProverBase.MathBench_ProverBase` | 3 | `MathBench_ProverBase` | pending |
| 27 | `Performant_Isabelle_ML.Performant_Isabelle_ML` | 3 | `Performant_Isabelle_ML` | pending |
| 28 | `Semantic_Embedding.Semantic_Embedding` | 3 | `Semantic_Embedding` | pending |
| 29 | `Isabelle_RPC.Remote_Procedure_Calling` | 2 | `Isabelle_RPC` | pending |
| 30 | `Minilang_Agent.Minilang_Agent` | 2 | `Minilang_Agent` | pending |
| 31 | `Minilang_AoA.Minilang_AoA` | 2 | `Minilang_AoA` | pending |
| 32 | `Isa_REPL.Isa_REPL` | 1 | `Isa_REPL` | pending |
| 33 | `MiniF2F_MyProver.MiniF2F_MyProver` | 1 | `MiniF2F_MyProver` | pending |

**Total 733 records over 13 theories**, counted per offending theory, so a
record naming two of them appears in two rows. 28 of the 733 are theory-status
records; see the plan's §4 for why keeping the flag would have been worse than
dropping it.

One of these 733 is an **EXPERIENCE** record (it names `Minilang.Minilang`), and
it is the single entry in the whole drop set that **no re-interpretation can
recreate** — experiences are agent-authored, written during proof search rather
than by theory interpretation. Migrating row 25 rather than re-interpreting it
is the only way to keep it.

### Nothing to do

- **736 records off a superseded content generation** (13 theories under
  `Gauss_Jordan` and `Rank_Nullity_Theorem`, whose `.thy` bytes had changed when
  those records were written). Every one is a duplicate of a record that stays:
  re-pointing it by long name to the current generation lands it on a key the
  current generation's record already holds. Measured by running the migration
  with the revival rule widened to exactly that (plan D5a).
- **13 superseded theory-status records** of theories the image does hold. The
  current generation carries its own.
- **42 EXPERIENCE records** off that same superseded generation are *not*
  dropped: plan D5 revives them by re-pointing their constituents by name, and
  a per-record check of all 775 references they make confirmed that is sound.

## Why two theories shared a hash at all

Seven of the ten groups are genuinely distinct `.thy` files that happen to be
byte identical. The other three are **one `.thy` file loaded under two long
names** — a session-qualified name and a dotless global one — so Isabelle holds
two distinct theory values for one file:

| file | the two names |
| --- | --- |
| `afp/thys/Restriction_Spaces-Examples/HOLCF/Restriction_Spaces-HOLCF.thy` | `Restriction_Spaces-HOLCF` / `Restriction_Spaces-HOLCF.Restriction_Spaces-HOLCF` |
| `Isabelle2025-2/src/HOL/HOLCF/HOLCF.thy` | `HOLCF` / `HOLCF.HOLCF` |
| `afp/thys/HOL-CSP/HOL-CSP.thy` | `HOL-CSP` / `HOL-CSP.HOL-CSP` |

Two of those three are artefacts of the image generator:
`tools/Build_AFP_Image/AFP-DEP0/all_theories.lst:825,962` lists the
session-qualified spelling of a theory declared `(global)`, while the `sessions`
block pulls the same file in under its bare name, and deleting those two lines
removes both duplicates. `HOL-CSP.HOL-CSP` is not removable — it comes from AFP
source, `CSP_RefTK/Process_norm.thy:48`.

After the migration each name gets its own hash and every pair separates, so
this list does not grow again.

## What was rescued rather than re-interpreted

**58 theorem records standing on a shared hash are kept**, because a theorem
record stores its constituents as (long name, hash) pairs — the name is on
record and resolves the collision exactly. 41 name
`CryptoBasedCompositionalProperties.ListExtras`, 13
`Core_DOM.Core_DOM_Basic_Datatypes`, 4 `Core_SC_DOM.Core_DOM_Basic_Datatypes`.
An earlier revision of this document put them in the re-interpretation set,
giving 110 dropped where the true figure is 52.

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
already counted in Group 2.
