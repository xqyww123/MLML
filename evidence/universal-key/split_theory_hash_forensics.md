# Split theory-name/hash forensics over the pre-re-key store

Read-only census run 2026-08-13 against `cslh19`, on
`~/.cache/Isabelle_Semantic_Embedding/semantics.lmdb.pre-rekey-20260813-170504`,
`~/.cache/Isabelle_Theory_Hash/theory_hash.lmdb.pre-rekey-20260813-170504`, and the
re-key run's surviving artefacts in `/tmp/rekey/`. Every LMDB environment was opened
`readonly=True, lock=False, subdir=True`. Nothing was written on `cslh19` outside `/tmp`.
Nothing in the repository was touched. The Isa-REPL port was never contacted.

Every number below is **exact** (a full walk of the 1,380,494-entry store, or a full read
of the 12,920-entry hash registry, or a full read of the 1,534-row drop list) unless the
line says otherwise. No figure in this report is estimated.

---

## Verdict

**The signature — one theory long name carrying two distinct *persistent* hashes, with
records standing on both — is present, and it is small and completely localised: 21 theory
long names, and 791 records out of 1,380,494 (0.0573%).** Thirteen of those names are AFP
theories, all of them in the `Rank_Nullity_Theorem` / `Gauss_Jordan` cone; the other eight
are this project's own tooling theories (`Auto_Sledgehammer`, `MathBench_Prover`,
`MathBench_ProverBase`, `Minilang`, `Minilang_AoA`, `Isabelle_RPC.Remote_Procedure_Calling`,
`Performant_Isabelle_ML`, `Semantic_Embedding`), where all but a handful of the records
involved are one-per-generation theory-status flags.

**But the thirteen AFP splits are demonstrably explained by content changing between two
separate collection runs, not by two theory values inside one process, and I can show this
rather than assume it.** Under the pre-re-key digest — `clear_lsb(xxhash128(file bytes ++
parent hashes))`, with the long name *not* in the digest — I reconstructed the superseded
hash of all twelve non-root theories on the single hypothesis that only
`afp-2026-05-13/thys/Rank_Nullity_Theorem/Miscellaneous.thy`'s bytes differed and every
other file was byte-identical to today's. **All 12 of 12 reproduced exactly.** The thirteen
names are the root plus twelve of its 79 descendants in the dependency graph. So the two
generations differ because one file's bytes differed, which is the innocent
across-runs explanation, and it matches what `THEORY_HASH_REKEY_PLAN.md` §1 D5 already
recorded (a local edit to that file, reverted on 2026-07-11).

**What this evidence cannot decide, stated plainly.**

1. *In-process versus across-runs, in general.* The store carries no per-record write
   timestamp. The only chronology anywhere is `theory_hash.lmdb`'s per-hash *last-touched*
   time, and last-touched moves forward every time a hash is re-registered — so a wide gap
   between two hashes of one name is uninformative about when the older one was minted. A
   *narrow* gap is suggestive of a single session, and I measured that too (below): of the
   841 names carrying two or more persistent hashes, 47 have two hashes last touched under
   an hour apart, but **none of those 47 has records standing on both hashes** — the
   smallest gap between two *record-carrying* hashes of one name is 76,651 s (21.3 hours),
   and for the thirteen AFP names it is 47 days.
2. *The failure mode where the file bytes are identical is structurally invisible here.*
   Under the pre-re-key digest the hash is a function of bytes only. Two distinct theory
   values built in one process from the same file and the same parents produce the **same**
   persistent hash. The stale `Universal_Key.cache` / constituents-cache hazard the
   2026-08-13 probe established is about the theory *value* going stale behind a name, and
   in the byte-identical case it leaves no trace in any hash. So "no split found" for a
   given name is not evidence that name was never dual-valued in one process — only that
   its bytes never differed.
3. *Records written under a stale cached hash are indistinguishable from records written
   honestly against an older generation.* Both look like "a record standing on the
   superseded hash of a live name". The 791 records below are consistent with either
   reading. What tips the thirteen AFP names toward the honest reading is circumstantial,
   not decisive: both generations carry their own `finished` theory-status record (a
   complete run, not a half-written one), and the two generations' hashes are separated by
   a real file edit that fully accounts for them.
4. *Names the store never spells out.* Only XOR-prefixed records carry theory long names.
   The store references 10,608 distinct persistent theory hashes but only 8,332 distinct
   names ever appear in a constituent list; the rest are named only by `theory_hash.lmdb`
   or not at all. For a hash the registry never recorded, a split under that name is
   simply not observable.

The re-key handled this population cleanly: of the 791, **749 were dropped and 42 kept**
(the revived EXPERIENCE records of D5). Of the 749 dropped, 736 were duplicates of a record
the current generation already holds and 13 were superseded theory-status flags whose
current counterpart migrated — so nothing of substance was lost to the split. And the
current store carries **zero** names with two persistent hashes (verified by a full walk of
the post-re-key `semantics.lmdb`), so the condition no longer exists going forward.

---

## 1. How a theory long name is associated with a hash

There are three places, and exactly one of them states the association directly.

**Directly, and only here: `theory_hash.lmdb`.** This is a separate LMDB store under its own
platformdirs root (`Isabelle_Theory_Hash`, see `isabelle_semantics.py:41-42`), keyed by the
16-byte theory hash, whose value is a msgpack pair `(long name, last-touched unix time)`.
`_load_theory_names` (`isabelle_semantics.py:59-71`) and `_load_theory_generations`
(`:545-563`) read it; the latter's docstring calls the per-name hash list exactly what it
is — a list of content **generations** of one name. Because it is keyed by hash, one name
can and does hold many entries. The pre-re-key copy has 12,920 entries; the post-re-key one
has 11,494.

**Indirectly, on XOR-prefixed records: `theory_constituents`.** Tuple index 5 of the
positional msgpack record (`semantics.py:112-122`, `:225-228`) is a list of
`(theory long name, 16-byte hash)` pairs. It is the *only* place inside `semantics.lmdb`
where a name and a hash sit side by side, and it is what let the re-key's D4 resolve
records off a collision-shared hash. It applies to tag bytes `{0x02, 0x12, 0x22, 0x32,
0x42, 0x08}` — the theorem/rule kinds plus EXPERIENCE (`universal_key.py:_XOR_PREFIXED_TAG_BYTES`).

**Not at all, for the other two key shapes.** A 16-byte key *is* a theory hash and is the
theory-status record (the "fully interpreted" flag; one per content generation). A 32-byte
key with any other tag byte is name-addressed: its first 16 bytes are the defining theory's
hash. Neither carries a long name; for both, the only way to a name is the registry above.

In the census below I therefore build the name→hash association as the union of the
registry and the constituent lists, and attribute name-addressed and theory-status records
to a name through the registry.

## 2. The split census, over the pre-re-key store

Store shape (exact, full walk): 1,380,494 entries = 1,163,015 XOR-prefixed + 206,010
name-addressed + 11,468 theory-status + 1 counter. Four of the XOR records carry an empty
constituent list (legitimate — the `_GLOBAL` experiences); none carries an absent one.
The store references 10,608 distinct persistent theory hashes and 886 distinct WIP hashes,
and spells out 8,332 distinct theory long names in constituent lists. Unioned with the
registry, the association covers **11,978 distinct theory long names**.

**Names carrying more than one hash of any kind: 870.**

**WIP/persistent pairing, separated out as asked.** 966 names carry a WIP hash (each name
has at most one — the WIP hash is FNV-1a-128 of the long name, so it is a function of the
name alone). 71 names carry both a WIP hash and at least one persistent hash. **29 of the
870 are exactly the expected "one WIP + one persistent" pattern** and are not the signature.

**Names carrying more than one *persistent* hash: 841.** These split three ways by whether
records actually stand on the hashes:

| | names |
|---|---|
| two or more persistent hashes, **each carrying records** — the signature | **21** |
| two or more persistent hashes, only one carrying records (the others are registry-only history) | 743 |
| two or more persistent hashes, none carrying any record | 77 |

The 743 and the 77 are worth naming for what they are: `theory_hash.lmdb` is an append-over
diagnostic cache that has been accumulating since March 2026, so it remembers every content
generation the machine ever hashed, including generations whose records were long since
superseded or never written. They are history, not footprint. 248 of the 743 are AFP
theories, 494 are Isabelle distribution theories under `contrib/Isabelle2025-2`, 1 is out of the
image. (I did not chase down why the distribution theories moved; a patch to any ancestor
propagates a new hash to its whole cone, which would account for a block that size, but
that is a hypothesis I did not test.)

## 3. Which theories, and AFP versus actively-edited

The 21 record-backed splits, with per-hash record counts and the registry's last-touched
time. "current" marks the hash that a fresh recomputation of the pre-re-key digest from
`/tmp/rekey/deps.tsv` produces today.

**Thirteen AFP theories** (all under `contrib/afp-2026-05-13/thys/`; all present in
`tools/Build_AFP_Image/afp_all4_theories.txt`), each with exactly two record-carrying
persistent hashes — one superseded, last touched 2026-06-25 07:36 UTC, one current, last
touched 2026-08-11 16:37–16:40 UTC:

| theory | superseded hash / records | current hash / records |
|---|---|---|
| `Rank_Nullity_Theorem.Miscellaneous` | `d2308fd1…` 282 | `8c1268aa…` 491 |
| `Rank_Nullity_Theorem.Fundamental_Subspaces` | `5ed43ab5…` 36 | `d0f9e90e…` 63 |
| `Rank_Nullity_Theorem.Dim_Formula` | `fa89a53b…` 1 | `2a602fd4…` 1 |
| `Gauss_Jordan.Matrix_To_IArray` | `5a82d24f…` 131 | `acc5ca96…` 234 |
| `Gauss_Jordan.Rref` | `505df1ab…` 111 | `540ad3a4…` 189 |
| `Gauss_Jordan.Gauss_Jordan` | `b413b8bc…` 108 | `96684934…` 102 |
| `Gauss_Jordan.Elementary_Operations` | `36379f5c…` 99 | `4630a43f…` 132 |
| `Gauss_Jordan.Linear_Maps` | `2a0bb9b2…` 89 | `c8bde01a…` 79 |
| `Gauss_Jordan.Gauss_Jordan_PA` | `da85377e…` 54 | `f67e8976…` 83 |
| `Gauss_Jordan.Determinants2` | `6497fed4…` 48 | `fc14de30…` 66 |
| `Gauss_Jordan.Gauss_Jordan_IArrays` | `44a838a6…` 40 | `a86870b3…` 65 |
| `Gauss_Jordan.Determinants_IArrays` | `167946e5…` 23 | `da2ee89b…` 24 |
| `Gauss_Jordan.Rank` | `e4c5a1ed…` 13 | `0c342dab…` 155 |

(Record counts here are *references*: an XOR record with several constituents is counted
once under each constituent. The de-duplicated record total is in §5.)

These are static-between-runs theories, so a split is the harder case to explain innocently
— which is why I tested it rather than asserting it. The test and its result are in the
verdict: assuming only `Rank_Nullity_Theorem/Miscellaneous.thy` differed reproduces all
twelve inherited superseded hashes byte for byte. Both generations of every one of the
thirteen carry their own theory-status record.

**Eight of this project's own theories**, none of them in the AFP tree and none of them held
by the `AFP-ALL-4` image, so there is no current hash to compare against:

- `MathBench_Prover.MathBench_Prover` — 19 persistent hashes in the registry, 3 carrying
  records (5 each: 4 constant records + 1 theory-status), last touched 2026-06-17, 06-18, 06-24.
- `Auto_Sledgehammer.Auto_Sledgehammer` — 11 persistent hashes, 4 carrying records
  (17, 1, 1, 1), last touched 2026-06-18 through 2026-08-12; the 17 are 13 theorems,
  1 intro rule, 1 constant, 1 theorem-collection and 1 status.
- `Minilang.Minilang` — 3 hashes, all carrying records (3, 2, 1).
- `MathBench_ProverBase.MathBench_ProverBase` — 6 hashes, 3 carrying one status record each.
- `Semantic_Embedding.Semantic_Embedding` — 5 hashes, 3 carrying one status record each.
- `Performant_Isabelle_ML.Performant_Isabelle_ML` — 5 hashes, 3 carrying one status record each.
- `Minilang_AoA.Minilang_AoA` — 4 hashes, 2 carrying one status record each.
- `Isabelle_RPC.Remote_Procedure_Calling` — 2 hashes, both carrying one status record each.

These are exactly the actively-edited theories where a split across runs is expected, and
the shape of the data agrees: with three exceptions the "extra" records are one status flag
per generation, which is what a per-generation status key produces by construction. Their
timestamps spread over June to August 2026, i.e. many separate sessions.

**The converse phenomenon, for completeness.** Ten hashes are shared by *two different*
long names under the pre-re-key scheme (two `.thy` files with identical bytes and identical
parent hashes): `Separation_Logic_Imperative_HOL`/`Van_Emde_Boas_Trees.Imperative_HOL_Add`,
`Superposition_Calculus`/`Typed_Ordered_Resolution.Relation_Extra`,
`Types_Tableaus_and_Goedels_God`/`Lowe_Ontological_Argument.Relations`, `HOLCF`/`HOLCF.HOLCF`,
`Restriction_Spaces-HOLCF`(×2), `HOL-CSP`/`HOL-CSP.HOL-CSP`,
`Intro_Dest_Elim`/`Conditional_Simplification.Reference_Prerequisites`,
`Core_SC_DOM`/`Core_DOM.Core_DOM_Basic_Datatypes`, `Core_SC_DOM`/`Core_DOM.Testing_Utils`,
`FocusStreamsCaseStudies`/`CryptoBasedCompositionalProperties.ListExtras`. 110 records stand
on them. This is the collision the whole re-key was performed to eliminate; it is not the
split signature.

## 4. The drop list, classified

All 1,534 rows of `/tmp/rekey/dropped_keys.tsv`, re-classified from first principles: for
each dropped key I recomputed whether its theory hash is reproducible from today's
dependency table, whether it is shared by two names, and — when it is neither — whether the
name it belongs to (from the record's own constituent list for XOR keys, from the registry
for the other two shapes) is a name the `AFP-ALL-4` image holds.

| key shape | verdict | rows |
|---|---|---|
| XOR-prefixed | **signature**: a constituent hash is a stale generation of a name the image holds | **635** |
| name-addressed | **signature**: the key's hash is a stale generation of a name the image holds | **101** |
| theory-status | **signature**: the key *is* a stale generation of a name the image holds | **13** |
| name-addressed | out of scope: the name is absent from the image | 425 |
| XOR-prefixed | out of scope: a constituent's name is absent from the image | 280 |
| theory-status | out of scope | 28 |
| name-addressed | standing on a shared hash, no name available to resolve it | 42 |
| theory-status | standing on a shared hash | 10 |
| | **total** | **1,534** |

So **749 of the 1,534 rows carry the signature** — 48.8%. They resolve to exactly thirteen
theories, and they are exactly the thirteen AFP theories of §3:
`Rank_Nullity_Theorem.Miscellaneous` 280, `Gauss_Jordan.Matrix_To_IArray` 131,
`Gauss_Jordan.Rref` 105, `Gauss_Jordan.Elementary_Operations` 94,
`Gauss_Jordan.Gauss_Jordan` 92, `Gauss_Jordan.Linear_Maps` 79,
`Gauss_Jordan.Gauss_Jordan_PA` 54, `Gauss_Jordan.Determinants2` 46,
`Gauss_Jordan.Gauss_Jordan_IArrays` 40, `Rank_Nullity_Theorem.Fundamental_Subspaces` 35,
`Gauss_Jordan.Determinants_IArrays` 23, `Gauss_Jordan.Rank` 13,
`Rank_Nullity_Theorem.Dim_Formula` 1. (Counts are per offending constituent, so an XOR
record with two stale constituents appears under both; the row total is 749.)

The other two populations are the ones the plan names. **733 out of scope** (425 + 280 + 28),
over thirteen theories that the `AFP-ALL-4` image does not hold — `NTP4Verif.NTP4Verif` 398,
`MathBench_ProverBase.Geo_Real2` 277, `Auto_Sledgehammer` 20, `MathBench_Prover` 15,
`Minilang` 6, `MathBench_ProverBase` / `Performant_Isabelle_ML` / `Semantic_Embedding` 3
each, `Minilang_Agent` / `Isabelle_RPC.Remote_Procedure_Calling` / `Minilang_AoA` 2 each,
`Isa_REPL` / `MiniF2F_MyProver` 1 each. **52 on a shared hash** (42 + 10), the D4 population.
These three classes reproduce `THEORY_HASH_REKEY_PLAN.md` §4's breakdown exactly
(733 / 52 / 13 / 736, where the plan's 13 + 736 = my 749).

## 5. Blast radius

De-duplicated per record (an XOR record counted once no matter how many of its constituents
are stale), over the full pre-re-key store:

| record class | count |
|---|---|
| every constituent on its current generation | 1,371,528 |
| **touches at least one superseded generation of a live name — the signature** | **791** |
| touches a theory the image does not hold | 733 |
| touches a hash shared by two names | 110 |
| wholly WIP | 7,327 |
| XOR with an empty constituent list | 4 |
| the global counter | 1 |
| **total** | **1,380,494** |

The 791 sum to 0.0573% of the store. By kind: 621 THEOREM (`0x02`), 100 CONSTANT (`0x01`),
42 EXPERIENCE (`0x08`), 13 theory-status, 11 introduction rules (`0x12`), 2 induction rules
(`0x32`), 1 elimination rule (`0x22`), 1 LOCALE (`0x05`).

**What the re-key did with them: 749 dropped, 42 kept.** The 42 kept are the EXPERIENCE
records revived under D5 — re-pointed by name to the current generation, which is also what
made them reachable again for the first time since the content changed. Of the 749 dropped,
736 landed on a key the current generation's record already occupies (so nothing unique was
lost) and 13 were theory-status flags whose current-generation counterpart migrated
normally. The genuine, unrecoverable loss from this population is **zero records**; the
plan's "genuine loss of 785" is entirely the out-of-scope 733 plus the shared-hash 52, both
of which are different problems from the split.

Every one of the 791 stands on a *minority* hash in the sense asked: for all thirteen AFP
names the superseded hash carries fewer records than the current one in eleven cases
(`Gauss_Jordan.Gauss_Jordan` 108 vs 102 and `Gauss_Jordan.Linear_Maps` 89 vs 79 are the two
where the older generation carries more references, because the June run harvested
EXPERIENCE records against them that the August run did not repeat).

## 6. Exactly what I ran

Local reads, no writes: `THEORY_HASH_REKEY_PLAN.md`,
`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/semantics.py`,
`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/isabelle_semantics.py`,
`contrib/Semantic_Embedding/migrate_theory_hash_rekey.py`,
`contrib/Isabelle_RPC/Isabelle_RPC_Host/theory_hash.py`,
`contrib/Isabelle_RPC/Isabelle_RPC_Host/universal_key.py`,
`tools/Build_AFP_Image/afp_all4_theories.txt`.

On `cslh19`, four scripts, all read-only, all writing only under `/tmp/rekey_forensics/`
(sources kept beside this report):

1. `census.py` → `/tmp/rekey_forensics/census.json`. Rebuilds the pre-re-key-scheme hash of
   all 10,598 theories from `/tmp/rekey/deps.tsv` (all files present, 0 missing); loads both
   `theory_hash.lmdb` registries; walks all 1,380,494 entries of the pre-re-key
   `semantics.lmdb`, unpacking every XOR record's constituent list; emits the per-name
   per-hash record counts and the split lists.
2. `drops.py` → `/tmp/rekey_forensics/drops.json`. Classifies all 1,534 rows of
   `/tmp/rekey/dropped_keys.tsv` against the recomputed hash table and the registry.
3. `footprint.py` → `/tmp/rekey_forensics/footprint.json`. Second full walk, de-duplicating
   per record instead of per constituent, and cross-checking each dropped/kept decision
   against the drop list; also computes the registry timestamp-gap distribution.
4. `gaps.py` → `/tmp/rekey_forensics/gaps.json`. Full per-name timestamp-gap list and the
   WIP/persistent pairing counts.
5. `prop.py`. The single-changed-file propagation test of the verdict: 12/12.

Two ad-hoc checks on `cslh19` (`/tmp/post.py`, `/tmp/post2.py`): full walks of the *current*
`semantics.lmdb` confirming 32 names carry two hashes and that all 32 are one persistent
plus one WIP — **zero names with two persistent hashes** in the current store.

Independent cross-checks that came out right and raise confidence in the pass, each
computed here from scratch and only afterwards compared with the plan: the store's 10,608
distinct referenced persistent hashes match `THEORY_HASH_REKEY_PLAN.md` §6 G1; the 733
out-of-scope records, the 110 standing on a shared hash and the 4 empty-constituent XOR
records match §4 and D4; my 791 superseded-bucket records splitting 749 dropped / 42 kept
matches D5's "749 of the 791 superseded-bucket records do have a surviving same-(kind, name)
record" and "42 are revived"; the post-re-key store's 1,378,960 entries equal 1,380,494
minus the 1,534 drop rows; and my drop-list classes 733 / 52 / 13 / 736 reproduce §4's four
populations.

One number of mine deliberately does **not** correspond to anything in the plan: my 7,327
"wholly WIP" records count every key shape, whereas §1's 52 counts wholly-WIP XOR records
only. They are different populations, not a disagreement.
