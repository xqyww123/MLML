# Theory-hash re-key: implementation plan

Folds the theory long name into the persistent theory hash, so that two theories
sharing a base name stop sharing an identity. Companion to
`BUG_UNIVERSAL_KEY_SHORT_NAME_FIX_PLAN.md`; the list of theories needing
re-interpretation is `THEORY_HASH_REKEY_REINTERPRET_LIST.md`.

Authoritative data: the `cslh19` user store. It has no system layer installed.

Reviewed 2026-08-13 by a four-lens adversarial team plus a refutation round.
All decisions below are settled; §9 records the one engineering question still
to be verified.

## 1. The change

A persistent theory's hash becomes

```
clear_lsb( xxhash128( long_name ++ 0x00 ++ file bytes ++ each parent's new hash ) )
```

Parents contribute their **new** hashes, so the name propagates down the ancestor
DAG. The `0x00` separator makes the name/file boundary unambiguous — a theory
long name cannot contain a NUL, while file bytes are variable length.

The WIP hash function is unchanged: it is FNV-128 of the long name with the LSB
set, already name-addressed. **This does not mean WIP records stay put.** A
theorem key's 16-byte prefix is the XOR of *all* its constituents' hashes and
only bit 0 of byte 0 carries the WIP flag, so a record whose constituent list
mixes WIP and persistent theories moves with its persistent constituents.
Measured: of 1,163,015 XOR-prefixed records, 1,139,963 are all-persistent,
23,000 are mixed, and only **52** are wholly WIP and genuinely stationary. The
migration rule for the XOR class is unconditional — rewrite every constituent
hash, then recompute the prefix — with no WIP exemption anywhere in it.

### Decisions taken

- **D1.** Recursive folding (parents pass their new hashes), not a second hash
  layered on today's value.
- **D2.** Digest layout `long_name ++ 0x00 ++ file bytes ++ parent hashes`.
- **D3.** Records whose theory hash cannot be recomputed are **discarded**,
  except as D5 provides.
- **D4.** Records under a hash shared by two theories are **discarded** and those
  theories re-interpreted (list: `THEORY_HASH_REKEY_REINTERPRET_LIST.md`) —
  **but only those that carry nothing but the hash.** An earlier revision of
  this plan said a shared hash makes a record unattributable, full stop. That
  is true of a name-addressed key and of a theory-status key, whose 16-byte
  prefix is all they have. It is false of an XOR-prefixed record, which stores
  its constituents as (long name, hash) pairs: the long name is on record and
  resolves the collision exactly, with nothing guessed. Measured on the
  authoritative store: of the 110 records standing on a shared hash, **58 are
  theorem records carrying the name and are rescued** (41 naming
  `CryptoBasedCompositionalProperties.ListExtras`, 13
  `Core_DOM.Core_DOM_Basic_Datatypes`, 4 `Core_SC_DOM.Core_DOM_Basic_Datatypes`),
  and the remaining **52 — 42 name-addressed and 10 theory-status — are
  discarded**. The re-interpretation list is unchanged in *which* theories it
  names; only the record counts drop.
- **D5.** The 43 EXPERIENCE records inside the drop set are **not** treated like
  the rest. They are agent-authored — written by the AoA / missing-lemma
  pipeline during proof search, not by theory interpretation — so no
  re-interpretation can recreate them. **42 are revived**: their constituent
  list carries theory long names, so a constituent naming a theory the image
  *does* hold, merely at a superseded content generation, is re-pointed by name
  to the current generation and the XOR prefix recomputed. That also makes them
  reachable for the first time since the content changed. **One is dropped**,
  its constituent naming `Minilang.Minilang`, which the image does not hold.
  The rule is deliberately narrow — EXPERIENCE kind only, superseded generation
  only — because 749 of the 791 superseded-bucket records *do* have a surviving
  same-(kind, name) record and reviving those would duplicate them, and because
  reviving a shared-hash record would defeat D4.
  **The outstanding check has been run, and all 42 pass.** The worry was that
  `theory_constituents` drives *availability* — the list asserts "this strategy
  applies when these theories are loaded" — and these 42 were harvested against
  the theories' **old** content, so re-pointing them at the current generation
  asserts they still apply. Measured: the content change was a single edited
  file, `afp-2026-05-13/thys/Rank_Nullity_Theorem/Miscellaneous.thy`, whose
  bytes are now md5-identical to the stock AFP release (the local edit was
  reverted on 2026-07-11); the other eleven affected theories merely inherited
  a new hash through the parent chain. Both generations of every affected
  theory carry a `finished=True` status record, and their entity inventories
  are set-identical — 166 names against 166 for `Miscellaneous`, 19 against 19
  for `Fundamental_Subspaces`. Across the whole store the *only* records
  orphaned by that change are these 42. Resolving all 775 references the 42
  make (673 identifiers plus 102 goal patterns) inside `AFP-ALL-4` found zero
  identifiers that look like a library name and cannot be found. Revive all 42.
- **D5a.** Reviving *ordinary* records off a superseded generation was measured
  and is **provably empty**, so the narrowness of D5 costs nothing. Running the
  migration with the revival rule widened to every record whose superseded
  constituents are named (`--rescue-superseded all`) produces **the identical
  set of 1,534 dropped keys**: all 635 ordinary XOR records and all 101
  name-addressed ones land on a key a live record already holds, i.e. every one
  of them is a duplicate of the theory's current generation. The narrow rule
  and the wide rule cannot be told apart in the result.
- **D6.** The dependency table is dumped from `AFP-ALL-4` **only**. Theories that
  image does not hold get no new hash, so their records — 734 of them, including
  the thirteen theory-status records named in §4 — are dropped rather than
  rescued by dumping the extra images (`MathBench_Prover`, `NTP4Verif`) whose
  cones would cover them.
- **D7.** The migration **builds new environments beside the old ones and swaps
  whole directories at the end**. It never mutates a live store in place. The
  untouched original is therefore the backup, the staging build is the dry run,
  and re-running from the original is what makes the migration idempotent.
- **D8.** **No `SCHEMA_VERSION` bump.** Part B's D3 — "no key-scheme marker, no
  `SCHEMA_VERSION` bump, no CI key-provenance gate, no publication freeze" —
  stands unchanged.
- **D9.** `template_uk` is fixed at its producer and then recomputed, not
  patched in place (§5). Neither part belongs to this migration.
- **D10.** The `infra_filter` defects found along the way are a **separate
  project, after this migration** (§8).
- **D11.** Every write on `cslh19` needs the user's approval for that specific
  run.

## 2. Code changes

**`contrib/Isabelle_RPC/Isabelle_RPC_Host/theory_hash.py`.** `theory_xxhash128`
(`:19-30`) takes the long name and updates the digest with `long_name`, `b"\0"`,
the file bytes, then the parent hashes. It also clears byte 0's LSB before
returning, so that the clearing has exactly one implementation — the migration
script imports this same function, and a one-byte disagreement between the live
code and the migration would silently mis-key the whole store. The RPC handler
`_theory_xxhash128` (`:85-90`) destructures a 2-tuple and must gain the third
field; missing it raises on the first theory, so that failure is loud.

**`contrib/Isabelle_RPC/Tools/theory_hash.ML`.** The command's `arg_schema`
(`:62-66`) gains a string field; the call site (`:178-179`) passes
`Context.theory_long_name thy`. The parent recursion at `:177` is unchanged —
it already passes `hash_of` of each parent, which is now the new hash. Drop the
LSB clearing at `:189`, now done in Python.

**Reference docs that state the RPC signature** and would otherwise go stale
silently, since nothing executes them:
`contrib/Isabelle_RPC/.claude/skills/isabelle-rpc/references/registry.md:21` and
`references/modules.md:108`.

**`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/isabelle_semantics.py`.**
`fsck`'s orphan-vector count (`_count_vectors_with_no_visible_record`) becomes a
**warning above 10,000 and is silent below**. It does not enter `problems` and
does not change the exit code — a modest residue of orphan vectors is normal,
while a mis-keyed vector store yields ~1.37 M and must be impossible to miss.
Because the exit code is unchanged, G7 cannot rely on it; the migration carries
its own vector gate (§6, G4).

## 3. The migration table

Built offline from a table of `(theory long name, .thy path, ordered parents)`
dumped out of the `AFP-ALL-4` image, which holds 10,598 theories including
`Pure`. The names in that table are `Context.theory_long_name` of real theory
values and the parent column is resolved long names, not import strings: the
dump reads `map Context.theory_long_name (Theory.parents_of thy)`, and the
loaded-theory graph keys nodes the same way (`Pure/Thy/thy_info.ML:199`). Where
one `.thy` file appears under two names, those are two distinct theory values,
and each child's parent column names the value it was actually built on — there
is nothing for the migration to guess.

Recomputing **today's** hash from that table reproduces the stored hashes
exactly, which is what establishes that the reconstruction of the file paths,
the parent sets and their order is faithful. It says nothing about the long
name, which today's digest does not contain; the name's warrant is the code fact
above, and the check that the two implementations agree on it is G4.

Re-dump the table immediately before the migration run rather than reusing one
from disk, and run G1 over it.

## 4. What moves, and what is dropped

Per D7 the migration writes new environments and swaps at the end. Four stores.

**`semantics.lmdb`** (1.8 GB, 1,380,494 entries, no tombstones): 1,163,015
XOR-prefixed records, 206,010 name-addressed, 11,468 theory-status, 1 counter.
Keys are recomputed, and four value fields carry universal keys or theory
hashes and must be rewritten with them:

- `theory_constituents` — the hashes in the (long name, hash) pairs, after which
  the key's XOR prefix is recomputed from the new hashes;
- `locale_uk` — 190,550 references, all name-addressed shape, prefix
  substitution, zero dangling today;
- `deps` — 201,009 references, name-addressed shape, prefix substitution.
  40,036 of them already dangle today; the migration must not increase that;
- `template_uk` — 174,966 references, XOR shape, so no prefix substitution is
  possible. The 119,287 that resolve to a live record today are re-keyed through
  the per-record old-key → new-key map; the 55,679 that already dangle are left
  exactly as they are, and are repaired later by §5.

The counter (`b"\xf0"`, one byte) is not a record and is copied across
unchanged; every full-store walk in the codebase discriminates it by length.

**`vector_Qwen__Qwen3-Embedding-8B.lmdb`** (16 GB, 1,369,749 entries): keys only,
values copied verbatim. Its keys are the same universal keys, so it rides the
**per-record old-key → new-key map**, not the theory-hash table — 1,163,015 of
its entity keys are XOR-prefixed and their prefixes are not theory hashes. Its
723 sixteen-byte entries are embed-status keys, which *are* theory hashes and go
through the theory table; losing them would make `is_thy_embedded` false
everywhere and discard the token ledger. Its 8,908 empty values are vector
tombstones and copy verbatim to the new key.

**`theory_hash.lmdb`** (3.3 MB, 12,920 hash → name entries): re-keyed with the
theory table. For each of the 10 collapsed groups this store holds a single
entry (one hash, one arbitrarily-surviving name), so re-keying can only place it
under one of the two successors; the partner is left with no entry. That is
acceptable — the store is a rebuildable diagnostic cache — but the run should
report it rather than let it pass unnoticed.

**`experience_index.lmdb`** (405 buckets, 6,862 distinct experience keys — every
experience in the store): not migrated. It is a pure derived view of the
EXPERIENCE records, so `isabelle-semantics reindex` after the migration is both
simpler and safer than rewriting it.

**The experience corpus is the most valuable thing in the store**, since no
interpretation run can recreate it, so its fate is spelled out in full. Of the
**6,862** EXPERIENCE records: 6,765 have an all-persistent constituent list, 41
are mixed, 52 are wholly WIP, and 4 have an empty constituent list (their key
prefix is the all-zero `xor_theory_prefix([])`, and the index files them under
its `_GLOBAL` sentinel bucket). Under this plan **6,819 migrate** — of which the
52 wholly-WIP and the 4 constituent-less ones keep their exact key, since they
have no persistent constituent to re-hash — **42 are revived by D5**, and **1 is
dropped**.

Nothing else stores universal keys: `embed_cache/` is keyed by text hash,
`AoA_Collected/retrieval_training.db` stores entity full names, and Isa-Mini's
`aoa_proof_cache.db` is keyed by goal hash.

**Migrated: 1,378,960. Dropped: 1,534 records (0.111%)** — measured by running
the migration script's `plan` phase against the authoritative store, not
estimated. The two figures sum to the store's 1,380,494 entries, which is G3.

The 1,534 break down into four populations, and only the first two are a loss:

- **733 out of scope** (D6): 425 name-addressed, 280 XOR-prefixed and 28
  theory-status records whose theory `AFP-ALL-4` does not hold. Thirteen
  theories, dominated by `NTP4Verif.NTP4Verif` (398) and
  `MathBench_ProverBase.Geo_Real2` (277); the rest is our own tooling —
  `Auto_Sledgehammer` 20, `MathBench_Prover` 15, `Minilang` 6,
  `MathBench_ProverBase` / `Performant_Isabelle_ML` / `Semantic_Embedding` 3
  each, `Minilang_Agent` / `Minilang_AoA` / `Isabelle_RPC` 2 each, `Isa_REPL` /
  `MiniF2F_MyProver` 1 each.
- **52 standing on a shared hash with no name to resolve it** (D4): 42
  name-addressed and 10 theory-status.
- **13 theory-status records of a superseded content generation** of a theory
  the image does hold. Not a loss: the current generation carries its own
  status record, which migrates.
- **736 duplicates of a record that stays** (D5a): 635 XOR-prefixed and 101
  name-addressed records off a superseded generation, each landing on a key the
  current generation's record already holds.

So the genuine loss is **785 records, 0.057% of the store**.

**51 of the dropped records are theory-status records**, i.e. the flag saying a
theory is fully interpreted. 28 of them are out of scope, spread over thirteen
theories that are almost all our own tooling — `Auto_Sledgehammer` 4,
`MathBench_Prover` / `MathBench_ProverBase` / `Minilang` /
`Performant_Isabelle_ML` / `Semantic_Embedding` 3 each,
`Isabelle_RPC.Remote_Procedure_Calling` / `Minilang_AoA` 2 each, and
`Isa_REPL` / `MiniF2F_MyProver` / `Minilang_Agent` / `NTP4Verif` /
`MathBench_ProverBase.Geo_Real2` 1 each. (A theory has more than one because
each content generation gets its own status record.) The remaining 23 are 10
under a shared hash and 13 belonging to a superseded generation of a theory the
image does hold.

Dropping the 28 arms a full-price re-interpretation of those thirteen theories
on the next collection that covers them. The drop is forced by D3 — the key is
a hash that cannot be recomputed, so there is nowhere to write the flag — and
keeping the flag would in any case assert that a theory is fully interpreted
while its entity records are gone. Part B's §B.6 policy of preserving
`finished` for out-of-cone theories therefore does **not** apply here; that is a
deliberate divergence, not an oversight. The 13 superseded ones cost nothing:
the current generation carries its own.

## 5. `template_uk`: fix the producer, then recompute

55,679 of the 174,966 `template_uk` references point at a key absent from the
store. For the bulk of them the template is the locale-level form `Thy.L.foo` of
a type-class fact, which `infra_filter` excludes **by design** — so the pointer
names an entity that was never stored and never will be. Neither part of the fix
belongs to this migration.

**(a) Fix the producer.** In `build_entries` (`semantic_store.ML:704-709`),
when the template's locale is a type class — ask `Class.is_class`, never the
string `_class` — point `template_uk` at the class-level member `Thy.L_class.foo`
instead of the locale-level one, and store nothing where that member *is* the
referring record itself.

This is where the value actually matters, and it is not the stored field:
`sem_of` (`:757`, used at `:795`) resolves the key **live** to put
"Template meaning: …" into the interpretation prompt, and today that line is
simply lost for every type-class instance. Fixing the producer also makes the
fix durable — `write_answer` (`semantic_interpretation.py:372-378`) writes the
freshly-computed provenance back over the stored one on every interpretation, so
any after-the-fact patch of the stored field is reverted on next collection.

**(b) Recompute the existing records with the same code.** `build_entries`
computes provenance with **no LLM call** — the model only writes
interpretations — so a provenance-only traversal is cheap, and it rides Part B's
dump, which already walks the whole cone. Using the same code for both gives one
definition of correct, and avoids every hazard an after-the-fact patch carries:
name-based reverse engineering, homonym ambiguity across developments, empty
qualifiers, and drift in the key's tag.

Scheduling: (a) belongs with the §8 interpretation-pipeline work, (b) with
Part B. Nothing here blocks the migration; the field has no reader today.

## 6. Gates

Run against the staged store before the swap — **all of them, G7 included**.
That is what the staging build is for, and nothing forces G7 to wait: an
earlier revision of §9.6 put it after the swap, contradicting this sentence for
no reason.

`SEMANTIC_DB_DIR=<staging>` moves the semantic databases together
(`_paths.py`), which is what lets the cross-store checks run before anything
irreversible happens — but **it does not move `theory_hash.lmdb`**. That store
lives under a different platformdirs root (`Isabelle_Theory_Hash`) with no
environment override at all, so anything reading it through the library reads
the live one. The migration takes `--src-theory-hash` and writes its successor
into `--dest` for exactly that reason, and the gates are told where the staged
copy is rather than inferring it.

Implemented in `migrate_theory_hash_rekey.py`; the numbers quoted below are
what its `plan` phase reports against the authoritative store.

- **G1.** Recompute today's hashes from a fresh table; for every theory the
  store references and the image holds, the recomputed hash must be among the
  hashes the store carries for that name. **Exhaustive over all 10,608
  persistent theory hashes the store references**, not only the 7,943 that
  appear in a constituent list — 2,649 theory names occur solely as a
  name-addressed key prefix or a theory-status key, covering 217,478 records
  (15.75% of the store).

  Driven by **name**, not by hash. Phrasing it as "every stored hash must equal
  the recomputed one" is wrong and was the first thing the gate itself caught:
  a theory whose content changed since some records were written is referenced
  under *both* generations, and the superseded hash cannot equal today's
  recomputation by construction. Measured on the authoritative store: 10,567
  theories checked, **0 whose current hash the table fails to reproduce**, 13
  superseded generations referenced, 28 referenced theories the image does not
  hold. Any failure to reproduce stops the run.

  G1 is also what carries most of G4's weight. The stored hashes it reproduces
  were minted by the live ML through `get_theory_path` and `Theory.parents_of`,
  so reproducing them proves the table's file paths, parent sets and parent
  order are exactly what the live code feeds Python. What G1 cannot see is the
  long name, which today's digest does not contain.
- **G2.** The new-hash table must be injective, and must not intersect the set of
  old hashes still in use. (Both hold on the current data: 0 collisions, 0
  overlap.)
- **G3.** Record counts: migrated + dropped = 1,380,494, the dropped set equal to
  the explicit key list produced before the run, and **the destination stores'
  entry counts equal to what the classification says they should be**.

  That last clause is the one the whole `gates` subcommand rests on, and it is
  worth more than the "two old keys overwriting one new key" case it was
  written for — that case is already stopped twice, by `overwrite=False` at
  write time and by the collision check before any write. Its real work is that
  **every other check over the destination is a predicate on whatever keys
  happen to be there**, not a comparison against the intended set. `semantics.lmdb`
  is built in a single transaction, so a kill leaves it empty; the vector store
  is not, committing every 200,000 entries across an hours-long run, so a kill
  leaves a valid, self-consistent, truncated store — and a subset test over one
  only looks cleaner the more data is missing. The counts are the only thing
  that sees it. `apply` additionally refuses a non-empty `--dest`, which is the
  other route to two generations of records sitting side by side, each
  self-consistent, with every downstream gate passing.
- **G4.** Live-code agreement: run the new code in Isabelle and require the
  hashes it mints to equal the ones the migration script computed. This is the
  only check that the two implementations agree. Two halves, and they cost very
  different things:
  - Already done, at small scale: a purpose-built session (parent `HOL`,
    `Isabelle_RPC` loaded from source, no existing heap touched) hashed `Pure`,
    `Performant_Isabelle_ML.Performant_Isabelle_ML`,
    `Isabelle_RPC.Remote_Procedure_Calling` and the test theory itself through
    the live ML and the live RPC host, and all four agreed with the migration
    script's Python **byte for byte**. That is the whole of what is new — the
    argument the ML passes, the place Python folds it in, and the LSB — and
    none of it varies with the number of theories.
  - **Exhaustive over the migration table**, and it is cheap. `AFP-ALL-4` does
    **not** contain `Isabelle_RPC`: its ROOT chain, `AFP-ALL-4` → `AFP-ALL-3` →
    … → `AFP-DEP1-21`, names AFP sessions only. `repl_server.sh` builds a
    wrapper `REPL$$ = AFP-ALL-4 + sessions Isa_REPL Auto_Sledgehammer`, and a
    session named under `sessions` rather than as the parent is loaded **from
    source** — so `theory_hash.ML` is recompiled on every REPL start and no
    image anywhere has it frozen in. Nothing needs a 60-hour rebuild, and
    restarting the REPL is the whole of the deployment.

    G4 is therefore its own wrapper session on the same pattern, written out in
    §9.8 so it can be rebuilt from nothing. That is the live code, over all
    10,598 theories, for the cost of one small heap.
    `migrate_theory_hash_rekey.py verify-live --hashes FILE` consumes its dump.

  Additionally: every key in the migrated vector store must equal a key in the
  migrated record store.
- **G5.** No old hash survives anywhere in the new store — not as a key prefix,
  not as a 16-byte key, and not inside any `theory_constituents`, `locale_uk`
  or `deps` value — **and every persistent constituent's recorded hash is the
  one its recorded name maps to.**

  "Nowhere" is the headline, not the letter, and the gate as implemented says
  so: a `locale_uk` or `deps` entry whose *target theory* was itself dropped
  has nowhere to point, so it dangles either way and its stale prefix is
  reported in a separate bucket rather than counted as a failure. Measured on
  the migrated store, that bucket holds **3 `locale_uk` references**, all in
  `Restriction_Spaces-HOLCF` type-class instance records pointing at locale
  records dropped under D4. They cannot mis-resolve — G2 proves the new and old
  hash sets are disjoint — and re-interpreting that theory rewrites them.

  `template_uk` is **not** in that list, and an earlier revision wrongly put it
  there. It is a full universal key whose 16-byte prefix is an XOR of
  constituent hashes, not any one theory's hash, so "does it contain an old
  hash" is not a question that can be asked of it. The only staleness test that
  exists for an XOR-shaped pointer is whether it resolves to a live record, and
  that is G6's job. The 55,679 deliberately-untouched dangling values are
  listed rather than passing silently.

  The name-cross-examines-hash clause is the only non-circular check here, and
  it was added after the review. Recomputing the XOR prefix from the constituent
  list proves nothing on its own: the list and the key come out of the same
  `_map_hash` calls, so they agree even when the hash is wrong — and `_map_hash`
  resolves through the hash, discarding the name the record carries. Since
  constituents are stored as (long name, hash) pairs, `h == tab.new[n]` costs
  nothing and catches exactly the case key/value agreement cannot: a record
  whose key and value are mutually consistent and both name the wrong theory.

  This is otherwise **the only gate that inspects the rewritten value fields**:
  G1–G4 never open a record, G3 counts them, and `fsck`'s one relevant check
  ties the key to `theory_constituents` alone, by recomputing from the value the
  migration itself wrote. One cursor walk catches a skipped record class, a
  forgotten field, and a partially-rewritten field.
- **G6.** Dangling-reference counts must not grow **beyond what dropping records
  forces**. The bound for each of `locale_uk`, `deps` and `template_uk` is the
  source store's own count **plus the number of references whose target is in
  the drop set**, both measured in the same run rather than quoted from this
  document.

  An earlier revision gave the bound as the source count alone — `locale_uk` 0,
  `deps` 40,036, `template_uk` 55,679 — and that is wrong: a reference pointing
  into one of the 1,534 dropped records necessarily dangles afterwards, so a
  correct run must exceed those numbers. Implementing the bound as written
  would have produced a gate that fails every correct migration.

  G5 proves nothing stale survived; G6 proves nothing was pointed somewhere new
  and wrong.
- **G7.** `isabelle-semantics reindex`, then `fsck` clean, **against the staging
  directory, before the swap** — `experience_index.lmdb` lives under
  `SEMANTIC_DB_DIR`, so nothing forces this to wait, and running it first means
  the swap moves a set that already includes a freshly built index.

  `reindex` before `fsck`, in that order: all 6,862 experience records move, so
  running `fsck` first would report 6,862 missing plus 6,862 stale index entries
  and exit 1 on a perfectly correct migration.

  Confirm that **no orphan-vector alarm appears**, rather than reading a line
  for a number. Per §2 that count is report-only by design and stays out of the
  exit code; below the threshold nothing is printed at all, so the absence of
  the alarm is the success signal. The migration carries its own vector gate
  (G3's counts) and does not lean on `fsck` for this.

Disk: the old pair (1.8 GB + 16 GB) plus the new pair is **~35.6 GB against 87 GB
free**. Rollback is Part B §B.9's procedure: move all four environments back
together — never a subset — revert the code changes, and restart every REPL and
RPC host, since ML memoizes hashes per process and a survivor would hold
new-scheme hashes over an old-scheme store.

Preconditions for the run, per Part B §B.2: no process holds `semantics.lmdb`,
any `vector_*.lmdb`, `experience_index.lmdb` or `theory_hash.lmdb` — verify with
`fuser`/`lsof`, and never connect to the REPL port, which kills the server. The
migration script must open all four paths itself and must not touch
`open_theory_hash_store` or `Semantic_DB`, since py-lmdb refuses to open one
environment twice in a process.

## 7. Order of work

The re-key runs **before** Part B of the short-name fix plan. Part B's join is
by `key[16:]`, which contains no theory hash and is unaffected; but its dump
runs the new code and would emit new hashes, so a store that is still keyed the
old way makes the join harder for no benefit.

## 8. Deferred: the `infra_filter` defects

Confirmed by measurement in `AFP-ALL-4` (`is_infra_thm`/`is_infra_const` called
directly through `Infra_Filter.gen_infra_filters`), to be fixed **after** this
migration, since fixing them means re-enumerating and re-interpreting the
affected theories, which costs LLM budget.

- **`has_class_variant` infers "L is a type class" from the string `_class`.**
  `Class.is_class thy "Ring.cring"` is false — there is no type class named
  `cring` in the image — yet `Elliptic_Locale.cring_class.pdouble` exists,
  because `HOL/Decision_Procs/Algebra_Aux.thy:286` writes
  `interpretation cring_class: cring …` with a human-chosen prefix. The rule
  therefore deletes the general locale constant and keeps the specialization,
  taking all 20 `Elliptic_Locale.cring.*` facts with it. Fix: ask
  `Class.is_class`, and derive the class prefix with `Class.class_prefix`
  (`= Logic.const_of_class o Long_Name.base_name`), the very function
  `class_declaration.ML:295` uses to create the name path. **This fix does not
  bring the type-class templates back** — excluding the locale-level twin of a
  genuine class is the rule's intended behaviour, and only ~500 of the 55,679
  dangling references are misfire victims.
- **The `Abs_`/`Rep_` base-name test hits locale predicates.** Intended for
  typedef morphisms, it fires on the predicate constant `Abs_Int1.Abs_Int`, so
  7 of that locale's 9 facts die and only the two `.cong` rules survive. Fix:
  ask `Typedef.get_info_global` instead of the name.
- **An infra session poisons other sessions transitively.** `EC_Common` is not
  infrastructure, but four of its ancestors are in `HOL-Decision_Procs`, so
  every fact mentioning `Algebra_Aux.of_integer` / `of_natural` / `m_div` is
  dropped: of its 15 `field` lemmas the filter rejects 12, and the store holds
  exactly the other 3. Fix: separate "this entity does not deserve a record"
  from "any theorem mentioning it is worthless" — today one rule does both,
  through `Term.exists_Const is_internal_constant`.

The visible symptom is only 505 dangling references. The real loss is unmeasured:
an entity dropped where no instance of it happens to be stored leaves no trace at
all, so scoping that is the first task of the follow-up project.

## 9. Execution

The migration is
`contrib/Semantic_Embedding/migrate_theory_hash_rekey.py`, with four
subcommands: `plan` (tables, G1, G2, the classification and the explicit
drop-key list — opens every store read-only and writes nothing), `apply`
(builds the three new stores under `--dest`, then G3, G5, G6), `gates` (the
same gates against an already-built `--dest`) and `verify-live` (G4's live
half). `ISABELLE_RPC_PATH` says which checkout the shared `theory_xxhash128`
comes from, so that "the live code and the migration cannot disagree" is
visible rather than implicit.

The rest of this section is what the script needs from outside itself, and is
kept because nothing else is durable: `/tmp/deps.tsv` on `cslh19` is temporary.

### 9.1 Dumping the dependency table

On `cslh19`, feed this to `isabelle console -l AFP-ALL-4 -n` on stdin (`-n`
suppresses any build; the image takes about four minutes to load). Plain SML —
`\<^try>` cartouches do not survive the console.

```sml
fun path_of thy =
  (let
     val master_dir = Resources.master_directory thy
     val base = Long_Name.base_name (Context.theory_long_name thy)
     val f = Path.ext "thy" (master_dir + Path.basic base)
   in File.platform_path (File.full_path master_dir f) end)
  handle _ => "";

fun addthy thy (seen, acc) =
  let val n = Context.theory_long_name thy in
    if Symtab.defined seen n then (seen, acc)
    else
      let val (seen2, acc2) =
        fold addthy (Theory.parents_of thy) (Symtab.update (n, ()) seen, acc)
      in (seen2, (n, thy) :: acc2) end
  end;

val roots = map Thy_Info.get_theory (Thy_Info.get_names ());
val all_thys = #2 (fold addthy roots (Symtab.empty, []));

fun line (n, thy) =
  "DEP\t" ^ n ^ "\t" ^
  (if Resources.loaded_theory n then "L" else "W") ^ "\t" ^
  path_of thy ^ "\t" ^
  space_implode "," (map Context.theory_long_name (Theory.parents_of thy));

val _ = writeln (cat_lines (map line all_thys));
val _ = writeln ("DEPCOUNT " ^ string_of_int (length all_thys));
```

`Thy_Info.get_names ()` omits `Pure`, which is a constituent of 99.4% of all
theorem records — the parent closure in `addthy` is what brings it in, so the
result is 10,598 rows, not 10,597. Strip the console's `Poly/ML>` prompts with
`sed -n 's/^.*\(DEP\t\)/\1/p'`. Every row must have five tab-separated fields.

### 9.2 Building the two hash tables

Both are computed bottom-up over the table, in Python, importing
`theory_xxhash128` from `Isabelle_RPC_Host.theory_hash` so that the live code and
the migration cannot diverge:

```
old[T] = clear_lsb( xxh128( file(T) ++ concat(old[P] for P in parents(T)) ) )
new[T] = clear_lsb( xxh128( name(T) ++ 0x00 ++ file(T) ++ concat(new[P] ...) ) )
```

`old` is today's algorithm and exists only to run G1; `new` is what the store is
re-keyed to. Recursion depth reaches a few hundred — raise the limit.

### 9.3 Classifying every key

One pass over `semantics.lmdb` produces three artefacts: the **old-key → new-key
map** (~211 MiB in memory for 1.38 M 32-byte pairs), the **explicit drop-key
list**, and the counts G3 checks. Per entry:

- `len(key) < 16` — the counter `b"\xf0"`. Copied verbatim; it is not a record
  and has no theory hash.
- `len(key) == 16` — a theory-status record whose key *is* the theory hash. New
  key is that theory's new hash; dropped if the hash is unmappable or shared.
- 32 bytes with tag in `{0x02, 0x12, 0x22, 0x32, 0x42, 0x08}` — XOR-prefixed.
  An **empty** constituent list is legitimate and must not be confused with an
  absent one: a few experiences name no theory, their prefix is the all-zero
  `xor_theory_prefix([])`, and they keep their exact key. Otherwise map every
  constituent hash, and where a **persistent** constituent is shared by two
  theories use the long name the record itself carries (D4). If a constituent
  is unmappable: when the record is EXPERIENCE (tag 8) and every offending
  constituent's long name is held by the image, re-point it by name to the
  current generation (D5); otherwise drop the record. New prefix is
  `xor_theory_prefix` of the
  rewritten hashes; new key is that prefix ++ `key[16:]`.
- anything else — name-addressed. New key is the new hash of `key[:16]` ++
  `key[16:]`; dropped if that hash is unmappable or shared.

### 9.4 Rewriting a record's value

Order matters, because it is what keeps the key and the value consistent by
construction — the one property `fsck` actually checks:

1. rewrite the hashes in `theory_constituents`;
2. compute the new XOR prefix **from that rewritten list**, never from a
   separately-maintained copy;
3. substitute the 16-byte prefix in `locale_uk` and in every `deps` entry;
4. `template_uk`: if the value resolves to a live record today, replace it with
   that record's new key from the old-key → new-key map; if it already dangles,
   leave it byte for byte (§5 repairs those later, from Isabelle);
5. write under the new key.

### 9.5 The remaining stores

The vector store is streamed key by key through the **old-key → new-key map**,
not the theory table; entries whose key has no image are dropped; values —
including the 8,908 empty-value tombstones — are copied verbatim. The 723
sixteen-byte embed-status keys ride that same map: they are theory hashes, and
every one of them is present as a theory-status key in `semantics.lmdb`
(measured, 723 of 723), so the map already covers them — and routing them
through the theory table instead would resurrect a key whose record was
dropped, manufacturing exactly the orphan the vector gate exists to catch.

**It also holds one entry that is not a universal key at all**:
`\x00__vector_format__` = `q15/v1`, the Q1.15 provenance stamp written by
`migrate_float32_to_q15.py`. Nothing reads it at query time — that script is
its only reader, on its own re-run — but it has no image in the key map, so
the run of 2026-08-13 dropped it silently and it was restored by hand from the
pre-migration store afterwards. The `semantics.lmdb` counter was handled by
hand from the start and nobody asked the same question of the vector store.
Such entries are now copied verbatim and reported, and both the count gate and
the vector-key gate know they have no record by design. A migration that
silently discards a key it does not recognise is the wrong shape whatever the
key turns out to be.

More than one `vector_*.lmdb` is refused rather than half-migrated: the package
supports several models, and silently leaving one keyed to the old scheme would
orphan all of its entries after the swap. The authoritative machine has one.

`theory_hash.lmdb` is re-keyed with the theory table. Two kinds of merge happen
there and both are counted rather than left silent: the 10 collapsed groups,
whose single entry can only follow one of the two successors, and — much larger
— several content generations of one name, which now all key to that name's one
new hash. Over a quarter of the store merges this way, so the run must report
what it wrote rather than what it attempted.

### 9.6 Order of operations

1. Confirm no process holds any of the four stores (`fuser`/`lsof`); kill the
   REPL server if one is up, and never connect to its port.
2. Dump `deps.tsv` (§9.1) and build the tables (§9.2). Run **G1** and **G2**.
3. Build the new `semantics.lmdb`, then the new vector store, then the new
   `theory_hash.lmdb`, all in a staging directory. Run **G3**, **G4**, **G5**,
   **G6** against it with `SEMANTIC_DB_DIR=<staging>` and `--src-theory-hash`
   pointing at the live theory-hash cache (that one is not staged by the
   environment variable — see the head of §6). Then **G7**: `reindex` and
   `fsck` against the staging directory, still before the swap.
4. Swap all four directories together.
5. Restart every REPL and RPC host, since ML memoizes hashes per process.

Steps 3 and 4 are the writes that need per-run approval under D11.

### 9.7 What is kept of the dropped records

`--drop-list FILE` writes every dropped key and the reason it died. Pass it on
the run that matters; it is the record of what the migration decided, and the
input to any later top-up.

The records themselves are not lost by the migration and do not need to be
copied anywhere: per D7 the source stores are opened read-only and the whole
directory is swapped at the end, so **the untouched original holds all 1,534
dropped records with their full content** and stays the backup.

**Can re-interpretation put them back?** For all but one record, yes — and for
one class it is the only way. Interpretation is what mints an entity record, so
running the collection pipeline (`Semantic_Collection_App`) over a theory
regenerates its records under whatever hash that theory has at the time.

**The working list is `THEORY_HASH_REKEY_REINTERPRET_LIST.md`**, which names
every affected theory with a status column; keep that current rather than
re-deriving this from the numbers below. Per class:

- the **52 standing on a shared hash** must be re-interpreted; nothing else can
  bring them back, because the information saying which of the two theories a
  record belongs to does not exist anywhere in the store. This is what
  `THEORY_HASH_REKEY_REINTERPRET_LIST.md` is a list of, and what makes D4 a
  drop-and-re-interpret decision rather than a guess. It is cheap: after the
  migration each name has its own hash, the 20 theories are small, and the
  whole population is 42 entity records plus 10 theory-status records. Their
  theory-status records are among the dropped, so the next collection covering
  them re-enumerates without being told to.
- the **733 out of scope** can be re-interpreted too, but only under a session
  that holds those theories — `AFP-ALL-4` does not, which is why they dropped.
  For these, re-interpretation is the *expensive* path and not the first
  choice: their records still exist in the original store, so dumping a
  dependency table from an image that does hold them (`MathBench_Prover`,
  `NTP4Verif`) and re-running the same classification for those keys alone
  brings them across for no LLM spend at all. D6 declined to do that now;
  nothing about it expires.
- the **13 superseded theory-status records** and the **736 duplicates** need
  nothing: the current generation's record is already in the store.

**The one exception is a single EXPERIENCE record**, the one naming
`Minilang.Minilang`. Experiences are agent-authored — written during proof
search, not by theory interpretation — so no collection run recreates them,
which is the whole reason D5 exists. It is the only entry in the drop set that
no re-run of any kind can restore, and the only reason it is dropped at all is
that its constituent theory is out of scope.

## 10. To verify before §5(a) is scheduled

How to obtain the class-level member from the locale-level template in ML. A
class's own instance is a registration of locale `L` qualified
`Class.class_prefix L`, and `locale_instance.ML` already replays locale notes
through registration morphisms, so the machinery probably exists — but that is
an inference from reading, and §5(a) should not be scheduled until it has been
run.

### 9.8 The G4 dump session

Two files, kept here rather than in the tree for the same reason as §9.1: they
are throwaway inputs to a gate, and nothing outside this repository is durable.
Materialise them into a scratch directory on the machine holding the store.

`ROOT`:

```
session HASHDUMP = "AFP-ALL-4" +
  sessions Isabelle_RPC
  theories Hash_Dump
```

`AFP-ALL-4` is the parent, so its 10,598 theories come from the built heap.
`Isabelle_RPC` is named under `sessions` rather than as the parent, which loads
it **from source** — that is what puts the new `theory_hash.ML` in front of the
walk without rebuilding anything.

`Hash_Dump.thy`:

```isabelle
theory Hash_Dump
  imports Isabelle_RPC.Remote_Procedure_Calling
begin

ML \<open>
fun addthy thy (seen, acc) =
  let val n = Context.theory_long_name thy in
    if Symtab.defined seen n then (seen, acc)
    else
      let val (seen2, acc2) =
        fold addthy (Theory.parents_of thy) (Symtab.update (n, ()) seen, acc)
      in (seen2, (n, thy) :: acc2) end
  end;

val roots = map Thy_Info.get_theory (Thy_Info.get_names ());
val all_thys = #2 (fold addthy roots (Symtab.empty, []));

fun line (n, thy) =
  "HASH\t" ^ n ^ "\t" ^
  \<^try>\<open>Theory_Hash.to_hex (Theory_Hash.hash_of thy) catch _ => "CANNOT_HASH"\<close>;

val _ = File.write (Path.explode (getenv "HASH_OUT"))
  (cat_lines (map line all_thys) ^ "\nHASHCOUNT " ^
   string_of_int (length all_thys) ^ "\n");
\<close>

end
```

The parent closure in `addthy` is there for the same reason as in §9.1:
`Thy_Info.get_names ()` omits `Pure`, a constituent of 99.4% of theorem
records. Run with

```
HASH_OUT=<file> isabelle build -d <MLML> -d <scratch> -o quick_and_dirty=true HASHDUMP
```

and feed `<file>` to `verify-live`. The dump necessarily contains a few
theories the dependency table does not — `Performant_Isabelle_ML`,
`Remote_Procedure_Calling`, `Hash_Dump` itself — because they come with
`Isabelle_RPC` and `AFP-ALL-4` does not hold them. `verify-live` reports that
count and does not fail on it; a mismatch or a missing theory does fail.
