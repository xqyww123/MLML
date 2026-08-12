# BUG: a theorem's universal key depends on theory-resolution order, not on the theorem

Status: **diagnosed, not fixed.** Found 2026-08-12 while backfilling source
positions into the semantic DB. Nothing has been changed in response to it.

Locations, as of `Isabelle_RPC` @ `5fcf0b2`:

- `contrib/Isabelle_RPC/Tools/theory_hash.ML` — `by_short_cache` / `hash_of_short` (≈222-233)
- `contrib/Isabelle_RPC/Tools/Universal_Key.ML` — `theory_short_of` (≈464-468),
  `compute_constituents` (≈469-480), and the signature comment (≈58-65)

## 1. Summary

The universal key of a **theorem-alike** entity (theorem, intro/elim/induction/
case-split rule) is supposed to be content-addressed: a function of the
proposition alone. **It is not.** Its 16-byte prefix depends on the order in
which theories happened to be resolved in the ML process that computed it.

Two theories in different sessions may share a **base name** (`Expr`, `Heap`,
`Term`, `Syntax`, `Value`, `Comparator`, …). The key computation resolves a
constant's defining theory **by base name**, through a **process-global,
first-writer-wins memo**. Whichever theory pins a base name first in a process
pins it for every later computation in that process — including for theorems that
have nothing to do with it.

Consequence: the same theorem gets different keys in different processes.

## 2. The defect, exactly

`Universal_Key.compute_constituents` identifies each constituent theory by the
**leading qualifier** of a constant's internal name:

```sml
fun theory_short_of name =                        (* Universal_Key.ML *)
  case Long_Name.explode name of
    seg :: _ :: _ => seg
  | _ => "Pure"

(* constituent theories, keyed by short name (unique within a runtime);
   short-name resolution + hashing is memoized inside Theory_Hash. *)
  ... Strhashtab.update thys (short, Theory_Hash.hash_of_short context short)
```

and `Theory_Hash.hash_of_short` memoizes that resolution **globally**:

```sml
val by_short_cache : (string * hash) Symtab.table Synchronized.var =   (* theory_hash.ML *)
  Synchronized.var "Theory_Hash.by_short" Symtab.empty

fun hash_of_short context short =
  case Synchronized.change_result by_short_cache (fn tab => (Symtab.lookup tab short, tab)) of
    SOME info => info                       (* <-- context is IGNORED on a hit *)
  | NONE =>
      let val thy = resolve_theory context short
          val info = (Context.theory_long_name thy, hash_of thy)
          val _ = Synchronized.change by_short_cache (Symtab.update (short, info))
      in info end
```

The cache key is the bare short name. **No context, no invalidation.** On a hit
the `context` argument is discarded, so the answer is whatever the first caller
in this process happened to get.

And `resolve_theory` with a short name is a genuine name-space lookup:

```sml
Theory.check {long = false} (Context.proof_of context) (name, Position.none)
```

### Two comments in the source state the false assumption outright

`Universal_Key.ML`'s signature comment:

> "A constant/type's defining theory is taken as the LEADING QUALIFIER of its
> fully qualified name … **No name-space lookup is involved, so the key depends
> only on the thm, not on the context it is reached from.**"

Both halves of that sentence are wrong: `hash_of_short` → `resolve_theory` →
`Theory.check {long=false}` **is** a name-space lookup, and the key therefore
does depend on the context — worse, on the *first* context of the process.

`compute_constituents`' inline comment:

> "constituent theories, keyed by short name (**unique within a runtime**)"

Measured in an `AFP-ALL-4` session: **1,655 of 10,647 loaded theories share a base
name with another** — 609 distinct collisions. `Syntax` is carried by 11
theories, `State` by 11, `Value` by 10. Inside the semantic DB, **366 base names
appear under more than one long theory name.**

## 3. Why name-addressed keys are immune (and this is the diagnostic fingerprint)

`key_of_ns_entity` — the constant/type/class/locale path — takes
`#theory_long_name` from the `Name_Space` entry and calls `Theory_Hash.hash_of`
on the **long** name. It never touches the short-name memo.

That asymmetry is visible in the data. After a full backfill sweep of the AFP
store on `cslh19`:

| kind | covered |
|---|---|
| constant | 97.2 % |
| locale / class | 99.8 % |
| collection / method | 99.5 % / 99.1 % |
| type | 94.4 % |
| **theorem** | **78.0 %** |
| intro-rule | 65.2 % |

The shortfall falls exactly on the kinds whose key goes through the short-name
memo, and only on those.

## 4. Consequences

1. **Theorem keys are not reproducible across processes.** A retrieval that
   computes a key today may not find the record written yesterday. This is a live
   correctness defect in the semantic DB, entirely independent of the position
   work that surfaced it.
2. **The store already contains the damage.** On `cslh19`'s 1,362,343-record
   store, **234,398 records** hold keys the current process cannot reproduce, and
   the same run produced ~240,712 keys with no record — the same mismatch seen
   from both sides. **19,007 records are duplicates of one another under different
   prefixes** (the same fact stored two or three times).
3. **Anything that selects records *by theory* is mis-targeted** on the affected
   records: `keys_belonging_to`, deletion, migration, vector invalidation. An
   affected record names constituent theories that are not even ancestors of the
   fact (observed: a `Q0_Metatheory.Syntax` record carrying `MiniSail.Syntax`).
   **This blast radius has not been measured.**

## 5. Evidence

**(a) The fingerprint.** Among records the sweep *reached*, **0 of 6,946**
constituent base names carry more than one long theory name. Among the records it
*missed*, **246 of 3,479** do. Per-context resolution would put both
`JinjaThreads.Expr` and `Statecharts.Expr` in the reached population; exactly one
appears, every time. Only a process-global first-writer-wins cache does that.

**(b) Sweep order predicts the winner, 4 for 4** (line numbers are in the sweep's
own per-theory log):

| base name | pinned first (all hit) | the losers (unreached refs) |
|---|---|---|
| `Term` | `First_Order_Terms.Term`, log line 898, 283/283 | `Higher_Order_Terms` 23,040 · `HOL-NanoJava` 491 |
| `Expr` | `Statecharts.Expr`, line 1038, 476/476 | `JinjaThreads` 9,497 · `Jinja` 3,143 · `CoreC++` 2,211 · `JinjaDCI` 303 |
| `Comparator` | `HOL-Library.Comparator`, line 1133, 152/152 | `Deriving.Comparator` 4,942 |
| `Heap` | `Selection_Heap_Sort.Heap`, line 909, 144/144 | `HOL-Imperative_HOL` 6,792 · `JinjaThreads` 5,654 |

**(c) The stored constituent lists are sound.** Re-XORing each record's stored
constituent hashes reproduces its own key prefix for **899,399 reached and
233,795 unreached records — 0 mismatches**. So the records faithfully record what
they were keyed on; the divergence is entirely on the recomputation side.

**(d) The statement digest is untouched.** `thm128` tails recomputed for a sample
were **22/22 byte-identical**. The corruption is confined to the 16-byte prefix.

**(e) Attribution of the 234,398 unreachable records:**

| cause | records | share |
|---|---|---|
| **the short-name memo** | **229,267** | **97.8 %** |
| genuine source change (constituent's hash moved) | 635 | 0.27 % |
| theories never swept (`Geo_Real2` 3,073, …) | 3,893 | 1.66 % |
| name-addressed stragglers | 601 | 0.26 % |

## 6. What is NOT the cause — do not re-chase these

- **Submodule updates.** Seven siblings on `cslh19` were fast-forwarded shortly
  before the sweep. Refuted at blob level: `Universal_Key.ML` (`952eaa88…`),
  `theory_hash.ML` (`8dd162e9…`) and `Term_Digest.ML` (`0ca5e072…`) have
  **identical blob SHAs** at `bf66a59` and `5fcf0b2`, and `git log bf66a59..5fcf0b2`
  over those paths returns **0 commits**. 0 % of the 234k.
- **An older AFP snapshot / changed theory hashes.** Only 0.27 %. This was the
  first hypothesis and it is essentially wrong: the constituent theories are all
  present, loadable and swept, and their hashes reproduce.
- **`thm128` not being alpha-invariant.** A real property of `Term_Digest`, but
  not the cause here: the tails recompute identically.
- **Records being stale duplicates of positioned ones.** Only 7.2 % of the
  unreached share an expression with a positioned record, 0.2 % an interpretation.

## 7. The fix

The correct source of a constant's defining theory is the one
`key_of_ns_entity` already uses: the constant's `Name_Space` entry's
`#theory_long_name` in the current context. `compute_constituents` should not
resolve by base name at all.

A weaker fallback, if the long name is genuinely unavailable at that point: key
the memo by `(theory identity of the context, short name)` rather than by the
short name alone. That removes the cross-context poisoning but still resolves by
base name, so it only narrows the window.

**Any fix changes existing keys**, i.e. it is a re-keying migration of a 1.9 GB
published store. Sequence it deliberately: measure the blast radius (§4.3) first,
then decide whether to re-key, to re-collect, or to carry a compatibility index.

## 8. Recovering the positions, independently of the fix

The 15-byte `thm128` tail plus the kind tag — `key[16:]` — identifies the
*statement* and is unaffected. Over 1,134,149 theorem-alike records there are
**1,124,334 distinct tag+tails**, and **220,252 of the 233,796 unreached (94.2 %)
have a tail that is globally unique**. The remaining 13,544 share a tail with a
record that is the *same fact under a different prefix*, so a record-name equality
tiebreak makes them safe too.

So: re-run the backfill matching on `key[16:]` with a name-equality guard, and
essentially all of the 234k get their positions — without waiting for the keying
fix. Read-mostly, no re-collection, no rebuild.

## 9. How to reproduce

The store: `cslh19:~/.cache/Isabelle_Semantic_Embedding/semantics.lmdb` (open
**read-only**). The sweep's per-theory log:
`~/.cache/Isabelle_Semantic_Embedding/semantics.lmdb.positions-20260812-003551.log`.
A 1,000-record sample with constituents:
`contrib/Semantic_Embedding/unpositioned_1k.txt`.

The cheapest direct demonstration needs no store at all: in one ML process under a
session containing two theories with the same base name, compute
`Theory_Hash.hash_of_short ctxt "Expr"` from two different contexts and observe
that the second returns the first's answer.

**Safety on `cslh19`:** the Isa-REPL server on :6666 is killed by a bare TCP
connect — check liveness with `ss` only. Never run `isabelle build` on
`AFP-ALL-4` (60 hours to rebuild) and never pass `-c`.

## 10. Background

Found while implementing `contrib/Semantic_Embedding/ENTITY_POSITION_PLAN.md`
(entity positions; §18 records the run). The backfill re-enumerates entities from
source and matches them to stored records by recomputing their universal keys —
which is precisely an experiment in key reproducibility, and it failed for 17 % of
the store.
