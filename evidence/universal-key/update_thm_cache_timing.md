# `update_thm_cache`: which regime, and what it costs

Measured 2026-08-13 on `Isabelle2025-2` / `polyml-5.9.2`, repo `/home/qiyuan/Current/MLML`.
Nothing in the repository was edited.

---

## Verdict

**There is no steady-state delta for the constituents cache to serve, and in the one
regime where a delta does exist the cache is worth about ten milliseconds, once.**

Broken into the two halves the question has:

*At `at_begin`, §A.6's unverified suspicion is correct.* Over ten identical
nine-theory session builds — ninety theory begins in total — exactly ten produced a
non-empty delta, and all ten were the same theory: the one whose import list joins a
cone that no `Thm_Cache` hook had ever visited (`HOL-Library.Library` on top of
`Semantic_Embedding`). Every other theory begin found
`Facts.dest_static false [cached_facts] current_facts` empty and the hook returned
`NONE`. The shipping configuration is on the far side of that one-shot pass, not in
front of it: `MathBench_Prover`'s already-built heap carries `Semantic_Embedding` in its
cone (706 ancestors, 710 theories loaded, 98,710 static facts), and beginning a fresh
theory on top of that heap takes 246 ms (median of 9, range 179–348 ms) — not the many
seconds that keying 98,710 propositions from scratch would take. Its snapshot already
covers its fact table.

*At `at_end`, a delta does exist and §A.6 does not mention it.* `Theory.at_end` runs the
same wrapper, and there the delta is the theory's own newly declared facts. Every
theory that declares anything pays it: 39 ms median (range 25–52 ms over 25
observations) for a theory contributing 152 cached entries. That is the genuine
recurring cost of the hook — and it is *still* almost entirely out of the constituents
cache's reach, because the cache can only skip work on a proposition whose 128-bit
digest has been seen before, and:

- within one such delta the repeat rate is 21.05 % at its most favourable (32 of 152,
  and that 21 % is an artefact of my `datatype`/`primrec`-heavy test theories — the
  theory of 30 hand-written lemmas repeated 0 %);
- a repeat is worth `compute_constituents`, measured at 8.41 µs (median of 5, range
  8.32–8.68 µs) minus the 0.39 µs a cache hit costs instead;
- so the cache saves **0.26 ms of a 39 ms `at_end`, i.e. 0.7 %**.

For the one-shot bulk pass the same arithmetic gives 1,232 repeats of 19,558
propositions (6.30 %) at 9.58 − 1.40 = 8.18 µs each = **10.1 ms of a 1,026 ms
`at_begin`, i.e. 1.0 %**.

What actually dominates the hook is not key computation at all. `Facts.dest_static`
walks the entire fact table on *every* invocation, before the `null new_facts` test and
before the `Time.now ()` the printed millisecond figure starts from — so that walk is
invisible in the trace line. It costs 18.4 ms per walk at 43,437 facts and 95.7 ms per
walk at `MathBench_Prover`'s 98,710 facts. And `Theory.apply_wrappers` re-runs the
wrapper list until every wrapper returns `NONE`, which I measured as exactly two passes
at every begin and every end — so a theory pays four full fact-table walks. On the
shipping heap that is roughly 0.38 s per theory of pure scanning that no cache of
proposition digests can touch. The 0.26 ms the constituents cache saves at a steady-state
`at_end` is about one part in 1,500 of that.

---

## 1. Which regime

`vtracing_global` (`contrib/Semantic_Embedding/Tools/semantic_store.ML:289`) is gated on
the theory-level config `Semantic_Store_verbose`, turned on with
`declare [[Semantic_Store_verbose = true]]`; a theory that declares it passes it to its
descendants, so one declaration in the root of the chain covers the whole session.

A batch `isabelle build` silently discards ordinary `tracing` (and `writeln`) output from
theory processing — I confirmed this with a deliberate `tracing "SMOKE-TRACING"`, which
appeared neither on the console (with or without `-v`) nor in the session `.gz` log. The
lines were recovered by pointing `Private_Output.tracing_fn` at the process stderr, which
`isabelle build` does echo. Attribution of a line to `at_begin` vs `at_end` comes from
`Position.thread_data ()`, which during a `Theory.at_begin`/`at_end` wrapper names the
`theory … begin` resp. `end` command that is running: line 1 of the file is a begin, the
last line is an end.

### Line counts

One round = one build of a nine-theory session (structure in §4). Per round:

- 9 theory begins + 9 theory ends = **18 boundary events**, each invoking
  `update_thm_cache` **twice** (measured, §2.3) = **36 invocations**;
- **7 lines emitted**, identical in all ten rounds:

| theory | boundary | N (new entries) |
| --- | --- | --- |
| `R*_Bulk` | `at_begin` | 19,499 |
| `R*_S1` … `R*_S5` | `at_end` | 152 each |
| `R*_T1` | `at_end` | 30 |

Everything else — the eight other theory begins, and the ends of `R*_Base`, `R*_Bulk`
and `R*_Merge` — produced no line at all, which is the hook reporting `null new_facts`
and returning `NONE`. Notably `R*_Merge`, whose two parents both carry a `Thm_Cache`
snapshot, is silent: the merge of the parents' snapshots really does equal the merge of
their fact tables.

A line with `N = 0` is possible and I saw one in a preliminary run: a theory whose only
new fact was `lemma smoke_1: "(1::nat) + 1 = 2"` printed
`0 new entries (34781 total) in 19ms` — the raw delta was non-empty, so the hook ran, but
the infra filter and `dedup_against` removed the single entry. None of the ten measured
rounds produced such a line.

### Distribution of N

Two clusters, nothing in between: one value of 19,499 (the bulk pass) and six values in
30–152 (a theory's own declarations). The bulk value is 128× the median of the others.

### Why the steady state is empty, and what would break it

At `at_begin` the current fact table is the merge of the parents' tables and the
`Thm_Cache` snapshot is the merge of the parents' snapshots. For a single-parent theory
`Context.merge_data` does not even call the merge function, so the child's snapshot *is*
the parent's final fact table object. The delta is therefore empty by construction. It is
non-empty exactly when some parent's cone never ran the hook — which happens once, at the
first theory that joins a `Semantic_Embedding`-descended branch to a branch built from a
plain heap. In this repository that theory is `MathBench_ProverBase`, which merges
`Minilang_AoA` (importing `Semantic_Embedding.Semantic_Embedding`) with ~50 AFP sessions
and `HOL-Complex_Analysis`.

---

## 2. The cost

### 2.1 Machine and load — read this before the numbers

14 logical cores (`nproc` = 14). The machine was **not** quiet: other agents were building
`Phi_Semantics_Framework`, `PhiStd` and related sessions throughout, and a Python test
suite ran alongside. One-minute load average sampled immediately before each round ranged
from 3.6 to 12.5. Every timed configuration below was run **5 times**; I report median
with the full min–max spread. Where a number is a single observation it says so.

### 2.2 The trace lines (5 rounds per configuration)

Default thread count (Isabelle `threads=0`, i.e. auto → 14):

| quantity | median | min | max | n |
| --- | --- | --- | --- | --- |
| `at_begin` bulk pass, 19,499 entries | 1,026 ms | 959 | 1,050 | 5 |
| `at_end`, 152 entries (`S1`…`S5`) | 39 ms | 25 | 52 | 25 |
| `at_end`, 30 entries (`T1`) | 20 ms | 19 | 33 | 5 |
| **sum of all 7 lines in a round** | **1,197 ms** | 1,149 | 1,295 | 5 |
| whole-session elapsed | 17 s | 15 | 20 | 5 |

`threads=1` (same sessions, `-o threads=1`), which halves Poly/ML's GC threads and roughly
doubles this allocation-heavy code:

| quantity | median | min | max | n |
| --- | --- | --- | --- | --- |
| `at_begin` bulk pass | 1,770 ms | 1,411 | 2,806 | 5 |
| `at_end`, 152 entries | 46 ms | 29 | 120 | 25 |
| `at_end`, 30 entries | 33 ms | 20 | 44 | 5 |
| **sum of all 7 lines in a round** | **2,027 ms** | 1,619 | 3,099 | 5 |
| whole-session elapsed | 28 s | 22 | 31 | 5 |

So the printed time is **1.2 s out of a 17 s session, about 7 %** — but that share is an
upper bound and should not be quoted as typical. My steady-state theories are deliberately
cheap (every proof is `by simp`), so the session's elapsed time is unusually small for the
number of facts declared. The *absolute* figures are the transferable ones: ~1.0 s once for
the bulk pass, and ~39 ms per theory end per 152 cached entries.

Per theory begin, in the steady state, the printed cost is **zero milliseconds** — there is
no line.

### 2.3 The cost the trace line does not show

`update_thm_cache` computes `new_facts` *before* it takes `t0`:

```sml
val new_facts = Facts.dest_static false [cached_facts] current_facts
in
  if null new_facts then NONE
  else let val t0 = Time.now ()
```

`Facts.dest_static` is `fold_static … |> sort_by #1` — it visits every static fact and
tests membership in the previous table. Timed directly with prev = the same table (so the
result is empty, exactly the steady-state case), 7 repetitions each:

| fact table | median | min | max |
| --- | --- | --- | --- |
| 43,437 facts (my bench session) | 18.4 ms | 17.6 | 34.3 |
| 98,710 facts (`MathBench_Prover` heap) | 95.7 ms | 76.0 | 131.0 |

And `Theory.apply_wrappers` loops. I counted the passes by registering an extra wrapper
that always returns `NONE` (so it cannot itself extend the loop) and prints one line per
firing: **two passes at every theory begin and two at every theory end**, without
exception, for every theory in the chain. The second begin pass is forced by
`Universal_Key.claim_cache_scope`, which returns `SOME` because the beginning theory's own
base name is not yet in the claims map.

Consequence: four full fact-table walks per theory. Cross-checked end to end on the real
shipping heap, `isabelle ML_process -l MathBench_Prover` (read-only, no build):

| `Theory.begin_theory` on … | median | min | max | n |
| --- | --- | --- | --- | --- |
| `MathBench_Prover` (98,710 facts, hook in cone) | 246.0 ms | 179.3 | 348.0 | 9 |
| `Main` (21,435 facts, hook **not** in cone) | 26.7 ms | 26.2 | 27.3 | 4 |

The first call of each series was slower (727.1 ms and 76.7 ms) and is excluded as a cold
outlier; both are reported here rather than dropped silently. 2 × 95.7 ms = 191 ms of the
246 ms is the two `Facts.dest_static` walks, which matches well; the remainder is
`Theory.begin_theory` itself plus `claim_cache_scope`'s 706-node cone walk.

That 246 ms also settles the regime question for the shipping heap by a second route: if
`MathBench_Prover`'s snapshot did *not* cover its fact table, this begin would have had to
key ~90,000 propositions, which at the bulk pass's measured 53 µs/entry is about 5 s, not
0.25 s.

### 2.4 An end-to-end A/B that did not resolve

I also ran a 2×2 (`Semantic_Embedding` in the cone or not) × (nine-theory chain or root
theory only), 3 rounds each, interleaved so any load drift hits all four alike. Median
elapsed: 28 s / 12 s / 13 s / 1 s, giving a hook cost of (28−12)−(13−1) = 4 s. But the
per-round values are 0 s, 9 s and 4 s. **This measurement is too noisy to resolve anything
and I am not using it**; I report it so it is not re-run in the belief that it is
informative. The load on this machine is simply too high for a whole-session subtraction
of this size. The internal instrumentation of §2.2–2.3 is what the conclusions rest on.

---

## 3. How much of that time is the constituents cache's target

`thm_constituents` (`Universal_Key.ML:705-727`) on a cache hit costs `Term_Digest.thm128`
plus one `Synchronized` table lookup; on a miss it additionally runs
`compute_constituents`. So the saving per hit is exactly the `compute_constituents` cost,
and `compute_constituents` is exported and bypasses the cache, which makes both halves
directly measurable on the same population.

### Duplicate-`thm128` rate within one delta

Counted over the propositions that actually reach `Universal_Key.key_of_theorem'`, i.e.
after the same `#concealed` / `Long_Name.is_hidden` / `is_infra_thm` gate that
`process_facts_into_cache` applies:

| delta | kept thms | distinct `thm128` | repeats |
| --- | --- | --- | --- |
| bulk `at_begin` (`R1_Base` → `R1_Bulk`) | 19,558 | 18,326 | 1,232 (**6.30 %**) |
| steady `at_end` (`R1_S1` → `R1_S2`) | 152 | 120 | 32 (**21.05 %**) |
| steady `at_end` (`R1_S2` → `R1_S3`) | 152 | 120 | 32 (21.05 %) |
| steady `at_end` (`R1_Bulk` → `R1_T1`) | 30 | 30 | 0 (**0.00 %**) |
| all seven deltas of one round, pooled | 20,348 | 18,956 | 1,392 (6.84 %) |

The 6.30 % on a `HOL-Library`-scale population sits just under §A.6's already-recorded
9.14 % ceiling on an AFP-scale one. The spread between 0 % and 21 % across the
steady-state theories is the whole story of the steady state: the 21 % comes from
`datatype`/`primrec`-generated facts, where one theorem is registered under several fact
names and so is digested more than once; the theory made of 30 hand-written lemmas has no
repeats at all. My test theories are unusually definition-heavy, so 21 % should be read as
a favourable bound, not a typical value.

### What a repeat is worth

| population | `thm128` (warm memo) | `thm_constituents`, cache **hit** | `compute_constituents` (what a hit skips) |
| --- | --- | --- | --- |
| bulk delta, n = 19,558, 3 reps | 0.74 µs (0.72–0.75) | 1.40 µs (1.40–1.49) | **9.58 µs (9.18–9.92)** |
| steady delta, n = 152, 5 reps | 0.25 µs (0.24–0.26) | 0.39 µs (0.39–0.84) | **8.41 µs (8.32–8.68)** |

Multiplying out:

- bulk `at_begin`: 1,232 × (9.58 − 1.40) µs = **10.1 ms**, against a 1,026 ms `at_begin`
  → **1.0 %**;
- steady `at_end`: 32 × (8.41 − 0.39) µs = **0.26 ms**, against a 39 ms `at_end`
  → **0.7 %**;
- steady `at_begin`: **0 ms**, because no key is computed there at all.

One negative result worth recording so it is not repeated. My first attempt at the miss
cost used the theorems the infra filter *rejects* (their digests are genuinely cold, since
the hook never keys them) and produced 101 µs per theorem, an order of magnitude above the
figure above. That population is not representative: `is_infra_thm` rejects oversized
propositions among other things, so the rejected set is systematically the large ones. The
9.6 / 8.4 µs figures come from the real kept population via `compute_constituents`, which
needs no cold cache to measure.

---

## 4. Exactly what was run

### Sessions

Ten identical benchmark sessions, generated by
`…/scratchpad/tcb/gen.py` into `…/scratchpad/tcb/R1` … `R10`, with
`…/scratchpad/tcb/ROOT` holding, for each `r`:

```
session TCB_R<r> in R<r> = "HOL-Library" +
  options [document = false]
  sessions
    Semantic_Embedding
  theories
    R<r>_Base  R<r>_Bulk  R<r>_S1 … R<r>_S5  R<r>_T1  R<r>_Merge
```

Why this shape is representative:

- Parent heap `HOL-Library` is **already built and up to date** (verified with
  `isabelle build -n`), so no project heap is touched. `Semantic_Embedding` is listed under
  `sessions`, so its theories (plus `Isabelle_RPC` and `Performant_Isabelle_ML`) load from
  source in ~10 s — this is the cheap-session allowance, and no heap image is produced for
  it.
- `R_Base` imports `Semantic_Embedding.Semantic_Embedding`, installs the stderr redirect
  and declares `Semantic_Store_verbose`.
- `R_Bulk` imports `R_Base` **and** `HOL-Library.Library`. Its second parent cone has never
  run the hook, so its `at_begin` is the whole inherited fact table — structurally the same
  event as `MathBench_ProverBase` joining `Minilang_AoA` to the AFP sessions, at 19,499
  entries instead of ~90,000.
- `R_S1`…`R_S5` form a single-parent chain, each declaring 2 `datatype`s, 1 `primrec`, 5
  `definition`s and 60 lemmas (all propositions distinct) — the steady state, with both an
  empty `at_begin` and a real `at_end` delta.
- `R_T1` is a second branch off `R_Bulk` with 30 plain lemmas; `R_Merge` imports `R_S5` and
  `R_T1`, so its `at_begin` merges two snapshot-carrying parents.

`…/scratchpad/probe/` holds `Probe.thy` … `Probe4.thy` in

```
session TCB_Probe in "." = TCB_R1 +
  options [document = false]
  theories Probe Probe2 Probe3 Probe4
```

reconstructing each delta with `Facts.dest_static` over `Thy_Info.get_theory` and measuring
digest counts, `compute_constituents`, and the no-op scan.

`…/scratchpad/pass/` holds the pass-counting session (`TCB_Pass`), whose `Pass_Base`
registers `Theory.at_begin (mark "begin") #> Theory.at_end (mark "end")` with a wrapper
that always returns `NONE`.

`…/scratchpad/ab/` holds the inconclusive 2×2 of §2.4.

### Commands

```sh
source /home/qiyuan/Current/MLML/envir.sh
S=/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad

isabelle build -j 4 Semantic_Embedding                  # ~10 s, cheap session
python3 $S/tcb/gen.py

for r in 1 2 3 7 8;      do isabelle build -d $S/tcb TCB_R$r; done
for r in 4 5 6 9 10;     do isabelle build -o threads=1 -d $S/tcb TCB_R$r; done
isabelle build -d $S/tcb -d $S/probe TCB_Probe
isabelle build -o threads=1 -d $S/pass TCB_Pass

isabelle ML_process -r -l MathBench_Prover -e "$(cat $S/mbp.ML)"  < /dev/null
isabelle ML_process -r -l MathBench_Prover -e "$(cat $S/mbp2.ML)" < /dev/null
```

Raw output is kept in `…/scratchpad/tcb/run_R*.log` and `…/scratchpad/ab/run_*.log`.

`isabelle build -c` was never used, and no project heap was rebuilt: `MathBench_Prover`,
`Minilang*` and `Phi_*` were only ever read (`isabelle build -n` to check staleness, and
`isabelle ML_process -l`, which loads a heap without building).

### One artefact left outside the scratchpad

Building `TCB_Probe` caused its parent `TCB_R1` to be written as a heap image:

```
~/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/TCB_R1     (54 MB, 2026-08-13)
```

Nothing depends on it and it is safe to delete; I left it in place rather than remove
files from the shared heaps directory without being asked. No other heap image was created
(`Semantic_Embedding` and the nine other `TCB_R*` sessions are leaves and produced none).
