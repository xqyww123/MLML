# What `Universal_Key.thm_constituents` recomputes on every AoA invocation

## Answer

In a scratch theory begun over the **`MathBench_Prover`** heap (707 ancestors, 98,710 static facts),
the three populations that get their universal keys — and hence their constituent-theory lists —
rebuilt at every `Semantic_Store.make_entity_callbacks` call and in the queries that follow are:

1. **The static delta** (`semantic_store.ML:1186-1191`) is **empty in a fresh scratch theory (0 thms)**
   and grows exactly one thm per proved lemma: **50 thms after 50 lemmas, 150 after 150**. At 150 it
   costs **1.309 ms without the constituents cache and 0.228 ms with it** (8.73 vs 1.52 µs per thm).
2. **All dynamic-collection members** (`semantic_store.ML:1200-1201`) are **3,245 thms**, drawn from
   65 non-infrastructure dynamic collections. **All 3,245 get a universal key built** (see the
   correction below — the infra filter only decides which of them are *emitted*, not which are
   key'd); 3,113 survive `is_infra_thm`. Their `thm_constituents` calls cost **34.49 ms without the
   cache and 16.62 ms with it** (10.63 vs 5.12 µs per thm). The full per-member key work the code
   actually does — `key_of_theorem'`, `constituents_of`, plus a second rule-kind key for the 1,583
   members that sit in rule-suffixed bins — costs **53.34 ms per AoA call** with the cache warm.
3. **The five thm-like callbacks' live sets** total **5,042 thms**: theorems 150, introduction rules
   1,418, elimination rules 249, induction rules 1,758, case-split rules 1,467. One query of each,
   summed, spends **107.5 ms in `scope_ok`'s `thm_constituents` calls without the cache and 9.25 ms
   with it**.

Every figure is a median of **11 interleaved rounds** (each round runs the no-cache pass and then
the cached pass), with the full min–max given in the breakdown. Nothing was hand-picked; the two
numbers that are single observations are labelled `[1 observation]`.

**Steady-state hit rate is 100 % for all three populations.** Over the whole run
`Universal_Key.constituents_totals ()` reported `skipped = 0` and `empty_name_fallback = 0`, so not
one of the ~13,500 propositions measured was of the kind `thm_constituents` refuses to cache. Every
proposition read a second time is a hit.

**The finding that changes the picture: the cache is already warm before the first AoA call.** The
scratch theory's `Universal_Key.cache_scope_id` is `SOME 31914266` — *the same id* `MathBench_Prover`
itself reports, so the scratch theory does not get a fresh cache, it inherits the very cache object
that theory carries. And that object is not empty. A stride sample of 5,026 static facts that the
probe had never touched cost **4.75 µs per thm on its first-ever cached pass, against 18.02 µs per
thm with no cache at all**. A pass consisting purely of misses cannot be cheaper than the no-cache
pass — a miss does everything the no-cache path does and then digests, looks up and inserts — so the
majority of those 5,026 (about 84 % by the arithmetic below) were hits on first touch. Consequently
the "first AoA call is all misses, second call is all hits" model does not hold here. Only two of
the populations are genuinely cold on the first call: the freshly proved proof-local facts, and the
`Induct.dest_rules` net (induction and case-split rules), whose propositions are not the static
facts' propositions.

---

## Where the measurement was taken, and why

The context is a scratch theory `Probe_AoA_Recompute` with `imports MathBench_Prover.MathBench_Prover`,
processed by `isabelle process_theories -l MathBench_Prover`. This is the session the AoA agent
actually runs against. Two properties of it matter here: its cone carries `Semantic_Embedding` and
`Isabelle_RPC` (which is what makes `Universal_Key`'s `Theory.at_begin` hook have run, and gives the
theory a cache at all — a smaller session such as the built `Semantic_Embedding` heap has that too),
and it carries the full mathematical library AoA proves against, which is what makes the population
sizes realistic.

A note on how that session was chosen. The brief was first tightened to `MathBench_Prover`, then
corrected to `MathBench_ProverBase` on the grounds that the `MathBench_Prover` heap had disappeared.
It had — but only briefly: another agent's `isabelle build -b -o threads=10 -o system_heaps
MathBench_Prover` (not mine, started 23:04, which I left strictly alone) rebuilt it, and it was back
at `contrib/Isabelle2025-2/heaps/polyml-5.9.2_x86_64-linux/MathBench_Prover` (83 MB) at **23:08**,
before I started. I used `MathBench_Prover` rather than `MathBench_ProverBase` because
`MathBench_ProverBase` does **not** import `Minilang_AoA` (that happens in `MathBench_Prover.thy`),
so its cone contains no `Universal_Key`, no `Semantic_Store` and no `Context_Callbacks`: a scratch
theory over it would have had to load four sessions from source and would have reported
`cache_scope_id = NONE`, making the whole with-cache half of the measurement impossible. If you
would rather have `MathBench_ProverBase` anyway, say so and I will re-run — the probe is unchanged
apart from the import line.

`isabelle build` was never run, in any form, and `-c` appears nowhere. `process_theories` calls
`Build.build_logic(..., strict = true)`, which first does a `no_build = true` test and only builds if
that fails; the run log shows no `Build started for Isabelle/...` line, so nothing was built.

### Preconditions, as printed by the probe

```
probe theory itself: hash persistent = true, cache_scope_id = SOME 31914266
    Pure:             hash persistent = true, cache_scope_id = NONE
    Main:             hash persistent = true, cache_scope_id = NONE
    MathBench_Prover: hash persistent = true, cache_scope_id = SOME 31914266
ancestors of probe theory = 707
static facts visible      = 98710
```

`Theory_Hash.is_persistent (Theory_Hash.hash_of Pure)` is `true`, so the RPC host was up and
`hash_of` took its persistent (xxhash128-over-RPC) branch — the numbers are therefore trustworthy.
The shell exported `ISABELLE_RPC_PYTHON=/home/qiyuan/Current/MLML/.venv/bin/python3`. `Pure` and
`Main` report `cache_scope_id = NONE`, which is the `No_Cache` state the brief asks to be confirmed;
the scratch theory reports `SOME 31914266`.

### The two regimes

`thm_constituents` has exactly two branches:

```ml
fun thm_constituents context thm =
  case Cache_Scope.get (Context.theory_of context) of
    No_Cache => compute_constituents context (Thm.prop_of thm)
  | Cache p   => (* Term_Digest.thm128, lookup, on miss compute + insert *)
```

So the without-cache regime is literally `Universal_Key.compute_constituents context (Thm.prop_of
thm)`, and that is what the probe calls. This is better than switching reading theories: it keeps
the reading context byte-identical between the two regimes, so no cone difference can contaminate
the comparison, and it is the same code the `No_Cache` branch would execute.

### Machine load

Run 2 (the run reported here) ran 23:22:48–23:22:58 with the 1-minute load average sampled every 5 s
between **1.76 and 2.10** (5-minute average 2.08–2.16) on this shared box, which was also holding
four other resident Isabelle/Scala sessions belonging to sibling agents. Run 1 (7 rounds, same probe
minus the heap-warmth population) ran at 23:19:23 under a heavier **4.37–5.00** load, immediately
after the sibling's `MathBench_Prover` build finished; its numbers are given at the end as a
replication and agree with run 2 except where noted. The Draft theory as a whole took 11.2 s elapsed
(11.0 s cpu, 1.0 s GC) in run 2.

---

## Breakdown

### 1. The static delta — `Facts.dest_static false [cached_facts] current_facts`

`cached_facts` is the `Thm_Cache` snapshot taken at the theory's `Theory.at_begin` and not refreshed
until `at_end`, so the delta is the facts this theory has declared since it began. The probe takes
its own snapshot in the first `ML` block of the scratch theory; no command has declared a fact by
that point, so that snapshot is the same fact table the `at_begin` hook stored.

| Point | Fact names | Thms | No cache (median [min–max]) | With cache, 2nd+ call | First cached call `[1 obs]` |
| --- | --- | --- | --- | --- | --- |
| Empty scratch theory | 0 | **0** | 0.005 ms [0.005–0.006] | 0.006 ms [0.005–0.009] | 0.018 ms |
| After 50 lemmas | 50 | **50** | 0.425 ms [0.407–0.547] = 8.50 µs/thm | 0.032 ms [0.028–0.046] = 0.64 µs/thm | 0.534 ms |
| After 150 lemmas | 150 | **150** | 1.309 ms [1.250–1.478] = 8.73 µs/thm | 0.228 ms [0.164–0.304] = 1.52 µs/thm | 1.242 ms |

The plain answer to "how big is it": in an empty scratch theory it is **exactly empty — zero facts,
zero thms** — and it then grows one thm per lemma, linearly, with no other contribution. Both the
measured costs scale linearly with it too.

The lemmas were not `lemma foo_i: "True" by simp`. Fifty of those would share one proposition and
therefore one cache entry, which would make the hit rate meaninglessly good and the per-thm compute
cost meaninglessly cheap. I used 150 *distinct* propositions cycling four shapes — `(a::nat) + b + k
= k + b + a`, `(x::real) * k = k * x`, `(n::int) - k + k = n`, `length (replicate k (x::'a)) = k` —
so all 150 propositions are distinct, as the "distinct propositions = 150" line confirms. Their
constituent sets are small (`Nat`, `Num`, `Groups`, `Groups_List`/`List`, …), which is why the warm
hit is 0.64–1.52 µs rather than the ~1.8–2.5 µs the bigger populations show: a hit still has to
compute `Term_Digest.thm128` over the whole proposition, so hit cost tracks proposition size.

These fresh propositions are the one population that is genuinely cold on its first cached pass, and
the table shows it: at 50 lemmas the first cached call (10.68 µs/thm) costs *more* than a no-cache
pass (8.50 µs/thm), the extra being the digest, the failed lookup and the insert.

### 2. All dynamic-collection members

| Quantity | Value |
| --- | --- |
| Names in the fact name space | 112,014 |
| `Facts.is_dynamic` among them | **106** |
| After `is_infra_dynamic_fact` | **65** (41 dropped) |
| Members of those 65 collections | **3,245** |
| Distinct propositions among them | 3,071 (174 duplicates, 5.4 %) |
| Members surviving `is_infra_thm` | **3,113** |
| Rule-suffixed collections among the 65 | 23 |
| Members sitting in those 23 | 1,583 |

**A correction to the question's premise.** The question asks "how many survive the infra filters
(that is the number that actually gets a key built)". Reading
`process_dynamic_facts_into_cache` closely, the two are different numbers. Per member the code does

```ml
val thm' = Thm.transfer thy thm
val uk0 = Universal_Key.key_of_theorem' NONE context thm'
val theories = (case Universal_Key.constituents_of uk0 of SOME cs => map #1 cs
                | NONE => map #1 (#2 (Universal_Key.thm_constituents context thm')))
...
in if Bytehashtab.defined pset uk0 then [] else (if is_infra_thm (coll, thm') then [] else [entry ...]) @ ...
```

`uk0` and `theories` are computed **unconditionally, before** `is_infra_thm` is consulted. The infra
filter only decides whether an *entry is emitted*. So the number that gets a key built is **3,245**,
all of them; **3,113** is the number that survives to become a `Theorem` entry. On top of that, the
1,583 members in rule-suffixed bins get a *second* key (`key_of_introduction_rule'` and friends),
which is a second `thm_constituents` call — a cache hit, since the first call just cached that
proposition.

Timings over the 3,245 members:

| Regime | Median | Range | Per thm |
| --- | --- | --- | --- |
| No cache (`compute_constituents`) | **34.49 ms** | 32.17–56.92 ms | 10.63 µs |
| With cache, 2nd+ call | **16.62 ms** | 16.17–23.44 ms | 5.12 µs |
| First cached call `[1 observation]` | 27.19 ms | — | 8.38 µs |
| Full per-member key sweep, warm cache | **53.34 ms** | 52.21–70.40 ms | 16.44 µs |

The last row is the honest per-AoA-call figure for this population: it replicates what
`process_dynamic_facts_into_cache` does per member (`key_of_theorem'` → `constituents_of` → the
rule-kind key where the bin name calls for one), not just the `thm_constituents` component. **Roughly
53 ms of every AoA invocation goes into re-keying dynamic-collection members**, and the comment at
`semantic_store.ML:1197` is right that none of it is ever saved: these never enter the persistent
`Thm_Cache`, so this repeats at every call.

Note that the warm hit here costs 5.12 µs, far above the ~1.8 µs of the other populations. That is
`Term_Digest.thm128`: dynamic-collection members are large propositions and many reach the digest
without a usable name hint, so the digest cannot be served from `thm128_cache` and is recomputed
over the whole term on every hit.

### 3. One semantic query's live pass — `scope_ok` at `context.ML:1266`

`scope_ok` sits second in the filter chain (after the name filter, before `filter_opt`, the
proposition-pattern matcher and the target-type filter), and it calls `thm_constituents` on every
live candidate that reaches it. With no `name_contains` given, that is the whole live set.

| Callback | Raw source | Live set | No cache (median [min–max]) | With cache, 2nd+ | First cached `[1 obs]` |
| --- | --- | --- | --- | --- | --- |
| `Context.theorems` | static delta | **150** | 1.230 ms [1.174–1.359] | 0.128 ms [0.103–0.187] | 0.234 ms |
| `Context.introduction_rules` | `Classical.dest_decls` → 1,790 | **1,418** | 13.330 ms [12.598–20.388] | 2.962 ms [2.823–3.718] | 4.222 ms |
| `Context.elimination_rules` | `Classical.dest_decls` → 1,309 | **249** | 2.677 ms [2.598–3.140] | 0.418 ms [0.357–0.486] | 0.631 ms |
| `Context.induction_rules` | `Induct.dest_rules` → 1,767 | **1,758** | 53.560 ms [47.571–73.845] | 3.112 ms [3.035–4.430] | 55.781 ms |
| `Context.case_split_rules` | `Induct.dest_rules` → 1,469 | **1,467** | 36.749 ms [35.210–48.186] | 2.626 ms [2.548–3.078] | 35.749 ms |
| **All five** | | **5,042** | **107.55 ms** | **9.25 ms** | |

"Raw source" is the net before the shared engine drops thms with no name hint and dedups by printed
name. Two things stand out and are worth someone's attention, though diagnosing them was not part of
this task:

- **The elimination-rule net loses 1,060 of its 1,309 members** (81 %) to that name-hint/dedup step,
  leaving a live set of 249. The comment at `context.ML` anticipates "~330 anonymous claset rules";
  the drop here is three times that, so most of it must be dedup by `Thm_Name.print` — several
  `make_elim`'d variants sharing one source fact name.
- **Induction and case-split rules are by far the most expensive propositions in the system**: 30.5
  and 25.1 µs per thm to compute constituents, against 8–11 µs everywhere else. They are also the
  only rule populations that are genuinely cold on the first call (see below), so the induction-rule
  query alone costs ~56 ms the first time it is asked in a session and ~3 ms thereafter.

### Hit rate, and why the first call is not all misses

The steady-state hit rate is **100 %** for every population: 0 of the ~13,500 propositions measured
produced `empty_name_fallback`, the one condition under which `thm_constituents` refuses to cache a
result, and `constituents_totals ()` confirmed `skipped = 0, empty_name_fallback = 0` for the whole
run. So on the second and every later AoA call, every one of these propositions is a hit.

The first call is a different story from the one the brief expected. Comparing the first-ever cached
pass against the no-cache pass tells you what fraction was already in the table, because a miss
strictly dominates a no-cache call in cost. Writing `t_cold = f·(t_nocache + t_hit) + (1−f)·t_hit`
and solving for the miss fraction `f`:

| Population | no cache | warm hit | first cached | ⇒ misses on first touch |
| --- | --- | --- | --- | --- |
| 5,026 untouched static facts (stride sample) | 18.02 µs | 1.83 µs | 4.75 µs | **~16 %** |
| Introduction rules (1,418) | 9.40 µs | 2.09 µs | 2.98 µs | **~9 %** |
| Elimination rules (249) | 10.75 µs | 1.68 µs | 2.53 µs | **~8 %** |
| Dynamic members (3,245) | 10.63 µs | 5.12 µs | 8.38 µs | **~31 %** |
| Case-split rules (1,467) | 25.05 µs | 1.79 µs | 24.37 µs | **~90 %** |
| Induction rules (1,758) | 30.47 µs | 1.77 µs | 31.73 µs | **~98 %** |
| 50 fresh proof-local lemmas | 8.50 µs | 0.64 µs | 10.68 µs | **100 %** (formula gives 1.18) |

The `f` column is a derived estimate, not a direct count — there is no API to ask the cache what it
holds — and the no-cache medians it divides by are the noisiest numbers in the run (the 5,026-fact
sample ranged 59.2–257.3 ms, i.e. 11.8–51.2 µs/thm, so its 16 % could be anywhere from ~16 % to
~25 %). But the *qualitative* reading is not an estimate at all: for the top four rows the first
cached pass is 2–4× cheaper than the no-cache pass, and that is arithmetically impossible unless
most of those calls were hits.

Where the warmth comes from: the scratch theory's `cache_scope_id` equals `MathBench_Prover`'s
exactly, so it inherits that theory's cache object rather than allocating one. The entries in it were
put there by `Semantic_Store`'s `Theory.at_begin`/`at_end` `update_thm_cache` hook building the
`Thm_Cache` over the session's ~98,710 static facts — each of which calls `key_of_theorem'` and
therefore `thm_constituents`. **I did not separate whether those entries were written when the
`MathBench_Prover` heap was built and then saved inside it, or written by the same hook firing when
the scratch theory began.** Distinguishing them would need a `Thm_Cache` accessor that the
`SEMANTIC_STORE` signature does not export. For the question asked it does not matter: either way
they are in the table before the first AoA call runs.

What is *not* warm, and why it is exactly the two `Induct.dest_rules` populations: the classical net
(`Classical.dest_decls`) hands back the very thms that were declared `[intro]`/`[elim]` as static
facts, so their propositions were already key'd by the `Thm_Cache` build. `Induct.dest_rules` hands
back rules after `Rule_Cases` processing, whose propositions differ from any static fact's — hence
essentially all misses on first touch and the ~56 ms and ~36 ms first-call costs above. (The
`f` formula charges a hit's digest cost to a miss too, so a genuinely all-miss population lands
somewhere around 0.9–1.2 rather than exactly 1.0; that is why the last three rows read 90 %, 98 %
and 118 % rather than a clean 100 %.)

---

## Two caveats on faithfulness

- The measurement context is `Context.Proof (Proof_Context.init_global thy)`, not a real
  mid-proof context. `agent_server.ML:1707` passes `Context.Proof ctxt` from inside a running proof,
  whose `Proof_Context.facts_of` additionally carries the proof's own local facts (`this`, `assms`,
  named `have`s). Those would add a handful of thms to the static delta and to the theorems live set
  — on the order of the number of `have` steps taken so far, i.e. small next to 150 — and they are
  fresh propositions, so they are misses on first touch and hits thereafter, exactly like the probe
  lemmas.
- Populations 2 and 3 were replicated in the probe rather than called through
  `Semantic_Store`, because `SEMANTIC_STORE` exports only `make_entity_callbacks` and not
  `process_dynamic_facts_into_cache`, `Thm_Cache` or the four `extract_*` net functions. The
  replication is a verbatim copy of those functions' bodies (they are 3–20 lines each) and it calls
  the same exported helpers the originals do — `Infra_Filter.gen_infra_filters`,
  `Context_Callbacks.dynamic_fact_members`, `Classical.dest_decls`, `Induct.dest_rules`,
  `Theory_Structure.is_*_rule_name`, `Theory_Structure.has_rule_shape`. Nothing was reimplemented
  differently; the counts it produces (98,710 static facts, 707 ancestors) match the sibling
  measurement quoted in the brief.

## Replication: run 1

Run 1 was the same probe with 7 rounds instead of 11 and without the heap-warmth population, taken
under a 4.37–5.00 load average. Its counts are identical (0/50/150; 106→65 collections, 3,245
members, 3,113 surviving; live sets 150/1,418/249/1,758/1,467) and its medians agree within the
ranges above, except that its induction-rule no-cache median came out at 77.4 ms [52.8–101.6] versus
run 2's 53.6 ms [47.6–73.8] — the population most sensitive to machine load, measured under twice
the load. Raw output for both runs is preserved.

## Probe source and how to re-run

All under `/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/`:

| File | What it is |
| --- | --- |
| `gen_probe.py` | Generator. Emits the theory; edit the ML here, not in the `.thy`. |
| `Probe_AoA_Recompute.thy` | Generated probe theory (477 lines: harness, 150 lemmas, seven measured populations). |
| `run_probe.sh` | Runner. Sources `envir.sh`, exports `ISABELLE_RPC_PYTHON`, invokes `process_theories`. |
| `probe_out.txt`, `probe_out_run2.txt` | Run 2 raw output (the numbers above). |
| `probe_out_run1.txt` | Run 1 raw output. |
| `run_probe.log`, `run_probe2.log` | Full `process_theories` logs. |
| `loadavg2.txt` | Load-average samples taken during run 2. |

To re-run:

```sh
cd /tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad
python3 gen_probe.py && ./run_probe.sh > run_probe.log 2>&1
cat probe_out.txt
```

`run_probe.sh` is:

```sh
cd /home/qiyuan/Current/MLML
source /home/qiyuan/Current/MLML/envir.sh
export ISABELLE_RPC_PYTHON=/home/qiyuan/Current/MLML/.venv/bin/python3
S=/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad
exec isabelle process_theories -l MathBench_Prover -o parallel_proofs=0 -O -v \
     -f "$S/Probe_AoA_Recompute.thy"
```

`-o parallel_proofs=0` keeps the 150 lemma proofs from being forked into background futures during
the timed sections; it is a build option and does not participate in the up-to-date check, so it
cannot provoke a rebuild. Round count is `NROUNDS` in `gen_probe.py`. The probe writes its results
incrementally to `probe_out.txt`, so you can watch it while it runs; the whole thing takes about
11 s of theory time once the heap is loaded (~2.5 min including the load).
