# `Universal_Key`'s constituents cache: mutable `Hash_Table` vs pure `Table` in a `Synchronized.var`

Measured 2026-08-12/13 on the shared box, Isabelle2025-2 / Poly/ML 5.9.2 (x86_64-linux).

---

## Verdict

**No. Trading the mutable `Hash_Table` for Isabelle's pure `Table` does not cost anything that
matters on the lookup path, at either population size, and the "O(1) becomes O(log n)" framing
overstates the change by comparing the wrong two things.**

The decisive number is this. At the measured real population of 20,000 entries, one lookup that
finds its key costs **29 ns** in the mutable hash table and **284 ns** in the pure tree. The
difference is **255 ns**. The thing that difference buys you the right to avoid is a
`compute_constituents` call, measured elsewhere at roughly 12 µs = 12,000 ns. So the entire penalty
of the redesign's lookup, at the full 20,000-entry population, is **2.1 % of one cache miss**. Put
the other way, and counting the lock both designs take: a cache hit costs 78 + 29 = 107 ns today and
would cost 78 + 284 = 362 ns through the tree, so it saves 99.1 % of the 12 µs today and 97.0 % of it
after the swap. Nobody can feel that.

Two further measurements make the comparison even less flattering to the "O(1)" side. First, both
designs take the `Synchronized.var` lock on every single cache access, and that round trip alone —
with no table work whatsoever inside it — costs **78 ns** (median; 57 ns at its quietest). That is
**two and a half times the entire hash-table lookup it is protecting**. The lock the current design
already pays for is more expensive than the data structure the redesign is accused of slowing down.
Second, computing the hash itself (`Term_Digest.digest128_hasher`) costs about **7 ns**, so a
quarter of the hash table's 29 ns is hashing, not probing.

The one number in this measurement that *is* dangerous is the merge. `Table.merge (K true) (t1, t2)`
for two tables of 10,000 entries each takes **2.8 ms** — roughly 233 times the cost of a single
`compute_constituents` call, and about **three times over a 1 ms budget**. This is the only result
that should change a design decision, and it only bites the variant that seeds a child cache from
its parents *and* has more than one parent carrying entries. `Table.merge (K true) (empty, t)` is
genuinely free — **1.8 ns, completely flat from n = 256 to n = 200,000** — because `Table.join`
short-circuits on `is_empty tab1` and hands back `tab2` unchanged
(`contrib/Isabelle2025-2/src/Pure/General/table.ML:539-546`; the guard is line 544). So a theory
begin with one contributing parent costs nothing at all; the cost is entirely in folding in the
*second and later* parents.

### The two variants

**Per-theory cache seeded empty (table stays in the hundreds).** The swap costs nothing measurable
in any sense that matters. At n = 256 a hit costs 14 ns through the hash table and 31 ns through the
tree — a 17 ns difference, **0.14 % of a 12 µs miss**. At n = 1,000 it is 16 ns versus 68 ns, a 52 ns
difference, **0.43 % of a miss**. Inserting a new key costs 52 ns versus 179 ns at n = 256 (a 127 ns
difference, 1.1 % of a miss) and 38 ns versus 175 ns at n = 1,000 (137 ns, 1.1 %). Every one of
these differences is smaller than, or the same order as, the 78 ns `Synchronized.var` round trip
that both designs pay unconditionally on every access. Allocating one `Synchronized.var` per theory
begin costs **56 ns**, which is 0.46 % of a single miss — irrelevant even if you begin ten thousand
theories.

**Per-theory cache seeded from the parents (tables reach ~20,000).** The lookup path is still fine:
+255 ns per hit, +482 ns per insert (34 ns → 516 ns), which together add about 6 % to the cost of a
miss and 2 % to the cost of a hit. But the merge is **not** within a 1 ms budget when two parents
each carry a real share of the entries: 10,000-into-10,000 measured **2.8 ms** (2.5–3.4 ms across
rounds; 2.5–3.0 ms across three independent processes). The per-entry folding cost is about
**280 ns**, so a 1 ms budget buys roughly **3,500 folded entries**. Concretely: at every theory
begin, `construct` may fold in the entries of every parent *except the first* for free-of-charge
`merge (empty, ...)` reasons — the first is O(1) — and it stays inside 1 ms only while those
remaining parents together hold under about 3,500 entries. Above that it does not. If the redesign
seeds from parents, this is the number to design around, not the lookup.

For scale, the *current* design already pays something comparable when `claim_cache_scope` forks a
cache: `Digest_Tab.make (Digest_Tab.dest cache)` on a 20,000-entry table measured **0.92 ms**
(0.81–1.9 ms). So the tree's merge is not in a different universe from what is there today — the
difference is that today's copy happens only on a base-name collision, whereas a parent-seeding
merge would happen at every theory begin that has a second contributing parent.

### Crossover

Taking 1 % of a 12 µs miss as 120 ns per lookup, the tree's lookup reaches it **between n = 1,000
and n = 2,000** — call it **n ≈ 1,500**. Measured (run 3, per-round minima, which are the least
contaminated by other load on the box): 81 ns at n = 1,000 (0.68 % of a miss) and 136 ns at
n = 2,000 (1.14 %). Run 3's medians bracket it the same way (117 ns at 1,000, 208 ns at 2,000), and
run 1's medians put n = 1,000 at 0.56 %. The hash table never reaches 1 % at any size measured: it
is 0.24 % at n = 20,000 and still only 0.82 % at n = 200,000.

---

## Measurements

All figures are **nanoseconds per operation**, median of **9 rounds** in one process, with the full
minimum–maximum spread across those 9 rounds in brackets. The "% of 12 µs" column expresses the
median against the 12 µs cost of the `compute_constituents` call a cache hit avoids.

The primary table is **run 1**. Runs 2 and 3 were separate processes started later, while other
work on the machine grew heavier; their medians are inflated by that contention, and they appear in
the cross-run section below rather than being averaged in. The direction and rough magnitude of
every result is the same in all three.

### Run 1 — the four required population sizes

| Measurement | n | Hash_Table median [min–max] | % of 12 µs | Table (2-3 tree) median [min–max] | % of 12 µs |
| --- | ---: | ---: | ---: | ---: | ---: |
| lookup, key present | 256 | 14.3 [12.5–24.8] | 0.12 % | 31.2 [29.4–46.9] | 0.26 % |
| lookup, key present | 1 000 | 15.6 [13.9–34.1] | 0.13 % | 67.5 [58.8–132.3] | 0.56 % |
| lookup, key present | 20 000 | 29.1 [26.7–39.7] | 0.24 % | 283.6 [234.8–408.4] | 2.36 % |
| lookup, key present | 200 000 | 98.3 [83.2–106.8] | 0.82 % | 814.0 [711.9–1220.4] | 6.78 % |
| lookup, key absent | 256 | 16.8 [12.0–21.2] | 0.14 % | 30.5 [28.0–48.8] | 0.25 % |
| lookup, key absent | 1 000 | 17.1 [14.8–24.3] | 0.14 % | 63.2 [56.9–102.2] | 0.53 % |
| lookup, key absent | 20 000 | 29.1 [23.1–72.3] | 0.24 % | 317.6 [235.5–392.5] | 2.65 % |
| lookup, key absent | 200 000 | 73.1 [64.3–144.4] | 0.61 % | 1040.7 [904.0–1841.3] | 8.67 % |
| insert a new key into a table holding n | 256 | 51.5 [43.0–79.9] | 0.43 % | 178.8 [158.7–515.8] | 1.49 % |
| insert a new key into a table holding n | 1 000 | 38.4 [36.6–55.9] | 0.32 % | 175.3 [164.9–254.2] | 1.46 % |
| insert a new key into a table holding n | 20 000 | 33.9 [29.7–55.6] | 0.28 % | 516.0 [458.4–618.3] | 4.30 % |
| insert a new key into a table holding n | 200 000 | 107.9 [86.4–272.0] | 0.90 % | 1537.1 [1458.7–3287.4] | 12.81 % |
| build from empty to n, per key | 256 | 29.1 [24.3–43.7] | 0.24 % | 181.0 [117.5–388.1] | 1.51 % |
| build from empty to n, per key | 1 000 | 37.5 [34.3–60.4] | 0.31 % | 201.2 [192.0–326.4] | 1.68 % |
| build from empty to n, per key | 20 000 | 54.2 [50.9–80.3] | 0.45 % | 562.1 [511.8–1215.3] | 4.68 % |
| build from empty to n, per key | 200 000 | 228.1 [175.9–720.6] | 1.90 % | 1802.2 [1237.6–3269.1] | 15.02 % |

The "build from empty to n" row is per key inserted over a whole construction, so for the hash table
it includes the amortised cost of its rehashes; the "insert into a table holding n" rows deliberately
do not (see the caveat about rehashing below).

### Run 1 — the operations only one of the two designs performs

| Measurement | n | median [min–max] | % of 12 µs |
| --- | ---: | ---: | ---: |
| `Synchronized.change_result v (fn s => (r, s))`, no table work | — | **77.8 ns** [56.7–557.6] | 0.65 % |
| `Synchronized.var` allocation (one per theory begin) | — | **55.6 ns** [37.4–173.9] | 0.46 % |
| `Term_Digest.digest128_hasher` alone | — | **7.2 ns** [5.6–10.9] | 0.06 % |
| `Table.merge (K true) (empty, t)` | 256 | 1.9 ns [1.5–4.3] | 0.016 % |
| `Table.merge (K true) (empty, t)` | 1 000 | 1.7 ns [1.6–2.1] | 0.015 % |
| `Table.merge (K true) (empty, t)` | 20 000 | 1.7 ns [1.6–2.7] | 0.014 % |
| `Table.merge (K true) (empty, t)` | 200 000 | 1.8 ns [1.6–3.5] | 0.015 % |
| `Table.merge (K true) (t1, t2)`, halves of n | 256 | 16.7 µs [14.6–82.8] | 139 % |
| `Table.merge (K true) (t1, t2)`, halves of n | 1 000 | 95.6 µs [88.2–112.4] | 796 % |
| `Table.merge (K true) (t1, t2)`, halves of n | 20 000 | **2.80 ms** [2.52–3.41] | 23 357 % |
| `Table.merge (K true) (t1, t2)`, halves of n | 200 000 | 61.3 ms [44.8–96.4] | 511 150 % |
| `Hash_Table.make (Hash_Table.dest t)` — today's fork copy | 256 | 9.2 µs [8.4–20.9] | 76 % |
| `Hash_Table.make (Hash_Table.dest t)` — today's fork copy | 1 000 | 41.5 µs [37.7–53.1] | 346 % |
| `Hash_Table.make (Hash_Table.dest t)` — today's fork copy | 20 000 | **0.92 ms** [0.81–1.91] | 7 668 % |
| `Hash_Table.make (Hash_Table.dest t)` — today's fork copy | 200 000 | 40.1 ms [30.7–90.3] | 334 546 % |

`Table.merge (K true) (empty, t)` is flat to within measurement noise across a factor of 780 in n.
That confirms the `is_empty` short-circuit at `table.ML:544` makes the first form genuinely O(1): it
returns `tab2` by pointer without touching it.

### Cross-run corroboration

Three independent processes, 9 rounds each. Medians drift with machine load; the per-round minima
are far more reproducible, because a minimum is the round that got least interfered with.

| Measurement | run 1 median / min | run 2 median / min | run 3 median / min |
| --- | ---: | ---: | ---: |
| lookup hit, hash, n = 20 000 | 29.1 / 26.7 | 173.8 / 33.1 | 149.6 / 35.1 |
| lookup hit, tree, n = 20 000 | 283.6 / 234.8 | 539.7 / 223.7 | 656.6 / 238.1 |
| `Synchronized.var` round trip | 77.8 / 56.7 | 92.9 / 60.7 | 124.0 / 68.8 |
| `Synchronized.var` allocation | 55.6 / 37.4 | 64.0 / 40.8 | 77.1 / 44.6 |
| `digest128_hasher` | 7.2 / 5.6 | 8.4 / 6.5 | 14.7 / 6.1 |
| `merge (K true) (empty, t)`, n = 200 000 | 1.8 / 1.6 | 2.5 / 1.7 | 3.0 / 1.9 |
| `merge (K true) (t1, t2)`, halves of 20 000 | 2.80 ms / 2.52 ms | 3.85 ms / 2.99 ms | 5.43 ms / 2.83 ms |

The tree's 20,000-entry lookup minimum is 234.8, 223.7 and 238.1 ns in the three processes — agreement
within 6 %. The 10,000-into-10,000 merge minimum is 2.52, 2.99 and 2.83 ms — agreement within 18 %.
Whichever statistic you prefer, the conclusion does not move: the lookup gap is a couple of hundred
nanoseconds against a 12,000 ns alternative, and the merge is milliseconds.

### Crossover points (run 3, which added n = 2 000 / 4 000 / 8 000)

Tree lookup, key present, run 3:

| n | median | min | min as % of 12 µs |
| ---: | ---: | ---: | ---: |
| 256 | 45.5 | 34.5 | 0.29 % |
| 1 000 | 117.1 | 81.2 | 0.68 % |
| 2 000 | 208.0 | 136.3 | 1.14 % |
| 4 000 | 335.4 | 155.1 | 1.29 % |
| 8 000 | 327.7 | 188.4 | 1.57 % |
| 20 000 | 656.6 | 238.1 | 1.98 % |
| 200 000 | 1517.9 | 952.3 | 7.94 % |

1 % of a miss (120 ns) is crossed between n = 1,000 and n = 2,000.

---

## How this was measured, and what state the machine was in

**Environment.** `source /home/qiyuan/Current/MLML/envir.sh`, then
`isabelle ML_process -l Pure -f <file>` — the Isabelle2025-2 distribution in `contrib/`, Poly/ML
5.9.2 on x86_64-linux. `Multithreading.max_threads ()` reported **8**; the benchmark itself is
single-threaded, but Poly/ML's garbage collector is not, which matters for reading the GC column
below. No Isabelle session was built and no server was started; nothing in the repository was
modified.

I loaded `-l Pure` and pulled the hash table in with
`use "…/contrib/Performant_Isabelle_ML/library/hash_table.ML"` rather than using
`-l Performant_Isabelle_ML`, because `ML_process -f` evaluates the file in the raw Poly/ML toplevel,
where the functors that the `Performant_Isabelle_ML` heap declared inside a theory's ML name space
are not visible (`Functor (Hash_Table) has not been declared`). The source file is the same file the
production code uses, and this way both structures are compiled by the same compiler invocation in
the same process, which is the fairer arrangement anyway.

**Keys.** `Word64.word * Word64.word`, generated by SplitMix64 with fixed seeds (`0x1` for the
present keys, `0x5EED0777` for the absent keys, `0x31337BEEF` for the fresh insert keys) — no
`Random`, and nothing that varies between runs. The process asserts that all 420,000 generated keys
are distinct before it measures anything, and prints the assertion's result. Note that on 64-bit
Poly/ML the native word is 63 bits, so `Word64.word` is a boxed value: both `Word64.compare` in the
tree's `ord` and structural equality in the hash table's `eq` chase a pointer. Both designs pay
that, and the production key type is exactly this type.

**Hash table construction matches production.** Tables are built with `Hash_Table.empty 1024`, the
same initial hint `Universal_Key` uses for `Digest_Tab.empty 1024`, and then filled by `update`, so
the load factors are the ones production actually reaches.

**Honesty measures.**

- Every measurement is calibrated once (which also serves as the warm-up) by doubling the iteration
  count from 1 until the measured interval reaches 60 ms, then that fixed count is used for all 9
  rounds. Calibration results are discarded from the log before the rounds start. The calibrated
  counts are printed (`iters …` lines in the raw logs) — they range from 1 iteration for a
  200,000-entry merge up to 67 million for `merge (empty, t)`.
- The hash and the tree run adjacently inside each round for each measurement (hash lookup hit, tree
  lookup hit, hash lookup miss, tree lookup miss, hash insert, tree insert, …), so drift and GC
  within a round hit both.
- Every loop accumulates a `Word64.word` derived from the values it retrieved; the accumulators are
  XOR-folded into a global `sink` that is printed at the end (`sink = 521164C99CD422A6` for run 1),
  so nothing can be discarded by the optimiser.
- Medians and full min–max are reported for all 9 rounds. No round was dropped and no pair was
  hand-picked. The raw per-round numbers are in the log files listed below, one `RAW` line per round
  per measurement.
- For the insert measurement, the mutable hash table cannot simply discard the result the way the
  persistent tree can, so both are measured the same way: insert a batch of `max(n/10, 64)` fresh
  keys into a table already holding n, and divide by the batch size. Between batches the hash table
  is rebuilt from scratch, and **that rebuild is outside the timed region** (the benchmark
  accumulates the timed intervals itself rather than wrapping the whole loop). The tree needs no
  rebuild because the starting table is persistent.

**Garbage collection.** `Timing.result` reports a `gc` field, and it is included per round in the
raw logs. It is **CPU time summed over Poly/ML's GC threads, not wall time** — for run 1 round 5 of
the n = 256 tree insert, `gc` is 810 ms against an elapsed 541 ms, which is only possible if several
threads are collecting at once. GC dominated a handful of individual rounds, always on the
allocating (tree insert, tree build) measurements and once on the `Synchronized.var` round trip
(run 1 round 2: 882 ms of GC, and that round's 558 ns is the maximum of the reported 57–558 ns
spread against a 78 ns median). No hash-table lookup measurement had any GC attributed to it in most
rounds. Because the reported statistic is the median of 9, a GC-heavy round moves the max but not
the headline figure.

**Machine state — this box was busy and I did not have it to myself.** 14 logical cores, Linux
6.17. Throughout the measurements six `veriT` processes were running at roughly 100 % CPU each,
alongside two `java` processes and several other `poly` processes belonging to other agents' work.
One-minute load average: about 10.3 just before run 1, falling to 4.9 by the end of run 1; about 9.0
at the start of run 2; and about 17.0 by the end of run 3. That is the whole explanation for the
inflated medians in runs 2 and 3, and for the wide max values throughout. It is also why the report
gives per-run minima alongside the medians: on a contended box the minimum is the closest thing
available to an uncontended measurement, and the three processes' minima agree with each other far
better than their medians do. I did not pin the process to a core and did not renice it.

**Rounds.** 9 rounds per run (the brief asked for at least 7), in each of 3 independent processes.
Run 1 and run 2 covered n ∈ {256, 1 000, 20 000, 200 000}; run 3 covered
n ∈ {256, 1 000, 2 000, 4 000, 8 000, 20 000, 200 000} to locate the crossover.

**Files.**

- benchmark source: `/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/bench.ML`
- same source with the extra sizes: `…/scratchpad/bench3.ML` (identical except for the `sizes` list)
- raw logs: `…/scratchpad/bench_run1.log`, `bench_run2.log`, `bench_run3.log`

---

## Things that surprised me, and things I could not measure

**The lock costs more than the data structure.** The `Synchronized.var` round trip with nothing
inside it — 78 ns median, 57 ns at best — is two and a half times the whole 20,000-entry hash-table
lookup (29 ns) and about a quarter of the 20,000-entry tree lookup (284 ns). The current design
already pays this on every cache access. So the "O(1) versus O(log n)" comparison is being made
underneath a constant that is larger than the O(1) term.

**`merge (K true) (empty, t)` is exactly as free as the short-circuit promises.** 1.7–1.9 ns and
completely flat from 256 to 200,000 entries, in all three processes. This is a real design lever: a
`construct` that folds parents starting from `empty` pays nothing for the first parent regardless of
its size.

**The hash table's insert got *cheaper* from n = 1,000 to n = 20,000** (38 ns → 34 ns in run 1).
That is a load-factor artefact, not a mystery: the table rehashes to a capacity of about four times
the used count, so its load factor oscillates between 25 % and 75 % as it grows, and the n = 20,000
fixture happens to sit at a 30 % load in a 65,536-slot array while n = 1,000 sits at 24 % in a 4,096-
slot one with a different cache profile.

**A caveat I want on the record about the insert numbers.** Because the batch size is n/10 and the
`Hash_Table` rehash threshold is 75 % of capacity, *no rehash occurs inside any timed insert region*
at any of the four sizes. The hash-table insert figures therefore exclude rehash amortisation. The
"build from empty to n, per key" row does include it, and shows the hash table at 29–228 ns per key
against the tree's 181–1802 ns, so including it does not change any conclusion.

**Things I could not measure here.**

- `Term_Digest.thm128`, which every cache access calls to produce the key, needs a real `thm` and a
  theory context, so it is not in this benchmark. It is on both designs' paths identically, but it
  means the real per-access cost of either design is higher than what is tabulated here, which makes
  the 255 ns gap an even smaller share of the total.
- `compute_constituents` itself. I took the 12–15 µs figure from the brief and used 12 µs throughout
  (the conservative end — using 15 µs would make every percentage smaller).
- Real lock contention. The benchmark is single-threaded, so the 78 ns round trip is the uncontended
  cost. Under real parallel theory processing the lock cost of *both* designs rises, and the
  redesign holds the lock for longer per access (284 ns of tree walk instead of 29 ns of probing),
  which would widen the gap under contention in a way this measurement cannot quantify.
- One structural note rather than a measurement gap: the brief calls
  `functor Table(Key: KEY)` a red-black tree. It is not — `contrib/Isabelle2025-2/src/Pure/General/table.ML:85-91`
  defines a 2-3 tree (`Leaf1`/`Leaf2`/`Leaf3`, `Branch2`/`Branch3`). This does not change any number
  above; it is still O(log n), just with a smaller depth constant than a red-black tree would have.

---

## Benchmark source (exact)

Run as `isabelle ML_process -l Pure -f bench.ML`. `bench3.ML` differs only in the `sizes` list.

```sml
(* ---------------------------------------------------------------------------
   Pure Table (2-3 tree, Pure/General/table.ML) vs mutable Hash_Table
   (Performant_Isabelle_ML/library/hash_table.ML), keyed by
   Term_Digest.digest128 = Word64.word * Word64.word.

   Run:  isabelle ML_process -l Pure -f bench.ML
   --------------------------------------------------------------------------- *)

use "/home/qiyuan/Current/MLML/contrib/Performant_Isabelle_ML/library/hash_table.ML";

type k128 = Word64.word * Word64.word;
type v128 = Word64.word * int;   (* small tuple, stands in for the cached triple *)

(* verbatim copy of Term_Digest.digest128_hasher (Isabelle_RPC/Tools/Term_Digest.ML:185) *)
fun digest_hasher (w : Word64.word) : word = Word.fromLargeWord (Word64.toLargeWord w);
fun digest128_hasher ((lo, hi) : k128) : word =
  Word.xorb (digest_hasher lo, Word.fromLargeWord (Word64.toLargeWord (Word64.>> (hi, 0w1))));

structure HT = Hash_Table(struct
  type key = k128
  val hash = digest128_hasher
  val eq = op = : k128 * k128 -> bool
end);

structure TT = Table(type key = k128 val ord = prod_ord Word64.compare Word64.compare);


(* ---------------- deterministic key generation: SplitMix64 ---------------- *)

val sm_gamma = 0wx9E3779B97F4A7C15 : Word64.word;
val sm_m1 = 0wxBF58476D1CE4E5B9 : Word64.word;
val sm_m2 = 0wx94D049BB133111EB : Word64.word;

fun sm_next (s : Word64.word) =
  let
    val s' = Word64.+ (s, sm_gamma);
    val z = s';
    val z = Word64.* (Word64.xorb (z, Word64.>> (z, 0w30)), sm_m1);
    val z = Word64.* (Word64.xorb (z, Word64.>> (z, 0w27)), sm_m2);
    val z = Word64.xorb (z, Word64.>> (z, 0w31));
  in (z, s') end;

fun gen_keys n seed : k128 Array.array =
  let
    val arr = Array.array (n, (0w0, 0w0) : k128);
    fun go i s =
      if i >= n then ()
      else
        let
          val (lo, s1) = sm_next s;
          val (hi, s2) = sm_next s1;
        in Array.update (arr, i, (lo, hi)); go (i + 1) s2 end;
  in go 0 seed; arr end;

val n_max = 200000;
val n_extra = 20000;

val present = gen_keys n_max (0wx1 : Word64.word);
val misses  = gen_keys n_max (0wx5EED0777 : Word64.word);
val extras  = gen_keys n_extra (0wx31337BEEF : Word64.word);

fun value_of (arr : k128 Array.array) i : v128 = (#1 (Array.sub (arr, i)), i);

(* sanity: all 420000 generated keys distinct *)
val () =
  let
    val t = HT.empty 1024 : unit HT.table;
    fun add arr =
      Array.app (fn k => HT.update t (k, ())) arr;
  in
    add present; add misses; add extras;
    writeln ("distinct keys generated: " ^ string_of_int (HT.size t) ^
             " (expected " ^ string_of_int (2 * n_max + n_extra) ^ ")")
  end;


(* ---------------- construction ---------------- *)

fun build_ht n : v128 HT.table =
  let
    val t = HT.empty 1024;      (* production uses Digest_Tab.empty 1024 *)
    fun go i = if i >= n then () else (HT.update t (Array.sub (present, i), value_of present i); go (i + 1));
  in go 0; t end;

fun build_tt n : v128 TT.table =
  let
    fun go i acc = if i >= n then acc else go (i + 1) (TT.update (Array.sub (present, i), value_of present i) acc);
  in go 0 TT.empty end;

(* tree over a slice [lo, hi) of present *)
fun build_tt_slice lo hi : v128 TT.table =
  let
    fun go i acc = if i >= hi then acc else go (i + 1) (TT.update (Array.sub (present, i), value_of present i) acc);
  in go lo TT.empty end;


(* ---------------- timing harness ---------------- *)

type stamp = {elapsed : Time.time, cpu : Time.time, gc : Time.time};

fun timed (f : unit -> Word64.word) : Word64.word * stamp =
  let
    val start = Timing.start ();
    val r = f ();
    val t = Timing.result start;
  in (r, t) end;

fun add_stamp (a : stamp, b : stamp) : stamp =
  {elapsed = Time.+ (#elapsed a, #elapsed b),
   cpu = Time.+ (#cpu a, #cpu b),
   gc = Time.+ (#gc a, #gc b)};

val zero_stamp : stamp = {elapsed = Time.zeroTime, cpu = Time.zeroTime, gc = Time.zeroTime};

(* a benchmark: given an iteration count, produce an accumulator + the time
   attributable to the measured work only *)
type bench = int -> Word64.word * stamp * int;   (* acc, time, ops actually done *)

fun simple (f : int -> Word64.word) : bench = fn iters =>
  let val (a, t) = timed (fn () => f iters) in (a, t, iters) end;

(* the global sink: printed at the end so nothing can be optimised away *)
val sink = Unsynchronized.ref (0w0 : Word64.word);
fun absorb w = sink := Word64.xorb (! sink, w);

(* log: (name, n, round, picoseconds-per-op, gc ns, elapsed ns) *)
val log = Unsynchronized.ref ([] : (string * int * int * int * int * int) list);

fun run_bench name n round (b : bench) iters =
  let
    val (acc, t, ops) = b iters;
    val ns = Time.toNanoseconds (#elapsed t);
    val ps = ns * 1000 div ops;
  in
    absorb acc;
    log := (name, n, round, ps, Time.toNanoseconds (#gc t), ns) :: ! log
  end;

(* calibrate: smallest power-of-two-scaled iteration count reaching >= 60ms *)
fun calibrate (b : bench) =
  let
    fun go it =
      let
        val (acc, t, _) = b it;
        val _ = absorb acc;
      in
        if Time.toMilliseconds (#elapsed t) >= 60 orelse it >= 100000000 then it
        else go (it * 2)
      end;
  in go 1 end;


(* ---------------- the individual benchmarks ---------------- *)

fun ht_lookup_hit (t : v128 HT.table) n = simple (fn iters =>
  let
    fun go i j acc =
      if i >= iters then acc
      else
        let
          val k = Array.sub (present, j);
          val acc' = case HT.lookup t k of SOME (w, _) => Word64.xorb (acc, w) | NONE => acc;
        in go (i + 1) (if j + 1 >= n then 0 else j + 1) acc' end;
  in go 0 0 (0w0 : Word64.word) end);

fun tt_lookup_hit (t : v128 TT.table) n = simple (fn iters =>
  let
    fun go i j acc =
      if i >= iters then acc
      else
        let
          val k = Array.sub (present, j);
          val acc' = case TT.lookup t k of SOME (w, _) => Word64.xorb (acc, w) | NONE => acc;
        in go (i + 1) (if j + 1 >= n then 0 else j + 1) acc' end;
  in go 0 0 (0w0 : Word64.word) end);

fun ht_lookup_miss (t : v128 HT.table) n = simple (fn iters =>
  let
    fun go i j acc =
      if i >= iters then acc
      else
        let
          val k = Array.sub (misses, j);
          val acc' = case HT.lookup t k of SOME (w, _) => Word64.xorb (acc, w) | NONE => Word64.+ (acc, 0w1);
        in go (i + 1) (if j + 1 >= n then 0 else j + 1) acc' end;
  in go 0 0 (0w0 : Word64.word) end);

fun tt_lookup_miss (t : v128 TT.table) n = simple (fn iters =>
  let
    fun go i j acc =
      if i >= iters then acc
      else
        let
          val k = Array.sub (misses, j);
          val acc' = case TT.lookup t k of SOME (w, _) => Word64.xorb (acc, w) | NONE => Word64.+ (acc, 0w1);
        in go (i + 1) (if j + 1 >= n then 0 else j + 1) acc' end;
  in go 0 0 (0w0 : Word64.word) end);

(* insert m fresh keys into a table already holding n; the rebuild between
   batches is NOT timed *)
fun batch_size n = Int.max (n div 10, 64);

fun ht_insert n : bench = fn iters =>
  let
    val m = batch_size n;
    val nb = Int.max (iters div m, 1);
    fun batch b (acc, st) =
      if b >= nb then (acc, st)
      else
        let
          val t = build_ht n;   (* untimed reset *)
          val (acc', t') = timed (fn () =>
            let
              fun go i a =
                if i >= m then a
                else
                  let
                    val k = Array.sub (extras, i);
                  in HT.update t (k, (#1 k, i)); go (i + 1) (Word64.xorb (a, #1 k)) end;
            in go 0 acc end);
        in batch (b + 1) (acc', add_stamp (st, t')) end;
    val (a, st) = batch 0 (0w0 : Word64.word, zero_stamp);
  in (a, st, nb * m) end;

fun tt_insert (t0 : v128 TT.table) n : bench = fn iters =>
  let
    val m = batch_size n;
    val nb = Int.max (iters div m, 1);
    fun batch b (acc, st) =
      if b >= nb then (acc, st)
      else
        let
          val (acc', t') = timed (fn () =>
            let
              fun go i a tab =
                if i >= m then (if TT.is_empty tab then Word64.+ (a, 0w1) else a)
                else
                  let val k = Array.sub (extras, i)
                  in go (i + 1) (Word64.xorb (a, #1 k)) (TT.update (k, (#1 k, i)) tab) end;
            in go 0 acc t0 end);
        in batch (b + 1) (acc', add_stamp (st, t')) end;
    val (a, st) = batch 0 (0w0 : Word64.word, zero_stamp);
  in (a, st, nb * m) end;

(* build from empty to n, per key (includes hash-table rehashing) *)
fun ht_build n : bench = fn iters =>
  let
    val nb = Int.max (iters div n, 1);
    fun batch b (acc, st) =
      if b >= nb then (acc, st)
      else
        let
          val (acc', t') = timed (fn () =>
            let val t = build_ht n in Word64.+ (acc, Word64.fromInt (HT.size t)) end);
        in batch (b + 1) (acc', add_stamp (st, t')) end;
    val (a, st) = batch 0 (0w0 : Word64.word, zero_stamp);
  in (a, st, nb * n) end;

fun tt_build n : bench = fn iters =>
  let
    val nb = Int.max (iters div n, 1);
    fun batch b (acc, st) =
      if b >= nb then (acc, st)
      else
        let
          val (acc', t') = timed (fn () =>
            let val t = build_tt n in if TT.is_empty t then Word64.+ (acc, 0w1) else acc end);
        in batch (b + 1) (acc', add_stamp (st, t')) end;
    val (a, st) = batch 0 (0w0 : Word64.word, zero_stamp);
  in (a, st, nb * n) end;

(* Synchronized.var round trip with no table work at all *)
val sync_v = Synchronized.var "Universal_Key.cache_scope" (0 : int);
val sync_roundtrip = simple (fn iters =>
  let
    fun go i acc =
      if i >= iters then acc
      else
        let val r = Synchronized.change_result sync_v (fn s => (s + 1, s + 1))
        in go (i + 1) (Word64.+ (acc, Word64.fromInt (r mod 2))) end;
  in go 0 (0w0 : Word64.word) end);

(* Synchronized.var allocation (one per theory begin in the redesign) *)
val sync_alloc = simple (fn iters =>
  let
    fun go i acc =
      if i >= iters then acc
      else
        let val v = Synchronized.var "Universal_Key.cache_scope" (i, TT.empty : v128 TT.table)
        in go (i + 1) (Word64.+ (acc, Word64.fromInt (#1 (Synchronized.value v) mod 2))) end;
  in go 0 (0w0 : Word64.word) end);

val hasher_only = simple (fn iters =>
  let
    fun go i j acc =
      if i >= iters then acc
      else
        let val h = digest128_hasher (Array.sub (present, j))
        in go (i + 1) (if j + 1 >= n_max then 0 else j + 1)
             (Word64.xorb (acc, Word64.fromLargeWord (Word.toLargeWord h))) end;
  in go 0 0 (0w0 : Word64.word) end);

(* Table.merge (K true) (empty, t) *)
fun tt_merge_empty (t : v128 TT.table) = simple (fn iters =>
  let
    fun go i acc =
      if i >= iters then acc
      else
        let val r = TT.merge (K true) (TT.empty, t)
        in go (i + 1) (if TT.is_empty r then Word64.+ (acc, 0w1) else acc) end;
  in go 0 (0w0 : Word64.word) end);

(* Table.merge (K true) (t1, t2), each of size n/2, disjoint *)
fun tt_merge_half (t1 : v128 TT.table, t2 : v128 TT.table) = simple (fn iters =>
  let
    fun go i acc =
      if i >= iters then acc
      else
        let val r = TT.merge (K true) (t1, t2)
        in go (i + 1) (if TT.is_empty r then Word64.+ (acc, 0w1) else acc) end;
  in go 0 (0w0 : Word64.word) end);

(* what the CURRENT design pays on a cache-scope fork: Digest_Tab.make (dest t) *)
fun ht_copy (t : v128 HT.table) = simple (fn iters =>
  let
    fun go i acc =
      if i >= iters then acc
      else
        let val t' = HT.make (HT.dest t)
        in go (i + 1) (Word64.+ (acc, Word64.fromInt (HT.size t' mod 2))) end;
  in go 0 (0w0 : Word64.word) end);


(* ---------------- the run ---------------- *)

val sizes = [256, 1000, 20000, 200000];

(* per-size fixtures, built once *)
val fixtures =
  map (fn n =>
    let
      val ht = build_ht n;
      val tt = build_tt n;
      val h = n div 2;
      val tt1 = build_tt_slice 0 h;
      val tt2 = build_tt_slice h n;
    in (n, ht, tt, tt1, tt2) end) sizes;

val () = List.app (fn (n, ht, tt, tt1, tt2) =>
  writeln ("fixture n=" ^ string_of_int n ^
           " hash_size=" ^ string_of_int (HT.size ht) ^
           " tree_size=" ^ string_of_int (TT.size tt) ^
           " halves=" ^ string_of_int (TT.size tt1) ^ "+" ^ string_of_int (TT.size tt2) ^
           " merged=" ^ string_of_int (TT.size (TT.merge (K true) (tt1, tt2))))) fixtures;

(* one round = every measurement once, hash and tree interleaved *)
fun round r (iter_of : string * int -> int) =
  let
    fun it name n = iter_of (name, n);
    val () = List.app (fn (n, ht, tt, tt1, tt2) =>
      (run_bench "lookup_hit/hash" n r (ht_lookup_hit ht n) (it "lookup_hit" n);
       run_bench "lookup_hit/tree" n r (tt_lookup_hit tt n) (it "lookup_hit" n);
       run_bench "lookup_miss/hash" n r (ht_lookup_miss ht n) (it "lookup_miss" n);
       run_bench "lookup_miss/tree" n r (tt_lookup_miss tt n) (it "lookup_miss" n);
       run_bench "insert/hash" n r (ht_insert n) (it "insert" n);
       run_bench "insert/tree" n r (tt_insert tt n) (it "insert" n);
       run_bench "build/hash" n r (ht_build n) (it "build" n);
       run_bench "build/tree" n r (tt_build n) (it "build" n);
       run_bench "copy/hash" n r (ht_copy ht) (it "copy" n);
       run_bench "merge_empty/tree" n r (tt_merge_empty tt) (it "merge_empty" n);
       run_bench "merge_half/tree" n r (tt_merge_half (tt1, tt2)) (it "merge_half" n)))
      fixtures;
  in
    run_bench "sync_roundtrip" 0 r sync_roundtrip (it "sync_roundtrip" 0);
    run_bench "sync_var_alloc" 0 r sync_alloc (it "sync_var_alloc" 0);
    run_bench "hasher" 0 r hasher_only (it "hasher" 0)
  end;

(* calibration (also serves as warm-up) *)
val () = writeln "calibrating ...";
val calib =
  let
    val per_size =
      maps (fn (n, ht, tt, tt1, tt2) =>
        [(("lookup_hit", n), calibrate (ht_lookup_hit ht n)),
         (("lookup_miss", n), calibrate (ht_lookup_miss ht n)),
         (("insert", n), calibrate (ht_insert n)),
         (("build", n), calibrate (ht_build n)),
         (("copy", n), calibrate (ht_copy ht)),
         (("merge_empty", n), calibrate (tt_merge_empty tt)),
         (("merge_half", n), calibrate (tt_merge_half (tt1, tt2)))]) fixtures;
    (* lookups/inserts: take the max of the hash- and tree-calibrated counts so
       both structures run the same number of operations *)
    val per_size2 =
      maps (fn (n, ht, tt, _, _) =>
        [(("lookup_hit", n), calibrate (tt_lookup_hit tt n)),
         (("lookup_miss", n), calibrate (tt_lookup_miss tt n)),
         (("insert", n), calibrate (tt_insert tt n))]) fixtures;
    val glob =
      [(("sync_roundtrip", 0), calibrate sync_roundtrip),
       (("sync_var_alloc", 0), calibrate sync_alloc),
       (("hasher", 0), calibrate hasher_only)];
    val all = per_size @ per_size2 @ glob;
  in
    fold (fn (k, v) => fn tab =>
      AList.map_default (op =) (k, v) (fn old => Int.max (old, v)) tab) all []
  end;

fun iter_of key = the (AList.lookup (op =) calib key);

val () = List.app (fn ((nm, n), i) =>
  writeln ("iters " ^ nm ^ " n=" ^ string_of_int n ^ ": " ^ string_of_int i)) calib;

(* discard calibration noise from the log *)
val () = log := [];

val n_rounds = 9;
val () = writeln ("running " ^ string_of_int n_rounds ^ " rounds ...");
val () =
  let
    fun go r = if r > n_rounds then () else (round r iter_of; writeln ("round " ^ string_of_int r ^ " done"); go (r + 1));
  in go 1 end;


(* ---------------- report ---------------- *)

fun median xs =
  let val s = sort int_ord xs in nth s (length s div 2) end;

val entries = rev (! log);
val names = distinct (op =) (map (fn (nm, n, _, _, _, _) => (nm, n)) entries);

fun ps_to_ns_str ps = Real.fmt (StringCvt.FIX (SOME 1)) (Real.fromInt ps / 1000.0);

val () = writeln "";
val () = writeln "== raw: name n round ns_per_op gc_ns elapsed_ns ==";
val () = List.app (fn (nm, n, r, ps, gc, el) =>
  writeln ("RAW\t" ^ nm ^ "\t" ^ string_of_int n ^ "\t" ^ string_of_int r ^ "\t" ^
           ps_to_ns_str ps ^ "\t" ^ string_of_int gc ^ "\t" ^ string_of_int el)) entries;

val () = writeln "";
val () = writeln "== summary: name n iters median_ns min_ns max_ns gc_ns_total elapsed_ns_total pct_of_12us ==";
val () = List.app (fn (nm, n) =>
  let
    val sel = filter (fn (nm', n', _, _, _, _) => nm' = nm andalso n' = n) entries;
    val pss = map (fn (_, _, _, ps, _, _) => ps) sel;
    val gcs = map (fn (_, _, _, _, gc, _) => gc) sel;
    val els = map (fn (_, _, _, _, _, el) => el) sel;
    val med = median pss;
    val iters = iter_of (hd (String.tokens (fn c => c = #"/") nm), n)
      handle _ => 0;
    val pct = Real.fromInt med / 1000.0 / 12000.0 * 100.0;
  in
    writeln ("SUM\t" ^ nm ^ "\t" ^ string_of_int n ^ "\t" ^ string_of_int iters ^ "\t" ^
             ps_to_ns_str med ^ "\t" ^ ps_to_ns_str (fold (fn x => fn a => Int.min (x, a)) pss med) ^ "\t" ^
             ps_to_ns_str (fold (fn x => fn a => Int.max (x, a)) pss med) ^ "\t" ^
             string_of_int (fold (curry (op +)) gcs 0) ^ "\t" ^
             string_of_int (fold (curry (op +)) els 0) ^ "\t" ^
             Real.fmt (StringCvt.FIX (SOME 4)) pct)
  end) names;

val () = writeln "";
val () = writeln ("sink = " ^ Word64.toString (! sink));
val () = writeln ("threads = " ^ string_of_int (Multithreading.max_threads ()));
```
