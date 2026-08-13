# Cost of computing a theorem's constituent theories over every static fact of `Complex_Main`

## Answer

**30,340 thms, 27,959 distinct propositions; without the cache 228 ms total / 7.53 µs per thm; with
the cache 251 ms / 8.29 µs.** Those are medians of 15 interleaved rounds (full ranges: without the
cache 205–302 ms, 6.75–9.96 µs/thm; with the cache 228–377 ms, 7.53–12.44 µs/thm). The cache makes a
single pass over this population about 10% *slower*, not faster, and the population breakdown says
exactly why: 27,959 of 30,340 propositions are distinct, so 92.15% of the calls are misses that pay
the cache's bookkeeping on top of the full computation, and only 7.85% are hits that avoid it. A
*second* pass with the cache now full costs 35 ms / 1.17 µs per thm — 6.4× faster than no cache —
so the cache pays off only when the same propositions are read again, never within one sweep of a
theory's own facts.

The two reading contexts were checked for agreement over the **entire** population, not a sample:
0 of 30,340 thms produced a different `(xor hash, constituent list, report)` triple. The
computation was also exact — `Universal_Key.constituents_totals ()` reported `skipped = 0` and
`empty_name_fallback = 0` both before and after all rounds, so no internal name failed to resolve
and no result fell back to the reading context's own theory.

## Population

| Quantity | Value |
| --- | --- |
| Static facts of `Complex_Main` (`Facts.dest_static false []`) | 26,713 |
| Individual thms after flattening | 30,340 |
| Distinct `Term_Digest.thm128` values among them | 27,959 |
| Distinct / total | 92.15% |
| Duplicate rate = cache hit rate on a cold pass | 7.85% |
| Theories in `Complex_Main`'s cone | 117 |
| Theories in the probe theory's cone (adds Isabelle_RPC's) | 120 |

The duplicate rate is the whole story of the measurement. `thm128` digests the *proposition*, so the
2,381 duplicates are facts stated identically under different names (aliases, `lemmas` re-exports,
members of collections that repeat a rule). Every other call must run the full computation anyway.

## The two regimes, and how they were reached

`Universal_Key` has two entry points and only one of them consults a cache:

- `compute_constituents : Context.generic -> term -> hash * constituent list * report` — the raw
  computation, never touches the cache.
- `thm_constituents : Context.generic -> thm -> ...` — looks the thm's `Term_Digest.thm128` up in a
  cache held in `Theory_Data`, and **bypasses the cache entirely** when the reading theory's
  `Cache_Scope` data is `No_Cache`.

So the faithful A/B is `thm_constituents` called in two different reading theories, which is what
production does:

- **Without the cache** — reading theory `Complex_Main`, straight out of the `HOL` heap.
  `Universal_Key.cache_scope_id @{theory Complex_Main}` = `NONE`, as printed by the probe. The
  `Theory.at_begin` hook that allocates a cache is registered while `Universal_Key.ML` is being
  loaded inside `Isabelle_RPC.Remote_Procedure_Calling`, so it only ever ran for theories begun
  after that point; nothing in a `HOL` heap qualifies.
- **With the cache** — a theory begun by the probe itself,
  `Theory.begin_theory ("Probe_Cache_i", …) [Complex_Main, Remote_Procedure_Calling]`. Its cone
  contains the theory that registered the hook, so the hook runs at `begin` and allocates a cache;
  `cache_scope_id` came back `SOME 5146278`, `SOME 5146286`, … one distinct id per round.

A round gets a **fresh, empty** cache because both parents carry `No_Cache` (`Remote_Procedure_Calling`
itself has `cache_scope_id = NONE` — the hook is registered inside its body, after its own `begin`),
so `Cache_Scope`'s merge yields `No_Cache` and `claim_cache_scope` takes its allocating branch. The
15 distinct scope ids in the rounds table confirm this, and so does the warm re-pass being 7× faster
than the pass that filled it.

Both reading contexts have `Complex_Main` in their cone, so every constant and type constructor
resolves in both.

## Rounds

15 rounds. Within each round the passes are interleaved, and the order is reversed on odd rounds
(`D, C, B, A`) versus even rounds (`A, B, C, D`), so neither regime is systematically first or last.
All figures are elapsed ms over the whole 30,340-thm population; `gc` is the GC time Poly/ML
attributed to that pass (it is summed over GC threads, which is why it sometimes exceeds elapsed).

- **A** = `thm_constituents` in `Complex_Main` (no cache) — the production "without cache".
- **B** = `thm_constituents` in the round's fresh cache theory (cold cache) — the production "with cache".
- **C** = `compute_constituents ctx (Thm.prop_of thm)` in `Complex_Main`.
- **D** = `compute_constituents ctx (Thm.prop_of thm)` in the round's cache theory.
- **E** = a second **B** pass in the same round, cache now full (bonus, not part of the A/B question).

| Round | A ms | B ms | C ms | D ms | E ms |
| --- | --- | --- | --- | --- | --- |
| 1  | 204.82 | 257.59 | 260.19 | 298.45 | 35.27 |
| 2  | 228.31 | 258.97 | 205.43 | 485.39 | 52.26 |
| 3  | 248.14 | 228.33 | 296.21 | 288.20 | 34.85 |
| 4  | 227.55 | 240.34 | 246.10 | 215.75 | 35.90 |
| 5  | 302.02 | 377.49 | 282.62 | 523.04 | 35.48 |
| 6  | 219.39 | 232.34 | 210.90 | 256.15 | 34.99 |
| 7  | 261.79 | 250.89 | 239.69 | 217.63 | 35.72 |
| 8  | 227.44 | 269.64 | 231.55 | 252.72 | 35.28 |
| 9  | 221.50 | 261.40 | 243.78 | 230.20 | 37.45 |
| 10 | 255.24 | 259.36 | 254.84 | 223.08 | 34.84 |
| 11 | 226.28 | 251.44 | 235.50 | 230.28 | 41.20 |
| 12 | 231.77 | 246.65 | 253.65 | 229.88 | 35.27 |
| 13 | 224.32 | 248.24 | 244.58 | 228.65 | 35.74 |
| 14 | 261.13 | 237.11 | 222.53 | 265.05 | 35.10 |
| 15 | 232.14 | 281.81 | 220.18 | 220.14 | 36.79 |

Median and full min–max over those 15 rounds:

| Pass | median ms | min–max ms | median µs/thm | min–max µs/thm |
| --- | --- | --- | --- | --- |
| A — `thm_constituents`, no cache | 228.31 | 204.82 – 302.02 | 7.53 | 6.75 – 9.96 |
| B — `thm_constituents`, cold cache | 251.44 | 228.33 – 377.49 | 8.29 | 7.53 – 12.44 |
| C — `compute_constituents`, `Complex_Main` | 243.78 | 205.43 – 296.21 | 8.04 | 6.77 – 9.76 |
| D — `compute_constituents`, cache theory | 230.28 | 215.75 – 523.04 | 7.59 | 7.11 – 17.24 |
| E — `thm_constituents`, warm cache | 35.48 | 34.84 – 52.26 | 1.17 | 1.15 – 1.72 |

Paired, per round, B − A is positive (cache slower) in 12 of 15 rounds; the median paired difference
is +23.92 ms, i.e. +0.79 µs per thm.

### How big is the noise, and does the A/B gap survive it

**A and C are the same code path.** In a `No_Cache` reading theory, `thm_constituents context thm`
*is* `compute_constituents context (Thm.prop_of thm)` — one extra pattern match and one
`Theory_Data` read per call. So A and C are two measurements of the same work in the same context,
and their spread is a direct read-out of this machine's noise floor: medians 7.53 vs 8.04 µs/thm,
a 0.5 µs/thm (7%) discrepancy that is by construction not a real effect.

The A/B gap, 0.76 µs/thm at the medians, is therefore only slightly larger than the noise floor.
What makes it believable is the paired sign (12/15 rounds, sign test p ≈ 0.035) and the fact that a
mechanical cost model predicts it almost exactly:

- The warm pass E costs 1.17 µs/thm. That is what the cache machinery costs when it does nothing but
  hit: one `Term_Digest.thm128` on an already-warm digest cache, plus a `Digest_Tab` lookup inside a
  `Synchronized.change_result`.
- Misses (92.15% of calls) pay that 1.17 µs *plus* the full computation, and one more critical
  section to store the result. Hits (7.85%) save the full computation, ≈ 7.5 µs.
- Predicted overhead ≈ 1.17 − 0.0785 × 7.5 = **+0.58 µs/thm**. Observed **+0.76 µs/thm**. The
  remainder is the store-side critical section and the `Digest_Tab` growth that the hit-only pass
  never pays.

**C vs D says the reading context itself is not a confound.** These are the same raw call in the two
different theories; medians 8.04 (`Complex_Main`) vs 7.59 (cache theory) µs/thm, i.e. the larger
name spaces of the merged probe theory do not systematically slow the name-space lookups. D's
205–523 ms range is driven by two rounds (2 and 5) in which Poly/ML charged that pass 550–570 ms of
GC; the median is unaffected, which is why the median is the headline number.

## Confounds handled

**`Theory_Hash.hash_of`'s per-theory RPC to Python.** Verified live, not inferred: the probe asserts
`Theory_Hash.is_persistent (Theory_Hash.hash_of @{theory Pure})` and aborts otherwise; it came back
`true`, with `Pure` hashing to `104565bfb236c0d3a121bcf876efb3a1`. It then enumerated the cone and
found that **all 117 theories of `Complex_Main`'s cone** hash on the persistent (RPC) branch — the
only WIP-branch theory anywhere in the probe's 120-theory cone is `Probe_Cache_0`, the ad-hoc theory
the probe itself created, which is never a constituent of anything (it declares no constants). The
one-off cost was taken **before** any timed round: a warm-up pass hashing every theory in the cone,
21.18 ms for 120 theories. None of that lands in a per-thm figure.

Getting the persistent branch took a change of harness and is worth recording, because the trap is
easy to fall into. Under **isabelle-mcp** the run failed with

```
Failed to launch the attached RPC host: the launched python exited before binding
The interpreter used was: /usr/bin/python3 … ModuleNotFoundError: No module named 'Isabelle_RPC_Host'
```

`Tools/RPC.ML` discovers its interpreter with `command -v python3` under Isabelle's bash, which
inherits the MCP server's environment; that server's `python3` is the system one and has no
`Isabelle_RPC_Host` wheel. Isabelle/ML's `getenv` reads the real OS environment
(`Pure/library.ML:1119`), so `ISABELLE_RPC_PYTHON` cannot be injected from inside the session, and
`python_cmd` is a memoised `Lazy` besides. Had I proceeded there, every theory would have hashed on
the FNV "WIP" branch and the numbers would have been off. The measurement was therefore run with
`isabelle process_theories` launched from a shell with
`ISABELLE_RPC_PYTHON=/home/qiyuan/Current/MLML/.venv/bin/python3`. No `isabelle build` was run in
any form; `process_theories` processes an ad-hoc `Draft` session against the already-built `HOL`
heap image (the whole session, theory loading included, takes 23 s wall).

**`Term_Digest.thm128`'s own cache.** It is keyed on the thm's name hint and confirms a hit by
comparing the stored proposition to the actual one with structural equality. The probe fills it
completely **before any timed round**, as a side effect of the pass that counts distinct digests
(that cold pass cost 270.57 ms for the whole population, ≈ 8.9 µs/thm). Both regimes therefore run
against an equally warm digest cache and neither round order can favour one — but note what this
means for interpretation: the "with cache" figure charges only the *warm* `thm128` cost. If
`thm_constituents` were the first thing in a process to digest these thms, the cache regime would
additionally pay something approaching that 8.9 µs/thm and would lose far more heavily. In
production that cold cost is not attributable to the cache, because `build_thm_key` needs `thm128`
anyway to form the key's 15-byte payload.

**Round ordering.** Interleaved within each round, with the order reversed between odd and even
rounds, so neither regime is always first (first-in-round passes tend to absorb the GC that the
previous round's allocation earned).

**Machine load.** Other agents share this 14-core box. `uptime` sampled every 10 s across the run:
1-minute load average 0.61 at start, then 1.13 / 1.04 / 1.11 / 1.02 — i.e. roughly one busy core
besides the probe, on 14. The whole `process_theories` session reported
`0:00:23 elapsed, 0:00:24 cpu, factor 1.04`, so the probe was not contending for CPU. The earlier
6-round run (same probe, `n_rounds = 6`, kept at `scratchpad/run2.log`) was taken at load 1.3 and
gave medians A = 246.2 ms / 8.11 µs and B = 262.3 ms / 8.65 µs — same ordering and magnitude, so
the result is not an artefact of one process.

**Figures that are a single observation** and are labelled as such: the population counts (26,713 /
30,340 / 27,959 — these are deterministic, not timings), the theory-hash warm-up 21.18 ms, the cold
`thm128` pass 270.57 ms, and the `Pure` hash value. Everything in the medians table is 15
observations.

## Re-running

Probe source: `scratchpad/Probe_Constituents.thy` (reproduced below verbatim). Command:

```bash
cd /home/qiyuan/Current/MLML
source ./envir.sh
export ISABELLE_RPC_PYTHON=/home/qiyuan/Current/MLML/.venv/bin/python3
SP=/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad
isabelle process_theories -O -l HOL -o editor_tracing_messages=0 \
  -D $SP -d contrib/Isabelle_RPC -d contrib/Performant_Isabelle_ML \
  Isabelle_RPC.Remote_Procedure_Calling Probe_Constituents > $SP/run.log 2>&1
grep -E '^(POPULATION|CONE|WIP_THEORIES|WARMUP|AGREEMENT|CACHE_SCOPE|TOTALS|ROUND|SINK)' $SP/run.log
```

`Isabelle_RPC.Remote_Procedure_Calling` has to be listed as a theory argument: `process_theories`
derives the ad-hoc session's `imports` from the *qualifiers of the theories named on the command
line* (`Pure/Tools/process_theories.scala:85-91`), not from the `imports` line inside the `.thy`, so
without it the import fails with "need to include sessions Isabelle_RPC in ROOT".

### `Probe_Constituents.thy`

```isabelle
theory Probe_Constituents
  imports Complex_Main Isabelle_RPC.Remote_Procedure_Calling
begin

ML \<open>
(* ================= population ================= *)
val thy_nc  = @{theory Complex_Main};
val ctx_nc  = Context.Theory thy_nc;
val rpc_thy = @{theory Remote_Procedure_Calling};

val static  = Facts.dest_static false [] (Global_Theory.facts_of thy_nc);
val n_facts = length static;
val thms    = maps snd static;
val n_thms  = length thms;

structure DT = Hash_Table(struct
  type key = Term_Digest.digest128
  val hash = Term_Digest.digest128_hasher
  val eq = op = : Term_Digest.digest128 * Term_Digest.digest128 -> bool
end);

(* ================= regime constructors ================= *)
fun mk_cache_thy i =
  Theory.begin_theory ("Probe_Cache_" ^ string_of_int i, Position.none)
    [thy_nc, rpc_thy];

(* ================= helpers ================= *)
fun ms t = Real.fromLargeInt (Time.toMicroseconds t) / 1000.0;
fun us_per t = Real.fromLargeInt (Time.toMicroseconds t) / Real.fromInt n_thms;
fun r2 (x : real) = Real.fmt (StringCvt.FIX (SOME 2)) x;

val sink = Unsynchronized.ref 0;
fun consume ((h, _, _) : Theory_Hash.hash * Universal_Key.constituent list
                         * Universal_Key.constituents_report) =
  sink := ! sink + Word8.toInt (Word8Vector.sub (h, 1));

fun timed f =
  let val t = Timing.start ()
      val _ = List.app f thms
      val {elapsed, gc, ...} = Timing.result t
  in (elapsed, gc) end;

fun run_A () = timed (fn th => consume (Universal_Key.thm_constituents ctx_nc th));
fun run_B ctx = timed (fn th => consume (Universal_Key.thm_constituents ctx th));
fun run_C () = timed (fn th =>
      consume (Universal_Key.compute_constituents ctx_nc (Thm.prop_of th)));
fun run_D ctx = timed (fn th =>
      consume (Universal_Key.compute_constituents ctx (Thm.prop_of th)));
\<close>

ML \<open>
(* ================= confound handling: warm-ups & assertions ================= *)

(* (1) the RPC path must really be live *)
val pure_hash = Theory_Hash.hash_of @{theory Pure};
val rpc_live  = Theory_Hash.is_persistent pure_hash;
val _ = if rpc_live then ()
        else error "Theory_Hash RPC path NOT live: Pure hashed on the WIP branch";

(* (2) warm Theory_Hash for EVERY theory in both reading cones, so the one-off
       per-theory Python RPC never lands in a per-thm figure *)
val warm_thy = mk_cache_thy 0;
val cone = Theory.nodes_of warm_thy;
val n_cone = length cone;
val warm_th_timing =
  let val t = Timing.start ()
      val _ = List.app (fn t => (Theory_Hash.hash_of t; ())) cone
      val {elapsed, ...} = Timing.result t
  in elapsed end;
val wip_thys =
  map Context.theory_long_name
    (filter_out (fn t => Theory_Hash.is_persistent (Theory_Hash.hash_of t)) cone);
val all_persistent = null wip_thys;
val cm_cone = Theory.nodes_of thy_nc;
val cm_wip =
  map Context.theory_long_name
    (filter_out (fn t => Theory_Hash.is_persistent (Theory_Hash.hash_of t)) cm_cone);
val _ = writeln ("WIP_THEORIES probe_cone=[" ^ commas wip_thys ^
                 "] complex_main_cone(" ^ string_of_int (length cm_cone) ^ ")=[" ^
                 commas cm_wip ^ "]");

(* (3) distinct thm128 count -- also fully warms Term_Digest's own thm128 cache
       BEFORE any timed round, so it favours neither regime *)
val dt : unit DT.table = DT.empty 65536;
val digest_timing =
  let val t = Timing.start ()
      val _ = List.app (fn th => DT.update dt (Term_Digest.thm128 th, ())) thms
      val {elapsed, ...} = Timing.result t
  in elapsed end;
val n_distinct = DT.size dt;

(* (4) the two regimes must agree *)
val res_nc = map (fn th => Universal_Key.thm_constituents ctx_nc th) thms;
val ctx_w0 = Context.Theory warm_thy;
val res_c  = map (fn th => Universal_Key.thm_constituents ctx_w0 th) thms;
val n_diff = length (filter_out I (map2 (fn a => fn b => a = b) res_nc res_c));

val totals0 = Universal_Key.constituents_totals ();

val _ = writeln (cat_lines [
  "POPULATION facts=" ^ string_of_int n_facts ^
  " thms=" ^ string_of_int n_thms ^
  " distinct_thm128=" ^ string_of_int n_distinct,
  "CONE theories=" ^ string_of_int n_cone ^
  " all_persistent=" ^ Bool.toString all_persistent ^
  " rpc_live=" ^ Bool.toString rpc_live ^
  " pure_hash=" ^ Theory_Hash.to_hex pure_hash,
  "WARMUP theory_hash_ms=" ^ r2 (ms warm_th_timing) ^
  " thm128_ms=" ^ r2 (ms digest_timing),
  "AGREEMENT differing_thms=" ^ string_of_int n_diff,
  "CACHE_SCOPE Complex_Main=" ^
    (case Universal_Key.cache_scope_id thy_nc of NONE => "NONE"
      | SOME i => "SOME " ^ string_of_int i) ^
  " Remote_Procedure_Calling=" ^
    (case Universal_Key.cache_scope_id rpc_thy of NONE => "NONE"
      | SOME i => "SOME " ^ string_of_int i) ^
  " probe0=" ^
    (case Universal_Key.cache_scope_id warm_thy of NONE => "NONE"
      | SOME i => "SOME " ^ string_of_int i),
  "TOTALS skipped=" ^ string_of_int (#skipped totals0) ^
  " empty_name_fallback=" ^ string_of_int (#empty_name_fallback totals0)]);

val _ = if n_diff = 0 then ()
        else error ("The two reading contexts DISAGREE on " ^
                    string_of_int n_diff ^ " thms: measurement meaningless");
\<close>

ML \<open>
(* ================= the rounds ================= *)
val n_rounds = 15;

fun round i =
  let
    val thy_c = mk_cache_thy i
    val ctx_c = Context.Theory thy_c
    val scope = case Universal_Key.cache_scope_id thy_c of
                  NONE => ~1 | SOME id => id
    val _ = if scope >= 0 then ()
            else error "round: cache theory has NO cache scope"
    (* alternate the order so neither regime always runs first *)
    val ((eA, gA), (eB, gB), (eC, gC), (eD, gD)) =
      if i mod 2 = 0
      then let val a = run_A () val b = run_B ctx_c
               val c = run_C () val d = run_D ctx_c
           in (a, b, c, d) end
      else let val d = run_D ctx_c val c = run_C ()
               val b = run_B ctx_c val a = run_A ()
           in (a, b, c, d) end
    (* bonus: the same cached pass again, now fully warm *)
    val (eE, _) = run_B ctx_c
  in
    writeln ("ROUND " ^ string_of_int i ^ " scope=" ^ string_of_int scope ^
      " | A_nocache_ms=" ^ r2 (ms eA) ^ " (" ^ r2 (us_per eA) ^ " us/thm, gc " ^ r2 (ms gA) ^ ")" ^
      " | B_cache_ms=" ^ r2 (ms eB) ^ " (" ^ r2 (us_per eB) ^ " us/thm, gc " ^ r2 (ms gB) ^ ")" ^
      " | C_compute_nc_ms=" ^ r2 (ms eC) ^ " (" ^ r2 (us_per eC) ^ " us/thm, gc " ^ r2 (ms gC) ^ ")" ^
      " | D_compute_c_ms=" ^ r2 (ms eD) ^ " (" ^ r2 (us_per eD) ^ " us/thm, gc " ^ r2 (ms gD) ^ ")" ^
      " | E_cache_rewarm_ms=" ^ r2 (ms eE) ^ " (" ^ r2 (us_per eE) ^ " us/thm)")
  end;

val _ = List.app round (1 upto n_rounds);
val _ = writeln ("SINK " ^ string_of_int (! sink));
val totals1 = Universal_Key.constituents_totals ();
val _ = writeln ("TOTALS_END skipped=" ^ string_of_int (#skipped totals1) ^
                 " empty_name_fallback=" ^ string_of_int (#empty_name_fallback totals1));
\<close>

end
```

Raw logs kept alongside this report: `run3.log` (the 15-round run reported here), `run2.log` (the
earlier 6-round run), `load_before.txt` / `load_during.txt` / `load_after.txt`.
