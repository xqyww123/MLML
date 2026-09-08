> SEALED (2026-09-08): the design below is implemented and committed
> (auto_sledgehammer 7615fe5, Isa-Mini 191e8b3, Isa-REPL d12051f).  It has since
> been modified: a record now carries BOTH the thread CPU time and the wall
> time, and each replay limit derives from its own kind.  The modification is
> in `PROOF_STORE_CPU_AND_WALL_TIME_PLAN.md`; this file is not edited any more.

# Proof-store replay in thread CPU time: handoff (2026-09-07)

Goal (the author's proposal): in the proof store of auto_sledgehammer and of
AoA, measure the time recorded for a proof, and budget the replay of a
recorded proof, in the calling thread's CPU time instead of wall clock.  Scope
is ONLY these two things: the record points and the replay budget.  The
per-operation timers of Isa-Mini (`timed_OPR`), the sledgehammer watchdog, the
Isa-REPL per-command timeout and every Python-side timer stay wall clock.

## What is already done (committed)

`contrib/Performant_Isabelle_ML` commit dba3d6f (superproject bump follows it),
accepted after five adversarial review rounds.  The API of
`library/thread_cpu.ML` is now:

    val self: unit -> clock option          (* NONE without a usable clock *)
    val the_self: unit -> clock             (* or the ERROR saying why *)
    val read: clock -> Time.time option
    val free: clock -> unit
    type timing = {thread_cpu: Time.time option, elapsed: Time.time, cpu: Time.time, gc: Time.time}
    val timing: ('a -> 'b) -> 'a -> timing * 'b        (* Timing.timing plus the thread's CPU *)
    val cpu_timing: ('a -> 'b) -> 'a -> Time.time option * 'b
    val apply: {thread_cpu: Time.time, wall: Time.time option} -> ('a -> 'b) -> 'a -> 'b

`apply`: the wall limit is the outer `Timeout.apply` (liveness), the CPU limit
the inner one; whichever fires first raises `Timeout.TIMEOUT`.  Without a
usable clock (no native library, or the OS refusing one) only the wall limit is
enforced, with a warning on every call; without a clock AND without `wall` it
is an error.  A limit under 1 ms is ignored (`Timeout.ignored`); `timeout_scale`
scales both.  `thread_cpu` in `timing` is NONE without a clock: no wall-clock
stand-in, the caller decides.

Test: `Test/Thread_CPU_Test.thy`, run from source over Pure (never `isabelle build`):

    cd contrib/Performant_Isabelle_ML && isabelle ML_process -l Pure -o threads=4 \
      -e 'Thy_Info.use_thy_legacy "/home/qiyuan/Current/MLML/contrib/Performant_Isabelle_ML/Test/Thread_CPU_Test"'

The same `isabelle ML_process -l Pure -e 'Thy_Info.use_thy_legacy "<abs path>"'`
loads any theory from source over the Pure heap; `isabelle process` no longer
exists in Isabelle2025-2.  For theories above HOL use the Isa-REPL server
(the one sanctioned way to build).

## The call sites (auto_sledgehammer and Isa-Mini, unchanged so far)

Replay point -- ONE channel, every replay goes through it:
- `contrib/auto_sledgehammer/library/sledgehammer_solver.ML` ~620, `eval_prf_str0`:
  `Timeout.apply timeout (Timing.timing (... Seq.pull)) seq`, matching
  `{elapsed = time, ...}`.  Reached by auto_sledgehammer's store hits
  (`replay_store`, ~1934), `fast_mepo`'s per-subgoal cache
  (`replay_mepo_proof` -> `eval_prf_str`), AoA's `store_hit_replay`
  (`contrib/Isa-Mini/Agent/proof_store_AoA.ML` ~128) and the `aoa_replay` method.
  The budget handed in is `Phi_Proof_Store.tolerant_time t = 1.5 * t + 1 s`
  (`contrib/auto_sledgehammer/library/cache_file.ML` ~876) of the recorded
  standard-machine time; `standard_time` divides a measurement by
  `timeout_scale` at every write point.

Record points (all single-threaded on the calling thread):
1. sledgehammer_solver.ML ~620: the `elapsed` of `eval_prf_str0` itself -- the
   time of a sledgehammer-found proof is the verification replay of the composed
   proof (~1789).
2. sledgehammer_solver.ML ~1478: `fast_mepo`'s fastforce time, `Time.now ()` difference.
3. `contrib/Isa-Mini/Agent/agent_server.ML` ~899: `prep_elapsed`, the three
   preprocessing segments (sequential; `preprocess_split_recorded` does not fork).
4. agent_server.ML ~961: each op's `elapsed`, summed on the Python side
   (`IsaMini/AoA/toplevel.py` ~96) over the final op stream during the assembly
   verification replay; `replay_time = prep_elapsed + that sum` (~1864).

Embedded records INSIDE the AoA op stream (not yet decided whether in scope):
- HAMMER's `cached_proof (prf, ms)`: replayed with `1.5 * ms + 3000 ms` wall
  (`contrib/Isa-Mini/Agent/agent.ML` ~1690).  Its `ms` is measured by
  `Timer.checkRealTimer` around the WHOLE sledgehammer search in
  `contrib/Isa-Mini/library/proof.ML` `HAMMER_i` (~4370) -- search wall time,
  not replay cost; the search forks futures and external provers, so the calling
  thread's CPU would be near zero there.
- FactInTime's `(prf, ms)`: `run_mepo_and_render`'s fastforce wall time,
  replayed with the same formula (agent.ML ~1148).

Conventions to respect: the `Timeout` structure below Performant_Isabelle_ML is
the accounted one (`library/accounted_timeout.ML`); `smt` proofs in a replay
wait on an external solver (CPU does not advance), and `smt_timeout` defaults
to 0 = unlimited, so a wall cap is mandatory beside a CPU budget.

## Decisions already taken by the author

- Replay budget: `Thread_CPU.apply {thread_cpu = <CPU budget>, wall = SOME <cap>}`;
  CPU budget from the recorded time via `tolerant_time`; the wall cap is a
  liveness guard.
- Record points switch to thread CPU together with the replay budget.  Old
  records (wall time, >= CPU time) stay valid: they only yield a more generous
  budget; no migration.
- Deployment without the native library is acceptable: the fallback degrades
  to wall clock with a warning.

## Decisions taken by the author on 2026-09-07 (after the handoff was first written)

1. Wall cap for every replay budget: `2 * recorded time + 3 s`.  Same formula at
   the proof-store replay (`eval_prf_str0`) and at the embedded HAMMER and
   FactInTime replays; one function beside `tolerant_time` in cache_file.ML,
   shared by all three sites.  The implementer objected that an `smt` replay
   waits on z3 with almost no CPU (so its recorded CPU time is tiny and the cap
   is ~3 s of wall) and that a loaded machine was measured at 5.7x slowdown;
   the author heard both and chose 2x + 3 s anyway.  Do not re-open.
2. A record point whose `Thread_CPU.timing` yields `thread_cpu = NONE` records
   the wall `elapsed` instead (today's behaviour; old records are wall time).
3. The embedded HAMMER and FactInTime records switch together with the
   proof-store records; HAMMER's recorded `ms` becomes the verification
   replay's CPU time (like the auto_sledgehammer store), no longer the
   search's wall time.
4. `isabelle_time` reported to the Python side stays wall time (the per-op
   `elapsed`); budgets are CPU, the displayed cost is wall.

5. The embedded records keep their own CPU budget constant (3 s, "1.5 * ms +
   3000 ms"); the author declined to unify it with `tolerant_time`'s 1 s.

6. (2026-09-08) The sledgehammer verification replay of a composed proof
   (`sledgehammer_solver.ML` ~1791) keeps its original plain 180 s wall guard
   and gets NO thread-CPU limit: written as
   `{thread_cpu = Time.zeroTime, wall = SOME 180 s}` (a thread_cpu below 1 ms
   is ignored by `Thread_CPU.apply`).  The 180 s is a fixed guard, not a
   recorded time, so the 2t+3 s formula does not apply there.
7. (2026-09-08, closed earlier, do not re-open) `wall` in the limits record
   stays `Time.time option`, the exact argument shape of `Thread_CPU.apply`.

## Implemented (2026-09-08)

`Phi_Proof_Store` (`contrib/auto_sledgehammer/library/cache_file.ML`) now exports
`type replay_limits = {thread_cpu, wall}`, `wall_cap` (2t + 3 s),
`replay_limits_with slack t` (1.5t + slack of CPU, `SOME (wall_cap t)` of wall),
`replay_limits = replay_limits_with 1 s`, and `timing` (a record point's
measurement: the calling thread's CPU, or the wall elapsed without a clock).
`tolerant_time` is gone: it had no other user.  `eval_prf_str`,
`replay_mepo_proof` and the evaluator of `try_cached_proof_by_hash` take
`replay_limits`; `eval_prf_str0` runs under `Thread_CPU.apply`.  `auto` now
returns `(Time.time * string) future * thm` like `all_auto` (the raw time of
the replay that produced the text), so `HAMMER_i` reports that time instead of
a wall timer around the search.  `MiniLang_Agent.embedded_replay_limits ms =
replay_limits_with 3 s` serves the FactInTime replay and HAMMER's
`try_cached_apply`, which wraps `Minilang.APPLY NONE` in `Thread_CPU.apply`.
The four record points use `Phi_Proof_Store.timing`.  `isabelle_time` on the
Python side never read the per-op number (it is Python's own wall measurement),
so decision 4 held without a change.

Verification without `isabelle build`: auto_sledgehammer and Minilang load from
source with `isabelle ML_process -l HOL -d <dirs> -e 'Thy_Info.use_thy_legacy
"<abs path>"'`; theories importing Isabelle_RPC need the Scala side, so they were
loaded from source inside a freshly started Isa-REPL server
(`Isa-REPL/repl_server.sh 127.0.0.1:PORT HOL <out> -l Minilang_AoA -d ...`;
restart it after every `.ML` edit) and driven with the async Python client
(`IsaREPL.Client`, `await c.eval(...)`).  Both proof-store test theories pass
there; probes through `eval_prf_str` show a 100 ms CPU limit firing at 0.1 s,
a 200 ms wall limit firing at 1 s (Poly/ML interrupts `OS.Process.sleep` only
at 1 s granularity) and a 1 s sleep not charged.  Caveat for probes: Poly/ML
evaluates a closed constant expression inside `tactic <...>` at method-command
time, outside any limit -- make a burner depend on the goal state.

Review: round 1 (5 critics, 5 fresh defenders, judge; 33 findings) left one
author decision (J1, above) and seven comment/naming items, all fixed; round 2
verified the fixes and added one comment item, fixed; a final judge pass
followed the J1 ruling.

## Working rules that applied throughout

Never `isabelle build`; one concept one word; every new decision and every
user-visible text is proposed before it is written; comments concise; reuse
Isabelle's combinators.  The author reviews in adversarial Opus 5 workflow
rounds (5 critics, 5 fresh defenders, 1 judge); 'fix-then-rereview' items are
the implementer's to do, 'must-discuss' items go to the author.  A review agent
that simulates load must kill what it starts (one left 20 busy loops behind).
