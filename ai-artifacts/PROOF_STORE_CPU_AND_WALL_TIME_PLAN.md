# Proof-store records carry both thread CPU and wall time (2026-09-08)

Status: rev 4, approved in full by the author and reviewed READY (three
adversarial review rounds, see Review history).  Implemented on 2026-09-08,
uncommitted; see Implementation record.

This plan supersedes ONE part of the sealed `PROOF_STORE_CPU_TIME_PLAN.md`:
there a record holds a single time and both replay limits derive from it.
Everything else in that document stands: which record points and which
replays are in scope, the sledgehammer verification replay's fixed 180 s wall
guard, `wall` in `replay_limits` staying `Time.time option`, and the wall cap
formula 2 * wall + 3 s.

## Why

Today a record in the proof store holds one time.  Since the seal of
2026-09-08 that time is the calling thread's CPU time (the wall elapsed on a
machine without a per-thread CPU clock); before the seal it was wall time.
Both replay limits derive from that single number t: the CPU limit is
1.5t + slack, the wall cap 2t + 3 s.

An `smt` proof breaks this.  It waits on z3, an external process, while the
Isabelle thread's CPU stands still: z3 takes 8 s of wall, the thread spends
~50 ms of CPU encoding the problem and reconstructing the proof.  The record
says t = 50 ms, so the wall cap on replay is ~3.1 s; z3 still needs 8 s; the
replay times out; the entry is invalidated and re-searched; the same proof is
found and recorded with the same 50 ms; the next replay fails the same way.
Any `smt` proof needing more than ~3 s of wall is uncacheable today.

Recording both times ends the mismatch.  The CPU limit derives from the
recorded CPU time and the wall cap from the recorded wall time, so each limit
watches one kind of failure: the CPU limit catches a replay that computes
more than the recorded one did (a changed context, a looping simp), which
machine load cannot inflate; the wall cap catches a stalled external solver
or a hung process.  For the `smt` record above the pair is cpu = 50 ms,
wall = 8 s, giving a CPU limit of ~1.1 s (the reconstruction costs what it
cost before) and a wall cap of 19 s (z3 is near-deterministic, so the replay
takes about what the search took).

## Design

### 1. The record type and its operations

All in `Phi_Proof_Store` (`contrib/auto_sledgehammer/library/cache_file.ML`).

The type: `type times = {thread_cpu: Time.time, wall: Time.time}`, the two
times of a record.  The field names are those of `Thread_CPU.timing` and of
`replay_limits`.

The operations that need no `Timeout.scale`:
`zero_times`, `add_times`,
`map_times : (Time.time -> Time.time) -> times -> times`,
`times_of_ms : int * int -> times`, `ms_of_times : times -> int * int`, and
`string_of_times : times -> string`.  They and the type are declared at the
head of the `Phi_Proof_Store` body, before `type proof_record` (today line
245, whose `time` field becomes a `times`).  The placement matters because
the file is elaborated in order: the frame conversions `replay` (283) and
`put_frame` (290) need `times_of_ms` and `ms_of_times`.

The two scalings stay where `standard_time` is today (867) and are built
from one guarded factor, so they are inverses by construction:
`fun timeout_factor () = Real.max (Timeout.scale (), 0.001)` (keeping the
existing comment that explains the clamp: `timeout_scale` is a user-settable
real, and 0 or a negative value would blow up or negate every stored time),
`standard_time = map_times (fn t => Time.scale (1.0 / timeout_factor ()) t)`,
and `machine_time = map_times (fn t => Time.scale (timeout_factor ()) t)`
(name proposed).  A comment on `machine_time` says why stock Isabelle's
`Timeout.scale_time`, the unguarded spelling a later reader would simplify
it into, is deliberately not used.

`string_of_times` spells the pair as `thread_cpu=... wall=...`, the way
`eval_prf_str`'s breakdown line (sledgehammer_solver.ML 645) already spells
its limits, so both kinds of trace read alike in a log.  That breakdown line
itself renders a `replay_limits` (an optional wall plus an `elapsed=` term),
a different type, and is left alone.

`timing : ('a -> 'b) -> 'a -> times * 'b` is a record point's measurement;
without a per-thread CPU clock `thread_cpu` is the wall elapsed, today's
rule.  `wall_cap` leaves the signature: its only caller is
`replay_limits_with`, so it becomes a local there.

Two rules.  First, no production caller outside cache_file.ML names a field
of `times`; test theories and throwaway probes assert on the two numbers and
name them deliberately.  Second, no site anywhere builds or destructures the
millisecond pair by hand: every wire goes through `times_of_ms` and
`ms_of_times`, the frame layer through `replay` and `put_frame`.  (The test
theories' `t1`/`t2`/`t3` become `times_of_ms (100, 100)` and the like.  A
per-instantiation msgpack abbreviation for the pair is a free local choice,
not mandated: mlmsgpack is functorised per stream type, so one shared
combinator is not one definition.)

Where the code holds a `times` in place of today's `Time.time`: a zero
(`Time.zeroTime` stands in for the record at sledgehammer_solver.ML 1215,
1218, 1788, 1988, 2028 and agent_server.ML 1942), a sum
(sledgehammer_solver.ML 2056, agent_server.ML 1865), a division by
`timeout_scale` at every write point, and one multiplication back
(agent_server.ML 1901, today a hand-written unguarded inverse of
`standard_time`).

No clamp `wall = max (wall, thread_cpu)`: thread_cpu.ML says the inequality
holds only up to one coarse clock tick, so a clamp would rewrite legitimate
measurements and would hide a transposition instead of preventing one.

### 2. The replay limits

`replay_limits_with slack ({thread_cpu, wall} : times)` =
`{thread_cpu = 1.5 * thread_cpu + slack, wall = SOME (2 * wall + 3 s)}`.
The store's slack stays 1 s (`replay_limits`), the embedded records' 3 s.
The sledgehammer verification replay keeps its fixed 180 s wall guard with
no CPU limit.

### 3. The L2 file format

`Proof_Store_Format` (the frame codec at the top of cache_file.ML) closes
before `Phi_Proof_Store` opens, so it stays in milliseconds and never names
`times`.  Its datatype becomes
`PUT of {id: string, hash: Hasher.digest option, cpu_ms: int, wall_ms: int, proof: string}`,
and `encode_put`'s argument record likewise.  The new tag 4 packs
`packTuple4 (packString, packOption packWord64, packPair (packInt, packInt), packString)`,
that is `(id, hash, (cpu_ms, wall_ms), proof)` with the pair nested in one
slot, mirroring `times` as every wire does (item 4).  The tag-1 and tag-3
arms fill both fields from their single int and decode forever.  `replay`
and `put_frame` remain the only conversions between milliseconds and
`times`, today's division of labour.

Decoding migrates a legacy frame, and the first theory-end compaction writes
that migration back to disk, because `put_frame` always emits the current
tag.  So every `.proof-store` becomes tag 4 on the next build, and the 40
such files tracked by contrib/phi-system churn wholesale.  The upgrade is
one-way, as the tag 1 to tag 3 bump was: a store compacted by an older
checkout silently loses its tag-4 records, so auto_sledgehammer and every
repository pinning it move together.  Author's ruling: accepted again, no
guard; old checkouts are never used.

A tag-3 frame written after the seal (2026-09-08 10:06) holds CPU time.
Lifted into both fields it yields exactly today's limits, so it is no worse
off than now: an `smt`-like one fails one replay, is tombstoned and
re-searched, and the new record carries a real wall time.

Test_Proof_Store_Double_Key.thy builds `F.PUT {...}` literals (54-67, 146)
and asserts the tag of `encode_record` (test 1); they follow this datatype
and tag 4.

### 4. The AoA op stream and blob

In ML, the `xcmd` datatype carries the recorded proof as
`(string * Phi_Proof_Store.times) option` at both constructors
(agent.ML 21/225 for `FactInTime`, 60/264 for `HAMMER`).  The integer pair
exists only inside the codec.  One codec pair in `agent_packer.ML`,
`pack_recorded_proof` (beginning with `ms_of_times`) and
`unpack_recorded_proof` (ending in `times_of_ms`), defined beside
`pack_extended_fact` and used at both carriers, replaces the five
spelled-out `packPair (packString, packInt)`.  The wire is
`(method, (cpu_ms, wall_ms))`, the pair nested.  Author's ruling: the nested
shape at every wire, so no arity changes anywhere and the field order lives
in `times_of_ms`/`ms_of_times` alone.

Legacy blobs: the unpacker's `||` alternative (the combinator
`unpack_extended_fact` already uses) sits inside the recorded proof's
`unpackOption` and chooses a 2-array second element against a bare integer,
the legacy `(method, ms)` lifted to `cpu = wall = ms`.  The outer `||` of
`unpack_extended_fact`, which chooses a 3-array against the pre-3a 2-array,
stays as it is, so that function carries both alternations nested.  The
inner placement is forced: msgpack tuple unpackers check the array length
first, so an alternation at the outer tuple cannot rescue an inner mismatch.
Old blobs inside `aoa_replay "<b64>"` (27 of the 40 tracked files) therefore
still decode; a new blob is undecodable to an older Minilang, one-way as in
item 3.

`embedded_replay_limits` (agent.ML 1103) loses its body and becomes the
partial application `Phi_Proof_Store.replay_limits_with (Time.fromSeconds 3)`,
keeping its name and its comment on the 3 s decision.

Standardisation (author's ruling): the two report points, `HAMMER_i`'s
`SH_PRF (prf, time)` (proof.ML ~4380) and `FACT_PRF (name, prf, time)`
(agent.ML ~1141), report `standard_time` of the measurement, so every time
inside a blob is standard-machine time like the outer record, and the
embedded limits differ from the store's only in their slack.  This applies
to these two points only.  `proof_opr`'s per-op time (agent_server.ML 967)
stays raw: it is summed in Python, folded into `replay_time`, and
standardised once at agent_server.ML 1932.  The re-report inside
`try_cached_apply` (agent.ML ~1707) copies a stored record and stays as it
is.  One `standard_time` at a report point cannot double-divide, because
`auto` returns a raw measurement on both of its routes (the search route
standardises only into `record`, sledgehammer_solver.ML 2013; `replay_store`
returns this replay's own measurement).  No data migration is needed:
`timeout_scale` is 1.0 on the machines that produced today's blobs, where
raw and standard time coincide.

Python (`IsaMini/AoA/model.py`).  The pair arrives already correct from ML
and Python only relays it; with the nested shape every existing pattern
still binds in arity (`case (15, (method, time_ms))` 1574,
`case (20, ...)` 1582), and nothing at runtime will ever point at the
carriers.  The edits are therefore names, annotations and docstrings with no
runtime check behind them, which makes the rename load-bearing:

- The field `time_ms` of `SH_PRF_Msg` (1513) and `FACT_PRF_Msg` (1523) is
  renamed to the pair's name (proposed `times_ms`).  Its two surviving reads
  are 8205, absorbed by the `_found_proof` restructure below, and
  `f.cached_proof = (m.method, m.time_ms)` (8049, on the live backfill path
  of every SUCCESS), which becomes `m.times_ms`.  After the rename a
  surviving `m.time_ms` raises.
- The annotations `tuple[str, int]` at 375, 393, 402, 1791 and 8224 become
  `tuple[str, tuple[int, int]]`; the docstrings at 384-390, 1509-1512 and
  1518-1522 say "thread CPU ms and wall ms".
- The carrier on the fact is `IsabelleFact_ProveInTime.cached_proof`
  (381-403).
- In the `Obvious` node class (8092, which assembles the HAMMER op), the
  `_found_tactic` + `_eval_time_ms` pair (8101, 8205, 8226) becomes one
  `_found_proof: SH_PRF_Msg | None` kept whole from the message, the idiom
  of `_backfill_recorded_fact_proofs` (8045-8049), and `cached_proof` is
  built from it in `assemble`.  An attribute named `_eval_time_ms` holding
  two times would be a lie.

### 5. The per-op time reported to Python

`IsaMini.proof_opr`'s `ret_schema` keeps its triple with
`packPair (packInt, packInt)` in the third slot; model.py 2021, the live
path of every operation, binds that slot unchanged in arity.

`toplevel.py`: a zero pair and one element-wise addition (Python `+` on
tuples concatenates), both module-level definitions near the top of the
file, serve the accumulator (91), the sum (98) and the give-up return.  Not
beside `zero_cost` (192): that is a local of `IsaMini_AoA`, invisible to
`_replay_assembled_proof` (75) where the accumulator lives.  The give-up
return today reads `cost + (0,)` (366), a literal scalar that becomes the
zero pair; the success return `cost + (replayed_ms,)` (361) keeps its form
with the pair in `replayed_ms`.  The `%d ms` of the log line (351), the
return annotation of `_replay_assembled_proof` (76,
`-> tuple[bool, str | None, str | None, int]`) and its docstring (85-88,
"the sum of the per-op ML execution times") follow.

The AoA stats tuple stays ten elements with
`unpackPair (unpackInt, unpackInt)` in the tenth (agent_server.ML 1774);
`replay_time = add_times prep_time (times_of_ms assembled)` (1865); the
level-0 scale-back (1901) is `machine_time`.  `isabelle_time` stays Python's
own wall measurement.

### 6. The L1 store

`contrib/Isa-Mini/IsaMini/proof_store.py`.  Author's ruling: a new table,
`proof_cache_v2 (goal_hash TEXT PRIMARY KEY, proof_text TEXT NOT NULL, std_cpu_ms INTEGER NOT NULL, std_wall_ms INTEGER NOT NULL, timestamp REAL NOT NULL)`.
The legacy `proof_cache` is never created by this code and, when it has the
legacy shape, never modified; it exists only on databases that predate this
change.

The open sequence, using the file's own `PRAGMA table_info` idiom (36-42)
for every column-set check:

1. A `proof_cache_v2` whose column set is neither empty nor the five above
   is dropped (today's rule, retargeted at the new table).
2. `CREATE TABLE IF NOT EXISTS proof_cache_v2 (...)`.
3. A `proof_cache` whose column set is neither empty nor the legacy four
   `{goal_hash, proof_text, std_time_ms, timestamp}` (the agent-era
   `proof_json` table) is dropped, as the committed code drops it today
   (author: X1 approved).
4. When `proof_cache_v2` is empty and a legacy-shaped `proof_cache` exists:
   `INSERT OR IGNORE INTO proof_cache_v2 SELECT goal_hash, proof_text, std_time_ms, std_time_ms, timestamp FROM proof_cache`.

Gating the copy on emptiness rather than on "newly created" makes it
idempotent: Python's sqlite3 does not wrap DDL in a transaction, so a
process interrupted after the CREATE leaves an empty table, and the next
open repairs it.

All three statements of the module, the SELECT of `lookup`, the INSERT OR
REPLACE of `store` and the DELETE of `invalidate` (73; its arity does not
change, so nothing else points at it), address `proof_cache_v2`.  RPC:
lookup returns `((cpu_ms, wall_ms), text)`, store takes
`(key, (cpu_ms, wall_ms), text)`.

Accepted price (author's ruling): the copy re-runs whenever `proof_cache_v2`
is empty at open, which happens on the first migration, after an
interruption following the CREATE, after a drop and re-creation, and equally
when `invalidate` has deleted every row.  Rows `l1_invalidate` removed can
then come back while the legacy table still holds them; such a row fails
its replay once more and is invalidated again, with the visible
"L1 proof cache ... is outdated!" warning.

The author's machine holds 2474 rows; the 20 written after the seal hold CPU
time and are copied as they are (author: no manual deletion).  What one of
them costs if it is `smt`-like: its replay fails once, `l1_invalidate`
deletes it with the warning above, and the goal falls through to `raw_AoA`,
one agent run (or a `gate_error` on a build with the AoA gate shut).  On a
build that writes the store the row is overwritten by the write-back anyway.

### 7. Every carrier of the single time becomes `times`

Forced by the compiler; this list is the implementer's checklist:

- `type proof_cache = Time.time * string` (cache_file.ML 149), the type of
  `get_cached_proof`, `get_cached_proof_by_hash`, `update_cached_proof` and
  the `by_hash` table.  contrib/phi-system's approved, unwritten
  `Docs/GUARD_CACHE_QUICK_MODE_PLAN.md` (rev 14 of 2026-09-08; the
  `.rev<N>.md` files beside it are archived snapshots) is typed on it and
  gains the second number: `type lemma`'s `proof_cache` half at its 143/147,
  the entry format packing that half as one `packInt (Time.toMilliseconds t)`
  at 759-761, and the write point's `Time.zeroTime` at 746-748.  How that
  plan re-encodes its entry is its own business.
- The specs of `try_cached_proof_by_hash` and `try_cached_proof_by_hash_at`
  (cache_file.ML 218-234), which spell `(Time.time * proof)` out instead of
  writing `proof_cache`.
- `Phi_Sledgehammer_Solver.eval_prf_str` (sledgehammer_solver.ML 169,
  `(Time.time * string) * context_state`), the value Verification 4 reads.
- `auto` and `all_auto` (`(times * string) future`), `run_mepo_and_render`
  (exported, `thm * string * times`), `SH_PRF`, `FACT_PRF`,
  `update_cached_proof`, `proof_store_AoA.ML`'s `std_time`, `replay_time`,
  and the two proof-store test theories.

Not forced, settled here: `written` / `proof_mark` keep one ms and it is the
wall, the number a reader can hold against a stopwatch (collision detection
compares the SHA1 only, so nothing is lost), and `collision_message` is
unchanged.  The two `Find proof (...)` traces (sledgehammer_solver.ML 2014,
2059) call `string_of_times`.

Contract comments that change with the code:

- cache_file.ML 13-21, the format header's tag table: tag 4 with the ms pair
  nested in one slot; tag 3 joins tag 1 as decoded-forever-never-written,
  both lifting their single ms into both fields.
- cache_file.ML 192-199: the limits now come from the two recorded times;
  the `wall_cap` sentence goes with the export item 1 removes.
- cache_file.ML 211-215, the `timing` comment: "a CPU record tightens the
  wall cap, the accepted trade" is exactly what this plan abolishes.
- cache_file.ML 629-630: `written`'s "standard-machine ms" says which one,
  the wall.
- sledgehammer_solver.ML's signature comment on `auto`'s time (still a raw
  measurement, now a pair).
- proof.ML 4369-4371, "the raw (undivided) time": false after item 4.
- proof_store_AoA.ML 10-11, 20-22, 25, 46-47 and proof_store.py 1-13, 22:
  "the same value shape (standard-machine time, proof text)".
- agent.ML 1103-1107, the `embedded_replay_limits` note.
- agent_server.ML 947-949, "Third component: this op's ML-side time in ms".
- toplevel.py 188-191, "a tenth element -- assembled_isabelle_time in ms".
- The model.py docstrings of item 4.

## Verification

1. The two proof-store test theories,
   `auto_sledgehammer/Test/Test_Proof_Store_Double_Key.thy` and
   `Isa-Mini/Test/Test_Proof_Store_Hash_Hit.thy`, in a fresh Isa-REPL server,
   extended with: a `tag3_payload` builder beside `tag1_payload`, hand-packed
   with the generic `MessagePackBytesIO.Pack` combinators, asserting the
   decoded record holds the single ms in both fields; test 1's tag assertion
   repointed at tag 4; the `F.PUT` literals rewritten to item 3's datatype.
2. A blob codec test, the tree's first packer test: hand-pack a legacy
   `(method, ms)` inside an `extended_fact` and inside a HAMMER op with
   `MessagePackBytesIO.Pack`, and assert `MiniLang_Agent.xcmd_unpacker_bytes`
   (the BytesIO twin; BinIO's instream cannot be fed from a string) yields
   the lifted record.  This is what catches a mis-nested `||`.
3. L1, pure Python, on temp databases: `ProofStore(<tmp>)` store then lookup,
   both times distinct.  A pre-created legacy four-column table with one
   row: the row is copied into `proof_cache_v2` with
   `std_wall_ms = std_cpu_ms` and `proof_cache` is untouched; a second open
   changes nothing.  A pre-created `proof_cache (goal_hash TEXT PRIMARY KEY, proof_json TEXT)`,
   the agent-era shape: dropped on open, `ProofStore` constructs without
   raising, and a store/lookup round trip on `proof_cache_v2` works (a
   mis-implementation raises `OperationalError` out of `__init__`, which
   both ML ends swallow into a permanent silent miss).  A pre-created legacy
   table with one row beside an explicitly empty five-column
   `proof_cache_v2`: the row lands, the case that tells the emptiness gate
   from a "newly created" gate.  Then once, against a COPY of the live
   49 MB database, as a throwaway check reported in the implementation
   record.
4. The wall-cap probe, in two arms.  The driver in both: sledgehammer never
   returns a sleeping method, so `auto`'s record point is unreachable; the
   record comes from `Phi_Sledgehammer_Solver.eval_prf_str`'s own return, is
   stored with `update_cached_proof` and replayed through `store_hit_replay`,
   the sequence Test_Proof_Store_Hash_Hit.thy 105-119 performs with its
   `count_fail` method.  The method is a `method_setup` whose tactic closes
   over the goal state and sleeps ~5 s, so Poly/ML cannot evaluate it at
   method-command time.  Both arms open with
   `is_some (Thread_CPU.self ())` else `error "probe void: no thread CPU clock"`
   (without a clock the un-edited `timing` records the 5 s elapsed, the cap
   is 13 s, and the Before arm would not time out either) and with
   `Timeout.scale () = 1.0`; both guards compile on either server.  The
   recording call runs under limits that cannot fire, e.g.
   `{thread_cpu = Time.fromSeconds 60, wall = SOME (Time.fromSeconds 60)}`,
   not the cited block's `S.replay_limits t1`, whose 3.2 s wall cap would
   kill the sleeping method while it is being recorded: only the replay is
   under test.  Before arm, a throwaway theory on the un-edited server (the
   value assertions do not compile there): the replay times out at the ~3 s
   cap.  After arm, a throwaway theory on the edited server: at the record
   point `#wall` is in [5, 6] s and `#thread_cpu` under 200 ms, and the
   replay succeeds under the 13 s cap.  Neither arm joins the committed test
   theories, which are clock-independent.
5. Two throwaway checks across the RPC boundary (author: X2 approved; no
   production code and no committed test changes for them), because the
   three widened msgpack wires (`proof_opr`'s return, the AoA stats tuple,
   the two L1 RPCs) fail only at runtime and land in code that swallows by
   documented design.  First, from the REPL against a live RPC host:
   `l1_write` a record under a key whose prefix no production writer mints
   (the idiom of Test_Proof_Store_Hash_Hit.thy 8-12, e.g. `TPSCW.wire-check`)
   with two unmistakable ms (11 and 2222); assert `l1_lookup` returns them
   distinct and in order; `l1_invalidate`; assert the second `l1_lookup` is
   NONE.  This writes into the user's real L1 database, since
   `get_proof_store` is a path-less singleton and no L1 `arg_schema` carries
   a path; a `db_path` parameter is not added to the RPCs for one throwaway
   check.  The prefix keeps the row unreachable by any production lookup,
   and if the final lookup is not NONE the row survived and is deleted by
   hand.  Second, one `by aoa` on a trivial goal plus one run driven to an
   agent give-up with the scripted test driver, asserted to come back as a
   give-up and not as an RPC decode error.

## Working rules

As in `PROOF_STORE_CPU_TIME_PLAN.md`: never `isabelle build`; restart the
REPL after every `.ML` edit; one concept, one word; adversarial Opus 5 review
rounds before the report; comments concise; reuse existing idioms.  New:
restart the Isabelle_RPC host after editing `IsaMini/*.py`.  Python modules
import once and `_store` is a process singleton, and both L1 ends swallow
failures by documented design, so a stale host leaves L1 silently dead under
green tests.

## Implementation record (2026-09-08)

Design items 1-7 are implemented as written, in the files the handoff lists;
the only names chosen here are `timeout_factor`, `machine_time` (proposed in
item 1), `times_ms` (proposed in item 4), `_found_proof` (item 4), and
toplevel.py's `_ZERO_TIMES_MS` / `_add_times_ms` (item 5).  `zero_times` is
written with `Time.zeroTime`; `replay_limits_with` binds `wall_cap` as a
local.  The blob codec's inner alternation sits on the recorded proof's
SECOND element (`unpackPair (unpackInt, unpackInt) || unpackInt`), one level
inside where item 4 places it, which is the same decision made at the
smallest possible scope.  Verification 2's test theory is
`Isa-Mini/Test/Test_Agent_Packer_Recorded_Proof.thy` (three cases: both
legacy slots lifted, the pre-3a fact pair, a round trip with all four
numbers distinct).

Verification 1-5 all passed on a fresh Isa-REPL server compiled from the
edited sources (port 6793, `-l Minilang_AoA`):

1. Both proof-store test theories load with zero errors; test 2b decodes a
   hand-packed tag-3 frame into both fields.
2. The packer test theory loads with zero errors.
3. The pure-Python cases pass on temp databases; the migration on a backup
   copy of the live database (2474 legacy rows, 20 post-seal) fills
   `proof_cache_v2` with all 2474 rows, cpu = wall on every one, legacy table
   untouched, 0.21 s, and a reopen changes nothing.  Note: the LIVE database
   was migrated during this session, not by this test, but by the ephemeral
   RPC host of an un-edited Isa-REPL server belonging to another agent's
   work (pid 949093, port 32799): the Before arm of Verification 4 ran there,
   its level-3 lookup spawned that host, and the host imported the new
   `proof_store.py` from disk.  Consequence: that server's ML side still
   speaks the single-int L1 wire, so its L1 lookups decode-fail into silent
   misses and its L1 stores fail silently until it is restarted; its L2 is
   unaffected.
4. Before arm (the un-edited server above): the 5 s sleeping method records
   0 ms, its replay FAILS after 3.05 s and is tombstoned.  After arm: the
   record is thread_cpu 0 ms / wall 5.005 s, the limits are cpu 1 s /
   wall 13 s, a hand-set 3.1 s wall cap still fires after 4.0 s (sleep is
   interruptible at 1 s granularity), and `store_hit_replay` succeeds in
   5.0 s with no tombstone.  A trap the plan did not foresee: `Method.evaluate`
   runs every `Source` method once against `Goal.protect 0 Drule.dummy_thm`
   as a closure check, before `eval_prf_str0`'s `Thread_CPU.apply` and its
   `timing`; a probe method that does its work regardless of the goal state
   therefore works twice, once outside the limits.  The probe method fails at
   once on a state without subgoals; a real proof method does the same.
5. L1 wire: `l1_write` with (11, 2222) ms, `l1_lookup` returns them distinct
   and in order, `l1_invalidate`, second lookup NONE, no row left in the live
   database.  A scripted `by aoa` (driver `test.ObviousTimeout_subproof`,
   `AoA_read_proof_store=false`) succeeds and writes a tag-4 L2 frame with
   cpu 121 ms / wall 1415 ms whose blob carries HAMMER cached proofs with
   time pairs (10/34 ms and 0/0 ms), and an L1 row with the same pair; a
   scripted give-up (driver `test.NamedFactResolution`) comes back as the
   agent's "exhausted its budget" message, not as an RPC decode error.

Review of the diff (4 critics, 8 fresh defenders, judge; Opus 5): READY to
commit; of eleven findings nine dismissed, three comment-only fixes ordered
and applied (the ML end of the AoA stats wire now names the pair; the
`machine_time` sentence in the signature comment states the caller's real
purpose; `store_hit_replay`'s contract paragraph re-wrapped), each accepted
by a re-review; the three test theories pass again on a server recompiled
after the fixes.  Not in this record: the commit.

## Review history

Rev 1 review (2026-09-08; 5 critics, 10 fresh defenders, judge): not ready.
Author rulings: M1 new L1 table; M2 no manual deletion, correct the premise;
M3 one-way upgrade accepted again, no guard; M4 the mark keeps the wall; M5
standardise the report points; R1 nested pair at every wire.  F1-F9 folded
in.

Rev 2 review (4 critics, 8 fresh defenders, judge): not ready.  Author
rulings: the legacy `proof_cache` is never created; a re-created
`proof_cache_v2` may resurrect invalidated rows; old checkouts are never
used.  R1-R10 and W1-W9 folded in.

Rev 3 review (4 critics, 8 fresh defenders, judge): READY, with eleven
wording fixes (F1-F11) and no author item.  The author then approved X1 (a
foreign-shaped legacy table is dropped as today) and X2 (the two cross-RPC
throwaway checks).  Rev 4 is rev 3 with F1-F11, X1 and X2 folded in and the
text reread for consistency.

Dismissed across all rounds (do not re-raise): `thread_cpu` as an option;
a msgpack map payload; a side-car frame or a passthrough of undecodable
frames; an RPC version handshake or new message kinds; a wall clamp;
option-typing or deleting the post-seal rows (their limits are bit-identical
to today's); re-measuring in `try_cached_apply`; "non-issue lists" filed as
findings; a shared msgpack combinator across the ML/Python boundary;
re-recording closed rulings' rationale; an abstract (opaque) `times`; a
`PRAGMA user_version` migration marker; naming a specific `by aoa` test case
in the plan; renaming `replayed_ms`/`assembled_isabelle_time_ms`; "what
joins the signature".

## Implementation handoff (start here after a context compaction)

The plan is approved in full and reviewed READY; the author said to start
after the compaction.  Nothing of it is written yet; the two plan files are
not yet committed.

Order of work: cache_file.ML (item 1, then item 3, then `proof_cache`,
`update_cached_proof` and the `written` mark of item 7) ->
sledgehammer_solver.ML (item 7's carriers, the traces) -> agent_packer.ML
(item 4's codec) -> agent.ML (the `FactInTime`/`HAMMER` payloads,
`embedded_replay_limits`, the `FACT_PRF` report point) -> proof.ML (`SH_PRF`,
`HAMMER_i`) -> agent_server.ML (items 5 and 7, the `SH_PRF`/`FACT_PRF`
packers at 390-399) -> proof_store_AoA.ML (item 6's RPC side) ->
proof_store.py (item 6) -> model.py and toplevel.py (items 4 and 5) -> the
two test theories and Verification 1-5.

Compiling the ML: start a fresh Isa-REPL server,
`contrib/Isa-REPL/repl_server.sh 127.0.0.1:PORT HOL <outdir> -l Minilang_AoA -o threads=8 -d ...`,
launched with `setsid nohup ... & disown` (never under the Bash tool's
timeout), restarted after every `.ML` edit; theories of the `-l` session
load from source inside it.  The Python client is async:
`async with Client(addr, 'HOL') as c: await c.eval(src)`; errors arrive as
`REPLFail`; output is disabled server-side, so signal results through
`error`.  Restart the Isabelle_RPC host after editing `IsaMini/*.py`.

Afterwards: an adversarial Opus 5 review round of the diff (critics -> fresh
defenders -> judge), then the report to the author in Chinese.  Commit only
on the author's word, on `main`, own files only; describe other agents'
uncommitted hunks in the message if they are swept in.
