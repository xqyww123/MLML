---
name: mathbench-import-reconcile
description: Playbook for adding a new import to MathBench_ProverBase and reconciling any syntax conflicts (constant/type short-name resolution and notation) so that PutnamBench problems still parse to identical goal terms. Use when adding/changing imports of the MathBench_Prover session, or when investigating MathBench-vs-PutnamBench environment divergences.
---

# MathBench import reconciliation

Goal: after adding a new theory to MathBench_Prover's environment, guarantee that
no PutnamBench problem changes meaning or breaks. A new import can shadow a
constant/type short name or a piece of notation that a problem relies on.

There are **two checks** and they have different authority:

| check | tool | role |
|---|---|---|
| **goal-term equality** | `tools/test_mathbench_goals.py` | **authoritative gate** — does every PutnamBench goal parse to the identical term with vs without MathBench? (pass = process exits 0) |
| **declared divergence** | `tools/check_putnam_divergence.py` | **coverage radar** — which const/type/notation short names resolve differently? (over-reports; deltas vs a golden ledger) |

The goal-term check is correctness; the divergence check is forward-looking
coverage (it catches names not yet exercised by any problem statement, and
proof-script risks the goal check is blind to).

## Architecture: fast inner loop, slow outer loop

The heavy AFP heap is **MathBench_ProverBase** (prebuilt, fixed). **MathBench_Prover.thy**
loads on top of it from source. So:

- **Inner loop (seconds, no AFP rebuild):** edit `tasks/MathBench_Prover/MathBench_Prover.thy`,
  restart the REPL (reuses the Base heap), re-run the checks.
- **Outer loop (one rebuild):** once the inner loop is green, move the validated
  `import` + reconciliation (`hide_const`/`no_notation`/...) into
  `tasks/MathBench_Prover/Base/MathBench_ProverBase.thy` and rebuild the heap.

Critical fact: the REPL caches loaded theories (`Thy_Info`), so **edits to
MathBench_Prover.thy are only picked up after a REPL restart** — there is no live
reload. Restart is cheap (reuses the Base heap).

### Dedicated REPL (port 7777)

The pipeline runs its own Isa-REPL on **port 7777** (base session
MathBench_ProverBase), isolated from the default 6666 other tasks use. It
starts/restarts it itself — never touches 6666:
```
python tools/mathbench_repl.py start      # start + wait until ready
python tools/mathbench_repl.py restart    # inner-loop step after editing MathBench_Prover.thy
python tools/mathbench_repl.py stop
python tools/mathbench_repl.py status
```
Both checks default to `127.0.0.1:7777`. They load MathBench_Prover via
`add_lib(['MathBench_Prover.MathBench_Prover'])`, which reads it **from source**
(reflecting your edit) on top of the Base heap:
- the goal gate's phase 2 add_libs it (phase 1 doesn't, giving the clean Putnam env);
- the divergence tool add_libs it on a *dedicated* connection only to regenerate
  the MathBench reference, then sweeps PutnamBench on a separate clean connection.

Rebuild the heap (outer loop, only after promoting to MathBench_ProverBase.thy):
```
RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 -o system_heaps MathBench_ProverBase
```

## The procedure

### 1. Add the import to MathBench_Prover.thy (not Base yet)
Add the new theory to the `imports` of `MathBench_Prover.thy`, then
`python tools/mathbench_repl.py restart`.
If MathBench_Prover.thy now fails to load (ambiguous parse, duplicate notation),
read the error and add the obvious `hide_const`/`no_notation` before going on.

### 2. Run the declared divergence check (delta vs golden)
```
python tools/check_putnam_divergence.py            # shows only NEW divergences (delta)
python tools/check_putnam_divergence.py --full     # shows everything
```
This tool runs on the 7777 REPL. It first **regenerates the MathBench reference
itself**, on a dedicated `add_lib` connection (writing
`/tmp/mathbench_{const.tsv,type.tsv,notation.txt}`), then sweeps every PutnamBench
import set on a *separate, clean* connection (its probes import only the
problem's own theories — never MathBench) and compares. So after `restart` you
just run it; there is no manual dump step. (`--no-regen` reuses existing dumps
against a plain-HOL server.)

Only the **delta** matters: divergences already in `tools/divergence_golden.json`
are known/accepted and suppressed. For each NEW divergence, decide (step 4).
If the run prints a `WARNING: ... SKIPPED` line, coverage is incomplete — fix the
cause and rerun; do not trust a green delta with skips.

### 3. Run the authoritative goal-term gate
```
python -m tools.test_mathbench_goals      # defaults to 127.0.0.1:7777; auto-retries socket flakes
```
**Pass = the process exits 0** (it exits non-zero iff `mismatch > 0` or
`new_errors > 0`). `new_errors` = a problem whose status changed between the two
phases (e.g. parsed without the lib, errors with it = MathBench broke it).
Persistent REPL socket errors (Connection reset / Broken pipe) are retried
automatically on fresh connections; if a key is *still* erroring after
`--retries` rounds it is reported (fail-loud) — re-run to confirm it is just a
flake, not a real change.

A real `mismatch` means a problem's goal term changed. The full per-goal sexprs
(WITHOUT vs WITH lib) are written to `mathbench_goal_comparison.json`; diff them
there — the long-name present only in the WITH side is the constant MathBench
introduced, i.e. the one to hide (unless it is what Putnam itself resolves to).

### 4. Decide each NEW divergence: FIX or ACCEPT
Ground truth for "which constant should win" is **PutnamBench's native
resolution** — MathBench must resolve a short name the way the problem's own
imports do.

- **FIX** (add reconciliation to MathBench_Prover.thy) when the divergence is or
  could be harmful — the goal gate shows a real mismatch, or a problem uses the
  name in the conflicting sense, or it is semantically dangerous (e.g. `transpose`
  matrix-vs-permutation, `measure` measure-theory-vs-recursion):
  - constant resolves differently → `hide_const (open) <the const that should lose>`
    (hide the one that does NOT match Putnam, so the Putnam-expected one wins)
  - notation conflict → `no_notation <const> (<mixfix>)`
  - type resolves differently → `hide_type (open) <type that should lose>`
  After editing, `mathbench_repl.py restart`, then re-run steps 2–3 (the
  divergence tool regenerates the reference itself).

- **ACCEPT** into the golden ledger only when **both**:
  1. the goal-term gate is green (the divergence provably changes no current goal), AND
  2. you judge it benign for the future too (code-gen internal name, a name no
     problem will use, a deliberately `no_notation`-removed operator, ...).
  ```
  python tools/check_putnam_divergence.py --accept-new --rationale "<why benign>"
  ```
  This appends the current new divergences to `divergence_golden.json` with your
  rationale and date. Commit the golden change so the acceptance is auditable.
  (`--accept-new` is refused together with `--limit` — only accept after a full
  sweep, never a partial one.)

  Guardrail: never `--accept-new` while the goal gate is red. The golden is for
  noise, not for silencing real breakage. You may always choose to FIX instead of
  accept (agent judgment may be stricter than the gate, never looser).

### 5. Promote and rebuild
When the inner loop is fully green (goal gate exits 0, divergence delta either
empty or all consciously accepted, no SKIPs):
1. Move the `import` and all reconciliation statements from MathBench_Prover.thy
   into `Base/MathBench_ProverBase.thy`.
2. Rebuild the heap (command above).
3. `python tools/mathbench_repl.py restart` (now picks up the rebuilt heap);
   re-run steps 2–3 to confirm the promoted state matches.

## If the REPL fails to start

`mathbench_repl.py start` waits up to 10 min (cold MathBench_ProverBase heap load
is slow) then exits non-zero. On failure: read `/tmp/mathbench_repl.log`; confirm
the `MathBench_ProverBase` heap is built (`isabelle build` it if not); a wedged
server is recovered with `stop` then `start`. The helper only ever touches port
7777 — it never disturbs a 6666 server other tasks use.

## Golden ledger notes

- `tools/divergence_golden.json` — accepted divergences with rationale, plus
  `meta.putnam_version` (the PutnamBench commit it was baselined against).
- Identity of an entry excludes file/import-set counts (they fluctuate). If the
  delta shows entries that are really just count changes, the key is wrong — do
  not paper over it by accepting.
- **PutnamBench data drift:** if `data/PutnamBench` is updated, the divergence set
  shifts for reasons unrelated to MathBench. Refresh the golden deliberately
  (note the new `putnam_version`); do not mistake data drift for import-induced
  divergence.

## Files
- `tools/mathbench_repl.py` — start/restart the dedicated REPL on port 7777
- `tasks/MathBench_Prover/MathBench_Prover.thy` — inner-loop edit target
- `tasks/MathBench_Prover/Base/MathBench_ProverBase.thy` — promotion target
- `tasks/MathBench_Prover/env_dump.ML` / `Env_Dump.thy` — reference dump logic
- `tools/check_putnam_divergence.py` / `divergence_golden.py` — divergence + golden
- `tools/test_mathbench_goals.py` — authoritative goal-term gate
