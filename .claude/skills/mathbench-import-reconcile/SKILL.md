---
name: mathbench-import-reconcile
description: Playbook for adding a new import to MathBench_ProverBase and reconciling any syntax conflicts (constant/type short-name resolution and notation) so that PutnamBench problems still parse to identical goal terms. Use when adding/changing imports of the MathBench_Prover session, or when investigating MathBench-vs-PutnamBench environment divergences.
---

# MathBench import reconciliation

Goal: after adding a new theory to MathBench_Prover's environment, guarantee that
no PutnamBench problem changes meaning or breaks. A new import can shadow a
constant/type short name or a piece of notation that a problem relies on.

**Prerequisites** (else the very first step hangs):
- The `MathBench_ProverBase` heap must already be built — otherwise the REPL
  start in step 1 times out. Build it with the outer-loop command below.
- Run every command from the project root (`/home/qiyuan/Current/MLML`):
  `python -m tools.…` and the relative `python tools/…` paths both assume it.

There are **two checks** and they have different authority:

| check | tool | role |
|---|---|---|
| **goal-term equality** | `tools/test_mathbench_goals.py` | **authoritative gate** — does every PutnamBench goal parse to the identical term with vs without MathBench? Pass = process exits 0. |
| **declared divergence** | `tools/check_putnam_divergence.py` | **coverage radar** — which const/type/notation short names resolve differently? Over-reports; judged by reading its stdout, not its exit code (see step 2). |

The goal gate is correctness. The divergence radar is forward-looking coverage:
it catches names not yet exercised by any problem statement, and proof-script
risks the goal gate is blind to. Both read the **same** problem set,
`data/putnamBench.json`, so their coverage matches.

## Architecture: fast inner loop, slow outer loop

The heavy AFP heap is **MathBench_ProverBase** (prebuilt, fixed); its `.thy` is
just an `imports` list with an empty body. **MathBench_Prover.thy** imports that
base (plus `Auto_Sledgehammer`) and loads on top of it from source; its body
holds the reconciliation (`no_notation` / `hide_const`). So:

- **Inner loop (seconds, no AFP rebuild):** edit `MathBench_Prover.thy`, restart
  the REPL (reuses the Base heap), re-run the checks. The REPL caches loaded
  theories, so edits are only picked up after a **restart** — there is no live
  reload, but restart is cheap.
- **Outer loop (one rebuild):** once the inner loop is green, move the validated
  `import` + reconciliation down into `Base/MathBench_ProverBase.thy` and rebuild
  the heap.

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
Both checks default to `127.0.0.1:7777` and already handle their own `add_lib`
isolation correctly — after a `restart` you just run them; no manual dump step.

Rebuild the heap (outer loop, only after promoting to MathBench_ProverBase.thy):
```
RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 -o system_heaps MathBench_ProverBase
```

## The procedure

### 1. Add the import to MathBench_Prover.thy (not Base yet)
Add the new theory to the `imports` of `MathBench_Prover.thy`, then
`python tools/mathbench_repl.py restart`.
No `ROOT` change is needed here even for a brand-new AFP session: `add_lib` loads
from source via `Thy_Info`, and every AFP session is globally registered (via
`contrib/afp-*/thys/ROOTS`), so `SessionName.Theory` resolves and is compiled on
top of the heap on the fly.
If MathBench_Prover.thy now fails to load (ambiguous parse, duplicate notation),
read the error and add the obvious `hide_const`/`no_notation` (after its `begin`)
before going on.

### 2. Run the declared divergence check (delta vs golden)
```
python tools/check_putnam_divergence.py            # shows only NEW divergences (delta)
python tools/check_putnam_divergence.py --full     # shows everything
```
This regenerates the MathBench reference itself, then sweeps every unique import
set in `data/putnamBench.json` and compares.

**Judge it by reading stdout, not the exit code.** Look at the final
`Summary: N new | … | …` line — only the **N new** (delta vs
`tools/divergence_golden.json`) needs review; golden-suppressed ones are known.
A `WARNING: … SKIPPED` line means coverage is incomplete — fix the cause and
rerun; do not trust a green delta with skips. The full report is also written to
`/tmp/putnam_divergence_report.md`. For each NEW divergence, decide in step 4.
(`--no-regen` reuses existing dumps against a plain-HOL server.)

### 3. Run the authoritative goal-term gate
```
python -m tools.test_mathbench_goals      # defaults to 127.0.0.1:7777; auto-retries socket flakes
```
**Pass = the process exits 0** (non-zero iff `mismatch > 0` or `new_errors > 0`).
`new_errors` = a problem whose status changed between the two phases (e.g. parsed
without the lib, errors with it = MathBench broke it). Persistent REPL socket
errors (Connection reset / Broken pipe) are retried automatically on fresh
connections; if a key is *still* erroring after `--retries` rounds it is reported
(fail-loud) — re-run to confirm it is just a flake, not a real change.

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

  ACCEPT writes a subjective judgement to a tracked file. Per the repo's CLAUDE.md
  ("never act on assumptions — always ask"), **confirm with the user before
  accepting**. Then:
  ```
  python tools/check_putnam_divergence.py --accept-new --rationale "<why benign>"
  ```
  This appends the current new divergences to `divergence_golden.json` with the
  rationale and date. Tell the user the golden change should be committed so the
  acceptance is auditable (do not commit unless they ask).
  (`--accept-new` is refused together with `--limit` — only accept after a full
  sweep, never a partial one.)

  Guardrail: never `--accept-new` while the goal gate is red. The golden is for
  noise, not for silencing real breakage. You may always choose to FIX instead of
  accept (agent judgment may be stricter than the gate, never looser).

### 5. Promote and rebuild
When the inner loop is fully green (goal gate exits 0, divergence delta either
empty or all consciously accepted, no SKIPs):
1. Move the new `import` into the `imports` list of `Base/MathBench_ProverBase.thy`,
   and the reconciliation statements (`hide_const`/`no_notation`) below its
   `begin` (the body is otherwise empty). Remove them from MathBench_Prover.thy.
   If the import comes from an AFP session not yet a dependency, also add that
   session to the `sessions` clause of `MathBench_ProverBase` in
   `tasks/MathBench_Prover/ROOT` — unlike the inner loop, `isabelle build` needs
   the dependency declared (the child `MathBench_Prover` session inherits it).
2. Rebuild the heap (command above).
3. `python tools/mathbench_repl.py restart` (now picks up the rebuilt heap);
   re-run steps 2–3 to confirm the promoted state matches.

## If the REPL fails to start

`mathbench_repl.py start` waits up to 10 min (cold MathBench_ProverBase heap load
is slow) then exits non-zero. On failure: read `/tmp/mathbench_repl.log`; confirm
the `MathBench_ProverBase` heap is built (`isabelle build` it if not); a wedged
server is recovered with `stop` then `start`. If the divergence tool instead
fails at "reference regeneration" / "No MathBench reference dumps found", that
usually means MathBench_Prover.thy currently won't load — go back to step 1 and
fix the load error first. The helper only ever touches port 7777.

## Golden ledger notes

- `tools/divergence_golden.json` — accepted divergences with rationale, plus
  `meta.putnam_data_sha` (content hash of `data/putnamBench.json` the baseline was
  computed against; `putnam_submodule_commit` is secondary provenance only).
- Identity of an entry excludes file/import-set counts (they fluctuate). If the
  delta shows entries that are really just count changes, the key is wrong — do
  not paper over it by accepting.
- **PutnamBench data drift:** if `data/putnamBench.json` changes, the divergence
  set shifts for reasons unrelated to MathBench. Refresh the golden deliberately
  (note the new `putnam_data_sha`); do not mistake data drift for import-induced
  divergence.

## Files
- `tools/mathbench_repl.py` — start/restart the dedicated REPL on port 7777
- `tasks/MathBench_Prover/MathBench_Prover.thy` — inner-loop edit target
- `tasks/MathBench_Prover/Base/MathBench_ProverBase.thy` — promotion target
- `tasks/MathBench_Prover/env_dump.ML` / `Env_Dump.thy` — reference dump logic
- `tools/check_putnam_divergence.py` — divergence radar
- `tools/divergence_golden.py` — golden ledger library (imported by the radar; not run directly)
- `tools/test_mathbench_goals.py` — authoritative goal-term gate
- `data/putnamBench.json` — the problem set both checks read
