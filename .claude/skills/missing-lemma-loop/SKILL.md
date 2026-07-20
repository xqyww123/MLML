---
name: missing-lemma-loop
description: Operational pipeline to start, monitor, STOP, and recover the MathBench missing-lemma loop running in multi-node fleet mode on the MBZUAI cluster (watcher + slurmx fleet REPLs + login-node RPC host + serial adjudication + phase-2 import reconciliation). Use when launching/resuming the fleet run, stopping it cleanly, recovering after a crash, or applying the hard-won operational rules (correct kill sequence, git safety on the shared checkout, shell/conda/timeout fixes, re-collection prerequisite). For the single-machine AoA×PutnamBench eval use `aoa-putnam-eval` instead; for the design rationale of the loop see `MISSING_LEMMA_LOOP.md`.
---

# Missing-lemma loop — fleet operations pipeline

Runbook to start / monitor / stop / recover the loop on the MBZUAI cluster in
`--fleet` mode. Design rationale: `MISSING_LEMMA_LOOP.md` (repo root).

## Topology

```
login node (cscc-login-2)                       compute nodes (cn-05, cn-06)
  watcher.py --fleet  ──spawns──>  evaluator_top.py (slurmx driver)  ──srun──>  6×REPL each
       │                                    │ (resurrects slurm jobs!)            (load 794MB heap)
       │ spawns SDK agents                  ▼                                         │ AoA prover
       │ (adjudication/search/dedup/phase2) slurm jobs "mlloop"                       │ surveys
       ▼                                                                              ▼
  login RPC host  Isabelle_RPC_Host.fork_and_launch__()  0.0.0.0:27182  <──IB──── compute REPLs
   (AOA_MISSING_LEMMA_SURVEY lives HERE; survey docs flow back through it)
```

- Real checkout: `/lustre/scratch/users/qiyuan.xu/MLML` (NOT `~/MLML`).
- Fleet config: `config/evaluation_servers.csv` (cn-05/cn-06 × 6 ports = 12 evaluators).
- See `cn22-mbzuai-deployment` memory for access details.

## Environment for every cluster shell

`ssh mbzuai-fm-2` commands are **non-interactive non-login** — they do NOT source
conda. Prepend:
```bash
source ~/miniconda3/etc/profile.d/conda.sh; conda activate base; source envir.sh
```
For the watcher launch also `source secret.sh` (DeepSeek/Fireworks keys). Use
`ssh -A` so git fetch/pull works (agent-forwarded key; the cluster has no GitHub
auth). One-off Python without sourcing: full path `/home/qiyuan.xu/miniconda3/bin/python`.

## Start the fleet

```bash
ssh -A mbzuai-fm-2 'cd /lustre/scratch/users/qiyuan.xu/MLML
  source ~/miniconda3/etc/profile.d/conda.sh; conda activate base; source envir.sh; source secret.sh
  nohup python -m tools.missing_lemma_loop.watcher run --fleet --driver DeepSeek.V4-pro \
    --timeout-seconds 1800 --job-name mlloop \
    --log-dir /lustre/scratch/users/qiyuan.xu/MLML/missing_lemma_loop_logs \
    --result /lustre/scratch/users/qiyuan.xu/MLML/result-missing-lemma-loop.db \
    >> _watcher_nightrun.log 2>&1 & echo "watcher PID $!"'
```
Healthy startup log: `Loaded 12 servers` → `embedding cache prewarmed` →
`Isabelle_RPC_Host pid … up` → `launching slurmx fleet eval` → fleet jobs appear
in `squeue` on cn-05/cn-06. Heap is `MathBench_ProverBase` under
`contrib/Isabelle2025-2/heaps/polyml-*/`.

**Before RESTARTING** after an import or the infra_filter fix: re-collect the
semantic DB first — see "re-collection prerequisite" below. Skipping it makes
the loop re-trigger phase-2 on already-imported theories.

## STOP the fleet — the correct kill sequence (CRITICAL)

**Killing the watcher alone does NOT stop the run.** Two traps:
1. The watcher spawns an orphan **`evaluator_top.py` slurmx driver that keeps
   RESUBMITTING the slurm jobs** — after `scancel`, `squeue` repopulates within
   seconds because the orphan re-launches them.
2. `kill watcher` does NOT run its scancel / RPC-host teardown (uncaught crash or
   SIGTERM skips atexit), so the fleet jobs and the login RPC host survive.

Correct order (kill the resurrectors BEFORE scancel). Find the pids:
`watcher_pid` = `pgrep -u $USER -f 'watcher.py'`,
`rpc_pid` = `cat missing_lemma_loop_state/RPC_0.0.0.0_27182.pid`.
```bash
# 1. kill watcher + orphan evaluator_top + any orphan SDK agents  (stops resurrection)
kill -TERM <watcher_pid> $(pgrep -u $USER -f evaluator_top) \
                         $(pgrep -u $USER -f 'claude_agent_sdk/_bundled/claude')
# 2. cancel the fleet jobs
scancel -u $USER --name=mlloop
# 3. kill the login RPC host
kill -TERM <rpc_pid>      # Isabelle_RPC_Host.fork_and_launch__ ... 0.0.0.0:27182
# 4. VERIFY: squeue empty, port free, no loop procs
squeue -u $USER -h | wc -l            # → 0
ss -ltnH | grep -c 27182              # → 0
```
Gotchas:
- **Never `pkill -f missing_lemma_loop` / `-f evaluator_top`** — it self-matches
  your own ssh shell (kills the session, exit 255). Use explicit PIDs, or a
  bracket trick (`missing[_]lemma_loop`). When checking with `pgrep -af`, the
  bash `-c` running your command also self-matches — filter it out.
- **Flaky login connectivity** truncates ssh commands mid-run (output stops with
  no error). Always RE-VERIFY the final state with a fresh minimal connection;
  do not assume a kill landed.
- Other users' `…/_bundled/claude` (vscode sessions) are NOT yours — `pgrep -u $USER`
  scopes to qiyuan.xu; never touch others'.

## Git safety on the shared `/lustre` checkout (HARD RULE)

The checkout is shared with other agents that hold uncommitted WIP (e.g.
`contrib/Isa-Mini/translator`, `data/miniF2F` — known bad pins, leave them).

- **严禁动 git 切换目录树**: never `git checkout <ref>` / `git checkout -- <path>`
  / `git reset --hard` / `git stash` / `git clean`, or anything that switches or
  discards the working tree. To undo a change, **re-apply it with Edit/Write**,
  not git. (Restoring a file to HEAD via Edit is fine; `git checkout` is not.)
- To SYNC to origin: fetch, then **`git merge --ff-only origin/main`** (refuses
  anything that is not a clean fast-forward — never conflicts, never touches
  unrelated WIP). Update only the submodules whose pin actually moved
  (`git submodule update --init contrib/<that-one>`), never `--recursive` over
  everything (would disturb other agents' nested-submodule WIP).
- Stage commits with explicit paths (`git add tasks/… tools/…`), never `git add -A`;
  leave the other agents' WIP untouched. Commit/push only when the user asks.

## Already fixed — do not re-debug or re-propose

- **conda-init hang**: `.zshrc`/`.bashrc` now source static `conda.sh` + `conda
  activate base` instead of the `$(conda shell.<sh> hook)` python fork that hung
  on NFS under load (fixed 2026-06-17; backups `~/.{bash,zsh}rc.bak-*`).
- **SDK Bash auto-background wedge** (commands SIGTERMed past the foreground
  timeout, output unreadable → agent thinks the shell is dead): mitigated by
  `BASH_DEFAULT_TIMEOUT_MS=300000` in `ClaudeAgentOptions.env` (watcher.py,
  commit a1bd565). The deterministic-Python phase-2 fix was **vetoed — do not
  propose it.**

## phase-2 import reconciliation + the re-collection prerequisite

- phase-2 promotes a confirmed missing import into `Base/MathBench_ProverBase.thy`
  + ROOT, rebuilds the heap, and reconciles divergences — see the
  `mathbench-import-reconcile` skill (which the phase-2 agent loads). It runs the
  divergence radar + the authoritative goal-term gate (639/639 must match).
- **The survey canary was DELETED** (commit f7a5d2c) — it false-positived on
  healthy/rebooting fleets (keyed only on new survey docs). Do not re-add; the
  `--canary-seconds` flag is now accepted-but-unused.
- **Re-collection is a HARD prerequisite before restarting after an import or the
  infra_filter `Num.` fix.** The semantic DB is built by a separate collect run.
  If you restart without re-collecting, the search agent (querying the stale DB
  that lacks the newly-imported theory's lemmas) **re-confirms it as a missing
  import** → triggers a redundant phase-2 → the agent, comparing Base against a
  stale baseline snapshot and unable to re-validate, **reverts the promotion**.
  This actually happened 2026-06-17.
- When you complete an import MANUALLY (outside the loop), mark its claims
  `imported` in the ledger (status `imported`, `resolution.theory` set,
  `semantic_collect_failed: true`), **NOT `pending`** — `_theory_imported` only
  recognizes status `imported`, so pending re-triggers phase-2 for an
  already-imported theory.
- **phase-2 agent rule — never blindly revert an already-promoted import.** A
  theory ALREADY in `Base/MathBench_ProverBase.thy` + ROOT (absent from
  `MathBench_Prover.thy`) is a validated prior promotion, NOT a crash orphan —
  even if the watcher baseline lacks it. Report `imported`; never delete it to
  "match the baseline" (that destroyed verified work, 2026-06-17). If genuinely
  unsure, leave files UNCHANGED and say so.
- After a crash, before restarting: delete `missing_lemma_loop_state/phase2/PROMOTING.json`
  (else `_recover_crashed_promotion` acts on a stale snapshot), and run the kill
  sequence above to clear orphans.

## State files (under `missing_lemma_loop_state/`)

`ledger.json` (claims + statuses), `fleet_eval.log` (eval progress / connection
errors), `rpc_host.log` (compute connections + AoA tool calls = survey channel
alive), `_watcher_nightrun.log` (watcher events), `phase2/` (snapshots + build
logs + PROMOTING.json marker). The dir is gitignored — never committed.
