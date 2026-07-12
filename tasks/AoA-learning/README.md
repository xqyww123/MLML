# AoA-learning

Replay a corpus of finished Isabelle proofs, hand each goal to the AoA agent
*together with its original Isar proof*, and let the agent distil what it learns into
the shared **experience memory**. The proofs the agent reconstructs are thrown
away — the product of a run is the memories, nothing else.

```
learn.py  (login node, one process)
   │  work-stealing queue of target theories
   │
   ├── Isa-REPL server ─ … ─ Isa-REPL server        (fleet; slurm compute nodes)
   │      running the App  Minilang.AoA_Learning    (learning.ML)
   │      replays a theory from source; at every goal:
   │                                    │
   │                                    ▼
   └────────────────────────► IsaMini.AoA RPC host  (login node, STARTED SEPARATELY)
                                        │            the LLM agent lives here
                                        ▼
                              Semantic_Embedding DB  ($SEMANTIC_DB_DIR)
                                 experience memories + vectors + availability index
```

Three processes, three owners:

| | who starts it | notes |
|---|---|---|
| REPL fleet | `learn.py` (`tools.server.launch_servers`) | `CLUSTER=slurmx` → `srun` on the `SESSION` heap |
| AoA RPC host | **the operator, by hand** | `learn.py` never starts it; every REPL must have `RPC_Host` pointing at it |
| semantic DB | nobody — it is a file tree | `SEMANTIC_DB_DIR`, must be **local disk** (see Pitfalls) |

The RPC host is shared and single: it is the only writer of the semantic DB, which
is what makes the memory dedup and the LMDB write path safe.

## Files

| file | what it is |
|---|---|
| `learn.py` | the driver: fleet, work queue, `control.db`, all reporting |
| `learning.ML` | the App `Minilang.AoA_Learning`: replays a theory, hooks every goal, calls AoA |
| `AoA_Learning_App.thy` | the theory that loads `learning.ML` (`AoA_Learning_Base` session, `ROOT`) |
| `gen_targets.py` | generates the target list **from the session heap** (see below) |
| `targets_full` | the real corpus (612 theories), generated — do not hand-edit |
| `targets`, `targets_pilot` | one-theory smoke tests |
| `cache/aoa_learning_control.db` | resume state (SqliteDict) |
| `logs/<iid>/` | one AoA log dir per goal; `meta.jsonl.zst` is what the reporting mines |

## The target list, and why it is exactly the heap

**A target is a theory that is already loaded in the `SESSION` heap.** `gen_targets.py`
asks Isabelle for that set directly (`Thy_Info.get_names ()` under
`isabelle ML_process -l MathBench_Prover`), drops Isabelle's tool / definitional-package /
code-generation theories and our own infrastructure, and writes what is left:
**612 theories = 376 Isabelle/HOL + 236 AFP**.

Two independent reasons it must be the heap's theories, not "every `.thy` of every
session the ROOT mentions":

*Scope.* The heap is the import closure of `MathBench_ProverBase` — precisely the
material MathBench/Putnam proofs stand on. A session named under `sessions` in a
ROOT only makes its theory *names* resolvable; its other theories are never loaded.
Scraping whole session directories drags in hundreds of theories nothing depends on
(`Collections`, `Word_Lib`, `Refine_Monadic`, `Abstract-Rewriting`, …) and the agent
learns lessons for goals we will never prove. (The first corpus did exactly this:
1636 theories, of which 1024 were off-corpus.)

*Key stability.* `Theory_Hash.hash_of` (`contrib/Isabelle_RPC/Tools/theory_hash.ML`)
hashes a theory by **content** — xxhash128 of the file plus its parents' hashes, byte-0
LSB cleared — only when `Resources.loaded_theory name` holds, i.e. **the theory is in
the heap**. Otherwise it falls back to FNV-1a of the theory **name** with the LSB
**set**: the *WIP* marker, designed for a jEdit buffer whose content is still changing.
An experience-memory key is the XOR of its constituent theories' hashes, so a single
non-heap constituent turns the whole memory into a WIP key — which will not match the
content-hash that same theory gets once it *is* in a heap, and the memory silently
stops being retrievable. Keep every target in the heap and every memory comes out
persistent, keyed byte-identically to what production proving computes.

Regenerate after changing the session's imports:

```bash
python tasks/AoA-learning/gen_targets.py            # -> tasks/AoA-learning/targets_full
```

## Protocol (msgpack, over the Isa-REPL channel)

```
client -> ML   (driver, log_dir, theory_path)          header
ML -> client   (0, pos)                                goal opened at "file:line"
client -> ML   bool                                    run AoA on it? (false = resume-skip)
ML -> client   (1, pos, outcome, iid)                  the AoA run concluded
ML -> client   (2, [msg, …])                           error detail, sent with every
                                                       non-"finished" outcome
ML -> client   5                                       theory replay done
```

`iid` names the goal's AoA log dir (`<log_dir>/<iid>/`); `outcome` is one of

| outcome | meaning | what `learn.py` does |
|---|---|---|
| `finished` | the agent **ran to completion** — it does *not* mean the goal was proved | terminal |
| `timeout` | the App's hard backstop fired (`--timeout-seconds` + 300 s); the agent was wedged | counts as a failed attempt |
| `error` | any other exception | counts as a failed attempt |
| `infra` | the RPC host was unreachable — the agent **never ran** | **not counted**; retried |
| `extraction_skipped` | the original proof has no recognised terminal (`sorry` / `oops`), so there is nothing to learn; `iid=""` | terminal |

"Finished" is deliberately about the *agent*, not the proof: a goal AoA fails to prove
still teaches it something, and that lesson is the point of the run.

## Resume (`control.db`)

A SqliteDict. Goal keys are `"file:line"`, theory keys are the theory's absolute path.

| value | meaning |
|---|---|
| `True` on a goal | finished — terminal |
| `"skipped"` | unparsable original proof — terminal |
| `"givenup"` | failed `MAX_GOAL_ATTEMPTS` (3) **real** attempts — terminal |
| `int n` | failed `n < 3` real attempts — **retried** on the next pass |
| `True` on a `.thy` | every goal of the theory reached a terminal state |

The rules that make an interrupted run recoverable:

* a theory is marked done **only when every one of its goals is terminal**. An
  unresolved theory is requeued for another pass (with a 60 s backoff after an infra
  outage);
* infrastructure failures never consume an attempt — a nine-hour RPC-host outage must
  not burn through the retry budget of every goal it touches;
* a goal that keeps failing for a *real* reason is given up after 3 attempts, so one
  hard goal cannot block its theory from ever completing.

`--dry-run` answers "skip" to every goal (it exercises replay/collector/protocol with
no LLM cost) and therefore **never writes theory-done keys** — otherwise a later real
run would skip the whole corpus.

## What the run reports

Per goal:

```
[srv] goal Foo.thy:214: finished in 62s, 18 tool calls,
      memory created: sum_le_via_mono_pointwise [run total: 15 created, 1 updated]
```

The memory field is **always printed** (`none` when the goal taught nothing) — most
goals produce no memory, and an omitted field is indistinguishable from broken
reporting. Its three counts come from `write_memory`'s own logged response:

* **created** — a new experience was written;
* **updated** — an existing same-name experience was overwritten;
* **rejected** — the agent's memory was too close to one already stored, so it was
  **not written**. Routine, not an error: the agent can re-issue the call to assert
  the two really are different.

Per theory a one-line summary (`RESOLVED (n/m goals finished) … memory: …`), and at the
end of the run the totals, the *names* of every memory created/updated, and the goals
given up. Two warnings mean the pipeline is broken rather than merely unproductive:
`no readable AoA log` (the log dir vanished) and `write_memory calls have no logged
outcome` (the RPC host predates the response-logging fix — restart it).

## Running it (cluster)

```bash
# 1. the shared AoA RPC host on the login node — by hand, NOT by learn.py
#    (pin the login node: the compute REPLs will connect back to this one)

# 2. the fleet + driver
export CLUSTER=slurmx SESSION=MathBench_Prover
export RPC_Host=cscc-login-1.ib0.cscc-new.mbzuai.ac.ae:27182
export SEMANTIC_DB_DIR=/var/tmp/$USER/Isabelle_Semantic_Embedding   # LOCAL disk!
python tasks/AoA-learning/learn.py \
    --targets tasks/AoA-learning/targets_full \
    --log-dir tasks/AoA-learning/logs \
    --timeout-seconds 900 --max-tool-calls 200
```

`--timeout-seconds` is the **per-goal wall-clock budget of one AoA run** (900 s = 15 min;
the App hard-kills at +300 s). It is not a REPL, RPC or fleet timeout.

Environment read by the stack (`learn.py` itself reads none of it):
`CLUSTER`, `SESSION`, `RPC_Host`, `EVAL_SERVERS_CONFIG`, `SBATCH_JOB_NAME`,
`SLURM_EVAL_WALLTIME`, `LOG_LEVEL`, `SEMANTIC_DB_DIR`.

Re-running the same command resumes: finished/skipped/given-up goals are skipped,
everything else is retried.

## Pitfalls (each one cost us a day)

* **The semantic DB must live on local disk.** LMDB uses `mmap` + POSIX locks, whose
  semantics are unreliable on NFS/lustre. Point `SEMANTIC_DB_DIR` at
  `/var/tmp/<user>/…`. Note `/var/tmp` is **per login node** — the DB follows the RPC
  host, so pin the host to one node.
* **`lmdb==1.4.1` is pinned on purpose.** py-lmdb 2.1.0 bundles liblmdb 0.9.35, which
  corrupts a *brand-new empty* database on first write (`MDB_CORRUPTED: Located page was
  wrong type`) on Ubuntu 24.04 — on every filesystem, including tmpfs. Do not "upgrade".
* **After editing any `.ML`, restart the REPL server** — a running REPL does not reload
  it; no `isabelle build` is needed.
* **The proof cache is bypassed** (`AoA_use_proof_cache` / `AoA_store_proof_cache` both
  false), so reconstructed proofs never touch the shared production cache. Memories, by
  contrast, land directly in the shared DB.
