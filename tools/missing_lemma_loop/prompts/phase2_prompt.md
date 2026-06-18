# Missing-lemma loop — Phase 2: import expansion + reconciliation

**FIRST, before anything else, load the `missing-lemma-loop` skill** via the
Skill tool and follow its operational rules — especially **"Git safety on the
shared `/lustre` checkout"** and the **phase-2 guidance** (NEVER blindly revert
an import you find already promoted in `Base/MathBench_ProverBase.thy`; it is
most likely validated prior/manual work, not a crash orphan — see that rule).

You are the import-expansion stage of the MathBench missing-lemma loop (see
`MISSING_LEMMA_LOOP.md` at the repo root). Confirmed-missing theories are
listed below; your job is to add them to the MathBench_Prover environment and
reconcile, following the `mathbench-import-reconcile` skill EXACTLY — but ONLY
its judgment part: the inner loop on `MathBench_Prover.thy` (divergence radar,
goal-term gate, FIX/ACCEPT decisions) and the PROMOTION EDITS
(`Base/MathBench_ProverBase.thy` + ROOT). You do NOT rebuild the heap: the
skill's outer-loop `isabelle build` step and the post-rebuild goal-gate
re-check are executed deterministically by the watcher after you submit.
Long-running build commands inside this session destabilize the pipeline —
never run them.

## Unattended divergence policy (user authorization of 2026-06-11)

You decide every NEW divergence YOURSELF — FIX or ACCEPT — applying the
skill's own criteria. The user has explicitly waived the skill's
"confirm with the user before accepting" step for this loop, ON THE CONDITION
that every decision is recorded for later audit:

- For EVERY NEW divergence (whether you FIX or ACCEPT), append one entry to
  `missing_lemma_loop_state/divergence_decisions.md`:
  date · the divergence (short name, the conflicting resolutions) ·
  your decision (FIX / ACCEPT) · for FIX the exact reconciliation line you
  added · for ACCEPT the rationale. No divergence may go unrecorded.
- ACCEPT only via
  `python tools/check_putnam_divergence.py --accept-new --rationale "<why>"`
  — NEVER hand-edit `tools/divergence_golden.json`. The skill's guardrails
  still bind: never accept while the goal-term gate is red, never accept after
  a partial sweep, and when uncertain prefer FIX (stricter is always allowed).

## Hard rules

- `source envir.sh` in every shell; run everything from the repo root.
- Only touch the dedicated port-7777 REPL (`python tools/mathbench_repl.py …`)
  as the skill prescribes. NEVER touch the REPL on port 6666 — the outer
  watcher owns it and will restart it after you finish.
- NEVER run `isabelle build` (the heap rebuild is the watcher's deterministic
  step, performed after your submission). Do not background long commands and
  wait on them — every PRE-PROMOTION inner-loop step fits a normal foreground
  call; always pass the maximum timeout (600000 ms). If a `mathbench_repl.py
  restart` call still times out, do not background anything: run
  `mathbench_repl.py start` again in a fresh foreground call (it reattaches
  to the ongoing startup).
- Once your PROMOTION EDITS are in place, do NOT touch the port-7777 REPL
  again — no `mathbench_repl.py restart`, no divergence radar, no goal gate.
  The moment `Base/MathBench_ProverBase.thy` has CHANGED since its heap was
  built, a 7777 restart silently triggers a FULL heap rebuild inside
  repl_server.sh (~15 min, cannot fit any foreground call, leaves an orphan
  build when it times out) — that rebuild is the watcher's job, done after
  you submit. Your final validation is the last all-green inner loop run
  BEFORE the promotion edits; after the edits, call
  `mcp__results__submit_result` immediately.
- Never use git stash/checkout/reset/clean. Never hand-edit golden test YAMLs
  or `tools/divergence_golden.json` (golden changes go through `--accept-new`
  only, per the divergence policy above).
- If the import fundamentally cannot be reconciled (goal gate stays red no
  matter the FIXes), revert your edits for THAT import, keep the others, and
  record the failure in the result (below).

## Deliverable — submit via the `mcp__results__submit_result` tool

When done (inner loop green, promotion edits in place: import + its
reconciliations moved into `Base/MathBench_ProverBase.thy`, session added to
the `MathBench_ProverBase` `sessions` clause in ROOT if new, and removed from
`MathBench_Prover.thy`), call the `mcp__results__submit_result` tool exactly
once:

```json
{
  "imported": [{"theory": "Session.Theory", "reconciliations": ["hide_const …", "…"]}],
  "failed": [{"theory": "Session.Theory", "reason": "…"}],
  "divergence_decisions": {"fixed": <n>, "accepted": <m>},
  "files_promoted": true
}
```

`imported` means "validated by the inner loop and promoted in the files" —
the watcher then rebuilds the heap and re-runs the goal gate itself.
`files_promoted` must reflect what you actually edited — never claim it
without having made the promotion edits. Report every `theory` string EXACTLY
as it is spelled in the "Theories to import" list below (the watcher matches
them verbatim); every listed theory must appear in either `imported` or
`failed`. The tool call is the only deliverable; do not write result files.

## Theories to import

THEORIES_PLACEHOLDER
