# Missing-lemma loop — Phase 2: import expansion + reconciliation

You are the import-expansion stage of the MathBench missing-lemma loop (see
`MISSING_LEMMA_LOOP.md` at the repo root). Confirmed-missing theories are
listed below; your job is to add them to the MathBench_Prover environment and
reconcile, following the `mathbench-import-reconcile` skill EXACTLY. Load that
skill first and follow its procedure (inner loop on `MathBench_Prover.thy`,
divergence radar, goal-term gate, then promote to
`Base/MathBench_ProverBase.thy` + ROOT and rebuild the heap).

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
- Rebuild command (outer loop, after promotion):
  `RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 -o system_heaps MathBench_ProverBase`
- Never use git stash/checkout/reset/clean. Never hand-edit golden test YAMLs
  or `tools/divergence_golden.json` (golden changes go through `--accept-new`
  only, per the divergence policy above).
- If the import fundamentally cannot be reconciled (goal gate stays red no
  matter the FIXes), revert your edits for THAT import, keep the others, and
  record the failure in the result file (below).

## Deliverable — submit via the `mcp__results__submit_result` tool

When done (heap rebuilt, post-rebuild checks green), call the
`mcp__results__submit_result` tool exactly once:

```json
{
  "imported": [{"theory": "Session.Theory", "reconciliations": ["hide_const …", "…"]}],
  "failed": [{"theory": "Session.Theory", "reason": "…"}],
  "divergence_decisions": {"fixed": <n>, "accepted": <m>},
  "heap_rebuilt": true
}
```

`heap_rebuilt` must reflect whether `isabelle build` actually succeeded — never
claim it without having run it. Report every `theory` string EXACTLY as it is
spelled in the "Theories to import" list below (the watcher matches them
verbatim); every listed theory must appear in either `imported` or `failed`.
The tool call is the only deliverable; do not write result files.

## Theories to import

THEORIES_PLACEHOLDER
