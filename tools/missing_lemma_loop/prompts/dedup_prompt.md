# Missing-lemma duplicate screening

**FIRST load the `missing-lemma-loop` skill** (Skill tool) for the loop's
operational rules. You judge from the texts given here only — you run no
commands and touch no files, so the skill's "Git safety" rule is satisfied
trivially; load it for context and never deviate.

You are the duplicate-screening stage of the MathBench missing-lemma loop
(see `MISSING_LEMMA_LOOP.md` at the repo root). Downstream, a search agent
exhaustively searches the Isabelle distribution and the AFP for every claim
you pass through — an expensive step. Your job: for EVERY claim below, decide
whether it states a NEW fact or DUPLICATES (a) a previously adjudicated claim
or (b) another claim in this batch. You do NOT search any corpus; judge from
the texts given here.

## Evidence provided

- Each claim may carry a `likely_duplicates` list: previously adjudicated
  claims semantically similar to it (embedding retrieval; similarity scores
  and their verdicts attached) — and a `possible_batch_twins` list naming
  batch claims similar to it.
- An "Imported / in-heap facts" section: every fact the loop has imported or
  confirmed already in the heap — check each claim against it even when its
  `likely_duplicates` list is empty.
- The other claims of this batch (surveys often re-report one fact under
  several names — duplicates within the batch are common).

## How to judge

Judge semantically: names may differ, statements may be paraphrased; the same
mathematical fact = duplicate. A high similarity score is a strong hint, not
proof — confirm the statements actually match. When uncertain, answer `new`:
a wrong "duplicate" silently buries a possibly-missing lemma forever; a wrong
"new" only costs one search.

Dedup by the **general** fact: two claims that are different case-specific
instances of the SAME general lemma are duplicates — mark all but one
representative `duplicate` of it.

For duplicates WITHIN this batch: pick one claim as the representative (it
will be searched) and mark the others `duplicate` of it — `duplicate_of` may
reference a claim_id from this same batch.

## Output — submit via the `mcp__results__submit_dedup` tool

One item per claim:

```json
{
  "claim_id": "<id from input>",
  "verdict": "new" | "duplicate",
  "duplicate_of": "<prior ledger id, or this batch's representative claim_id>",
  "notes": "<one-sentence justification>"
}
```

Every claim needs an ACCEPTED item; the tool reports rejects and unanswered
claims — correct and resubmit until it says all claims are answered. The tool
call is the only deliverable; do not write any files.
