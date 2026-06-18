# Missing-lemma confirmation search

**FIRST load the `missing-lemma-loop` skill** (Skill tool) and follow its **"Git
safety"** rule: your searches are READ-ONLY (grep the distribution / AFP); never
run `git checkout`/`reset`/`stash`/`clean` or otherwise switch or modify the
shared working tree.

You are the confirmation stage of the MathBench missing-lemma loop (see
`MISSING_LEMMA_LOOP.md` at the repo root). A DeepSeek prover agent working on a
PutnamBench problem reported the lemma claims below as "needed but not findable
in the loaded libraries". Your job: for EVERY claim, decide one verdict by
actually searching the sources. Do not filter or judge importance — every claim
gets a verdict.

## Generalize before searching

A claim often states a CASE-SPECIFIC instance of a general fact (e.g. a Riemann
sum for one concrete function/interval). First **generalize** it to the reusable
form it instantiates (over arbitrary variables / functions / intervals), then
search HOL + AFP for **that general form** — that is what would actually be
added to a library. Decide the verdict on the **general** form:

- general form already in the heap → `already_in_heap` (the library has it; the
  prover failed to instantiate it — say so in `notes`);
- general form in a non-heap corpus theory → `missing_import`;
- general form genuinely absent from both corpora → `not_found` (a real library
  gap; give the general statement worth proving in `notes`).

If the fact is irreducibly specific (no clean general form), adjudicate the
specific instance as usual.

## Corpora to search (Isabelle2025-2 toolchain ONLY)

- `contrib/Isabelle2025-2/src/HOL/` — the Isabelle distribution
- `contrib/afp-2026-05-13/thys/` — the AFP

Search strategies (use parallel subagents, one per claim or per claim cluster):
grep for the guessed name; grep for distinctive statement keywords / constant
names; read the candidate `.thy` files and check the statement actually matches
the claimed fact semantically (not just the name).

## Heap membership check

The file given as HEAP_THEORIES_FILE lists everything already loaded in the
MathBench_Prover heap: `Session CHAPTER/NAME` header lines and, under each, the
absolute paths of that session's `.thy` files. A hit counts as **already in
the heap** iff the `.thy` file where you found the lemma appears in that list
(match by absolute path; grep the file).

## Duplicates (safety valve)

Claims reaching you have already passed a duplicate-screening stage, so most
are genuinely new. But if you discover during your search that a claim states
the same fact as an entry in the "Imported / in-heap facts" section (or in a
"Previously adjudicated claims" section, when present), give verdict
`duplicate` with `"duplicate_of": "<that entry's id>"` instead of re-deriving
the verdict. For entries whose status is `imported`, NEVER answer
`already_in_heap`: the loop relies on the duplicate link to detect
provided-but-unfindable lemmas.

## Verdicts

For each claim, exactly one of `duplicate` (see above) or:

- `missing_import` — the fact exists in a corpus theory that is NOT in the
  heap. Report the best single theory to import (prefer the smallest/most
  specific theory; prefer HOL distribution over AFP when both have it; map AFP
  files to `SessionName.TheoryName` via the session's ROOT file in
  `contrib/afp-2026-05-13/thys/<Session>/ROOT`).
- `already_in_heap` — the fact (or an equivalent/stronger lemma) exists in a
  theory already in the heap. This signals a retrieval failure, not an import
  gap. Report the lemma's name and theory.
- `not_found` — you searched both corpora and found no matching fact.

## Output — submit via the `mcp__results__submit_verdicts` tool

Your verdicts are delivered ONLY by calling the
`mcp__results__submit_verdicts` tool. Each verdict object:

```json
{
  "claim_id": "<id from input>",
  "verdict": "missing_import" | "already_in_heap" | "not_found" | "duplicate",
  "duplicate_of": "<prior ledger id, verdict duplicate only>",
  "lemma_name": "<fully qualified fact name, if found>",
  "theory": "<SessionName.TheoryName, if found>",
  "evidence": "<file path and line of the found lemma>",
  "notes": "<one-sentence justification>"
}
```

Rules:
- Every input claim needs an ACCEPTED verdict. The tool validates each item
  and tells you what was rejected and which claims are still unanswered —
  correct and resubmit until it reports all claims answered.
- `missing_import` requires `theory`; `already_in_heap` requires `lemma_name`;
  `duplicate` requires `duplicate_of`.
- Be conservative with `missing_import`: only when you verified the statement
  in the source genuinely provides what the claim asks for.
- Do not write any output files; the tool call is the only deliverable.
