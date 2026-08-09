# CLAUDE.md

## Rules

### Memory writes require explicit approval

Never write to, update, or delete anything in the memory directory without my explicit approval for that specific write. Propose what you want to record and wait for me to agree. Reading memory is fine. When I approve, record it in the memory directory — do NOT put it in a `CLAUDE.md` instead. (Adding a rule to a `CLAUDE.md`, or writing a SKILL, is a separate thing and needs its own explicit approval.)

### Never Act on Assumptions — ALWAYS Ask

CRITICAL: You MUST NEVER make autonomous decisions under ANY uncertainty. If anything is ambiguous, unclear, or inconsistent — stop and ask me BEFORE acting. Never guess, never silently work around issues, never make judgment calls on my behalf. Be proactive: if something MIGHT be worth clarifying, ask first. It is always better to ask one question too many than to make one wrong assumption. When in doubt, ask. When not in doubt, consider whether you should be.

### Shared Working Directory

You operate in a shared working directory alongside other agents. Never use git stash, git checkout, git reset --hard, or any command that discards or hides uncommitted changes.

CRITICAL — NEVER run `git clean` (in any form: `-f`, `-d`, `-x`, `-X`, etc.). It is extremely dangerous: it permanently deletes untracked and git-ignored files with no recovery.

### Commit on `main` — never branch

Commit directly on `main`; never create or switch branches (this is a shared working tree — branching moves every other agent's checkout too). If another agent's uncommitted changes get swept into your commit, that is acceptable — briefly describe their work in the commit message alongside your own, and commit it all together.

### Isabelle builds — never lightly add `-c`

`isabelle build -c` is a *clean build*: the `-c` flag deletes session images before rebuilding, which on this shared checkout destroys the user's and other agents' already-built heaps. NEVER add `-c` to `isabelle build` without explicit user approval. (A plain incremental `isabelle build` without `-c` is fine.)

### Reloading `.ML` changes — just restart the REPL

After editing any Isabelle/ML (`.ML`) source, **just restart the REPL server**. A freshly started REPL loads the `.ML` from source even if it was never built — no `isabelle build` is required. An already-running REPL does NOT auto-reload edited code; restart it to pick up the change. Do NOT rebuild the session heap or chase heap timestamps for an `.ML` edit.

### Consistent Terminology — Never Coin Words

Always use the same term for the same concept, consistently. NEVER coin new words on the fly! Fix a single canonical name the first time a concept appears (if a document has a glossary, the glossary is authoritative), and stick to it in all subsequent discussion, documents, and comments. Express properties as descriptive sentences (e.g. "X does not change with content") — never wrap a property into a new noun.

### Always Reuse Code — Never Reinvent the Wheel

IMPORTANT: Before writing ANY new logic, search the codebase first. Reuse what exists — even if it means importing across modules or adding a parameter to an existing function. Do NOT copy-paste-and-modify; refactor instead.

### Verify, Don't Assume

If you are not sure whether something works, run it. Write code, run tests, check output — do not claim results you have not observed. If you do not know something, say so and ask. Never fabricate facts, paths, APIs, or behavior.

### Speak Plainly — Explain Enough to Be Understood

Always talk like a human being. Do not be stingy with words: spell out what you mean, give the background a reader needs, and be patient. Before sending anything, ask yourself whether I can actually follow it — if a sentence leans on a term, an abbreviation, or a piece of context I may not have in mind, explain it instead of assuming it. Terse, cryptic, jargon-packed answers are a failure even when they are technically correct.

The following habits are FORBIDDEN — each one has actually derailed a working session (2026-08-09):

1. **Compression instead of explanation.** When explaining a mechanism, a design, or a decision, write a patient step-by-step narrative in full sentences, with a concrete running example, defining every term at the point where it first appears. A dense summary that is "technically all there" is a failure if I have to decode it.
2. **Ad-hoc nicknames.** Never invent shorthand labels for concepts mid-conversation (metaphor names, "option 2", "path A", …) and then build later sentences on them. If a concept needs repeated reference, use its full descriptive phrase every time, or its established canonical name — nothing else.
3. **Tables as a substitute for prose.** A table may recap what the surrounding prose has already explained; it must never carry information that exists nowhere else in prose.
4. **Assuming I retain your earlier framing.** Conversations are long. When returning to a topic after any gap, re-establish the context from scratch before building on it. When I ask "what is X?", the answer starts from zero and must not lean on any label or framing from earlier turns.

Comments in source code, though, should be short, on point, and load-bearing.


## Isabelle distributions and AFP

| Directory | Description |
| --- | --- |
| `contrib/Isabelle2024/` | The Isabelle 2024 theorem prover distribution |
| `contrib/afp-2025-02-12/` | Archive of Formal Proofs (2025-02-12 snapshot), paired with Isabelle2024 |
| `contrib/Isabelle2025-2/` | The Isabelle 2025-2 theorem prover distribution |
| `contrib/afp-2026-05-13/` | Archive of Formal Proofs (2026-05-13 snapshot), paired with Isabelle2025-2 |

## Core systems

| Directory | Description |
| --- | --- |
| `contrib/Isa-REPL/` | Isabelle REPL with a Python client (Python → Isabelle) |
| `contrib/Isabelle_RPC/` | Bidirectional RPC letting Isabelle/ML call Python over MessagePack, with callbacks (Isabelle → Python) |
| `contrib/Isa-Mini/` | A minimal, AI-friendly proof language over Isabelle/HOL with high-level commands |
| `contrib/Isa-Mini/IsaMini/AoA/` | The AoA proof agent: LLM-driven proof construction via Minilang |
| `contrib/auto_sledgehammer/` | Sledgehammer wrapper usable as a tactic (`by auto_sledgehammer`); caches results. |
| `contrib/Performant_Isabelle_ML/` | High-performance Isabelle/ML data structures: mutable hash tables and an improved discrimination net (`iNet`). |
| `contrib/Semantic_Embedding/` | Semantic DB management, deformalization (Isabelle entities → English via Claude), and vector-based semantic retrieval. |

