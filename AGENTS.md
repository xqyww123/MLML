# Project Index

## General working rules

- Clarify before acting when a requirement is ambiguous, inconsistent, high-risk,
  or cannot be verified from local context. Do not invent facts, paths, APIs, or
  behavior.
- Before writing new logic, search the codebase for existing implementations and
  reuse local patterns where practical. Prefer refactoring or extending existing
  helpers over copy-paste variants.
- Verify behavior with focused commands or tests when the result matters. If a
  check cannot be run, say that explicitly rather than implying it was observed.

## Shared working tree — git rules (READ FIRST)

This repo **and its submodules** are a **shared working tree** with many agents
committing concurrently. Reckless git ops silently destroy others' uncommitted work.

- **Never change the branch.** No `git checkout` / `git switch` / `git checkout -b`:
  they move the *shared* HEAD for every agent and can wipe out others' uncommitted
  changes. Commit to whatever branch the tree is on — the user controls it; leave
  it as you found it.
- **Never** `git stash`, `git reset --hard`, `git checkout -- <path>`, or
  `git clean` (any form) — they discard uncommitted work irrecoverably.
- **Commit only your own files, explicitly listed:** `git add <file> …` then
  `git commit`. Never `git add -A` / `git add .` / `git commit -a` (they sweep up
  others' in-progress changes).
- **Advance a target branch (e.g. `main`) without touching the working tree**
  (e.g. when HEAD is parked on another branch) by pushing the commit ref as a
  fast-forward: `git push origin <sha>:<branch>` (no `--force`).

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

## Syncing the semantic embedding database from the published snapshot

The semantic embedding DB (deformalizations + vector stores, ~3 GB LMDB) lives at
`~/.cache/Isabelle_Semantic_Embedding`. To refresh from the Hugging Face Hub
snapshot (`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst`):

1. **Back up the current cache** (timestamped, so a bad sync is recoverable):
   ```bash
   ts=$(date +%Y%m%d_%H%M%S)
   tar --zstd -cf ~/Isabelle_Semantic_Embedding.backup_${ts}.tar.zst \
       -C ~/.cache Isabelle_Semantic_Embedding
   ```
2. **Update MLML** (the tarball pointer is tracked in the repo):
   ```bash
   git pull && git submodule update --init contrib/Semantic_Embedding
   ```
3. **Download the snapshot tarball.** `-y` overwrites without prompting (required
   for non-interactive / detached runs — `get` otherwise blocks on a `[y/N]`
   prompt and dies with `EOFError` when a differently-sized tarball exists):
   ```bash
   ./manage_data.py get -y contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst
   ```
4. **Extract over the cache** (tarball top-level dir is `Isabelle_Semantic_Embedding/`,
   so extract into `~/.cache`):
   ```bash
   tar --zstd -xf contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst -C ~/.cache
   ```

## Packaging and syncing the Isabelle + AFP distribution

Isabelle + its paired AFP snapshot are published together as
`contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst` on the Hugging Face Hub.

**Repackage and upload** (after rebuilding the shared jar with `isabelle scala_build`,
applying patches, etc.). `-y` skips the `[y/N]` confirmation (required for
non-interactive / detached runs — else `update` blocks on the prompt and dies with
`EOFError`); `update` regenerates `data/manifest.json`, so commit and push it:
```bash
cd contrib
tar --zstd -cvf Isabelle2025-2_and_afp-2026-05-13.tar.zst Isabelle2025-2 afp-2026-05-13
cd .. && ./manage_data.py update -y contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst
git add data/manifest.json
git commit -m "data: bump Isabelle+AFP tarball size"
git push
```

**Download and unpack** on another machine — mirror of the above:
```bash
./manage_data.py get -y contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst
cd contrib
tar --zstd -xf Isabelle2025-2_and_afp-2026-05-13.tar.zst   # overwrites Isabelle2025-2/ + afp-2026-05-13/
```
