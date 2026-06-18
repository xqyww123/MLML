# Project Index

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

The semantic embedding database (deformalizations + vector stores, an ~3 GB
LMDB collection) lives at `~/.cache/Isabelle_Semantic_Embedding`. To refresh a
machine's copy from the snapshot published on the Hugging Face Hub
(`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst`):

1. **Back up the current cache** — timestamped `.tar.zst`, so a bad sync is recoverable:
   ```bash
   ts=$(date +%Y%m%d_%H%M%S)
   tar --zstd -cf ~/Isabelle_Semantic_Embedding.backup_${ts}.tar.zst \
       -C ~/.cache Isabelle_Semantic_Embedding
   ```
2. **Make sure MLML is up to date** (the tarball pointer is tracked in the repo):
   ```bash
   git pull && git submodule update --init contrib/Semantic_Embedding
   ```
3. **Download the snapshot tarball** from the Hugging Face Hub. Pass `-y` to
   overwrite any existing tarball without prompting (required for
   non-interactive / detached runs — `get` otherwise blocks on a `[y/N]` prompt
   and dies with `EOFError` when a differently-sized tarball already exists):
   ```bash
   ./manage_data.py get -y contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst
   ```
4. **Extract it over the cache** — overwrites `~/.cache/Isabelle_Semantic_Embedding`
   (the tarball's top-level dir is `Isabelle_Semantic_Embedding/`, so extract into `~/.cache`):
   ```bash
   tar --zstd -xf contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst -C ~/.cache
   ```

## Packaging and syncing the Isabelle + AFP distribution

The Isabelle distribution and its paired AFP snapshot are published together as
`contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst` on the Hugging Face Hub.

**Repackage and upload** (after rebuilding the shared jar with
`isabelle scala_build`, applying patches, etc.):
```bash
cd contrib
tar --zstd -cvf Isabelle2025-2_and_afp-2026-05-13.tar.zst Isabelle2025-2 afp-2026-05-13
cd .. && ./manage_data.py update -y contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst
```
`-y` skips the `[y/N]` confirmation (required for non-interactive / detached
runs — `update` otherwise blocks on the prompt and dies with `EOFError`).
`update` regenerates `data/manifest.json` — commit and push it:
```bash
git add data/manifest.json
git commit -m "data: bump Isabelle+AFP tarball size"
git push
```

**Download and unpack** on another machine — mirror image of the above:
```bash
./manage_data.py get -y contrib/Isabelle2025-2_and_afp-2026-05-13.tar.zst
cd contrib
tar --zstd -xf Isabelle2025-2_and_afp-2026-05-13.tar.zst   # overwrites Isabelle2025-2/ + afp-2026-05-13/
```
