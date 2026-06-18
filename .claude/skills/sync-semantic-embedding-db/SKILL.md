---
name: sync-semantic-embedding-db
description: How to refresh the local semantic embedding database (~3 GB LMDB at ~/.cache/Isabelle_Semantic_Embedding) from the published Hugging Face Hub snapshot (contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst) — back up the current cache, pull the tracked tarball pointer, download with manage_data.py, and extract over the cache. Use when setting up or refreshing the semantic DB on a machine, or when deformalizations / vector stores are stale or missing.
---

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
