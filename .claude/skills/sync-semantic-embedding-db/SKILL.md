---
name: sync-semantic-embedding-db
description: How to refresh the local semantic embedding database (~1.5 GB of LMDB at ~/.cache/Isabelle_Semantic_Embedding). The development channel is the Hugging Face Hub tarball via manage_data.py (get/update). End users instead pull it anonymously from Cloudflare R2 with `semantics_manage.py pull`. Use when setting up or refreshing the semantic DB on a machine, or when deformalizations / vector stores are stale or missing. Do NOT run R2 `push` — it overwrites the shared remote and is a human-only action.
---

Two channels. **Developers** publish and fetch via the Hugging Face Hub (below).
**End users** pull from Cloudflare R2 (last section). If unsure which you are, you
are a developer — use Hugging Face.

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

## Publishing the local cache as the new snapshot

To package the current `~/.cache/Isabelle_Semantic_Embedding` and upload it as the
published snapshot:

1. **Make sure nothing is writing the cache** (a mid-write LMDB packages a corrupt
   snapshot). Confirm no live collection/embedding process holds open data fds —
   idle shells whose cwd is the dir are fine:
   ```bash
   lsof +D ~/.cache/Isabelle_Semantic_Embedding | grep -iv 'cwd\|zsh'
   ```
2. **Package** the whole cache dir (top-level dir must stay `Isabelle_Semantic_Embedding/`
   so the download step extracts cleanly into `~/.cache`). **Exclude the entire
   `embed_cache/` directory** — it is a purely local embedding-request cache
   (a diskcache LMDB keyed by API request, 3-day TTL, often >1 GB), not part of
   the published DB, so it should never ride along in the snapshot. Everything
   else in the cache dir does ride along: `semantics.lmdb/`, the `vector_*.lmdb/`
   store(s), and also `experience_index.lmdb/` and `AoA_Collected/` (verified
   2026-07-09 against the tracked tarball — unlike the R2 snapshot, which carries
   only the first two):
   ```bash
   tar --zstd -cf contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst \
       --exclude='Isabelle_Semantic_Embedding/embed_cache' \
       -C ~/.cache Isabelle_Semantic_Embedding
   ```
3. **Upload** to the Hub and refresh the manifest size (`update` re-uploads an
   existing manifest entry; `-y` skips the confirm prompt). Needs HF creds —
   `source ~/secret.sh` first:
   ```bash
   ./manage_data.py update -y contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst
   ```
4. **Commit + push the updated `data/manifest.json`.** `update` rewrites the
   tarball's `size` field in the manifest; this MUST be committed and pushed, or
   other machines' `manage_data.py get` will verify against the stale size and
   refuse/re-prompt. Commit ONLY this one file (the shared working tree usually
   has unrelated dirty paths):
   ```bash
   git add data/manifest.json
   git commit -m "Bump semantic DB tarball size after re-upload"
   git pull --no-edit && git push
   ```

## End users: pulling from Cloudflare R2

For a user who has `pip install`ed the package but has no repo checkout and no HF
token, R2 serves the database anonymously (no credentials):

```bash
.venv/bin/python contrib/Semantic_Embedding/semantics_manage.py pull
```

It merges into the local cache and backs it up first; `status` shows whether the
remote is newer. Use the venv's python — the shebang's `python3` has no boto3.

Publishing to R2 is `push`, which OVERWRITES the one remote object every user
pulls and needs R2 credentials. **It is a human's call — do not run it yourself.**
