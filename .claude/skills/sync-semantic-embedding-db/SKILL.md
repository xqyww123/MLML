---
name: sync-semantic-embedding-db
description: How to refresh the local semantic embedding database (~1.5 GB of LMDB at ~/.cache/Isabelle_Semantic_Embedding). Two channels — Cloudflare R2 via `semantics_manage.py pull/push/status` (merges key-by-key, preferred), and the older Hugging Face Hub tarball via manage_data.py (overwrites wholesale). Use when setting up or refreshing the semantic DB on a machine, or when deformalizations / vector stores are stale or missing.
---

## Two channels, and how they differ

| | Cloudflare R2 (`semantics_manage.py`) | Hugging Face Hub (`manage_data.py`) |
| --- | --- | --- |
| download | **merges** into the local stores, key by key | **overwrites** the cache directory |
| upload | overwrites the single remote object | overwrites the published tarball |
| contents | `semantics.lmdb` + `vector_*.lmdb` only | those, plus `experience_index.lmdb` and `AoA_Collected/` |
| staleness check | one HEAD request, free | download and compare sizes |

Prefer R2. Extracting the HF tarball over a cache that has local work discards it;
`pull` keeps both sides. The R2 snapshot deliberately omits `experience_index.lmdb`
— it is a derived view of the EXPERIENCE records, and `pull` rebuilds it.

## Syncing over Cloudflare R2

One-time setup. The two credentials have no defaults and are read only from the
environment; everything else has a built-in default:

```bash
# in secret.sh (gitignored)
export R2_ACCESS_KEY_ID=...
export R2_SECRET_ACCESS_KEY=...
```

Optional settings live in `~/.config/Isabelle_Semantic_Embedding/config.yaml`,
seeded from the package template on first run. Any key may be overridden by an
environment variable (`R2_BUCKET`, `R2_AUTO_PULL`, …); env wins over the file,
the file wins over the code defaults.

```bash
cd contrib/Semantic_Embedding
source ../../secret.sh

./semantics_manage.py status            # one HEAD request: is there anything newer?
./semantics_manage.py pull              # download + merge (backs up first)
./semantics_manage.py push              # pack + upload, OVERWRITING the remote
```

Both accept `--dry-run`, which never fails: it prints what it would do and names
whatever would block the real run. `pull` takes `--no-backup`; `push` and `pull`
take `--force`.

**Always `pull` before you `push`.** The two are asymmetric: `pull` merges, `push`
replaces the whole remote object. Pushing from a machine with less data leaves
everyone else pulling an incomplete set — the data is still on the machine that
had it, but the next person to collect will re-interpret and re-embed theories
that already existed, which costs real API money. `push` refuses when the remote
has moved since this machine last synced; `--force` overrides that.

Guardrails, all of which stop the operation before anything is written:

- neither command runs while another process holds the database open (LMDB has a
  single writer, and packing a live store captures a torn snapshot);
- the snapshot's `x-amz-meta-*` metadata is checked *before* the download —
  schema version, vector format (`q15`, not the pre-migration `float32`), and
  embedding dimension;
- after extraction and before the merge, a snapshot carrying legacy records
  (theorem keys with no constituent list) is refused;
- `pull` backs up the whole cache to `~/Isabelle_Semantic_Embedding.backup_<ts>.tar.zst`
  and keeps the last two. **That backup is the only way to undo a merge.**

Merge rule: remote records win, with one exception — a theory marked `finished`
locally stays finished even if the snapshot has it as WIP. (Otherwise the next
collection run would re-interpret and re-embed it.)

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
