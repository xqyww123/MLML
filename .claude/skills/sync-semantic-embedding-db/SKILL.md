---
name: sync-semantic-embedding-db
description: How to install or refresh the semantic embedding database (LMDB stores at ~/.cache/Isabelle_Semantic_Embedding; layered — a read-only system DB under the writable user DB). The development channel is the Hugging Face Hub tarball via manage_data.py (get/update). End users instead install the system DB from the conda channel (the isabelle-semantic-data package, or `isabelle-semantics pull`). Use when setting up or refreshing the semantic DB on a machine, or when deformalizations / vector stores are stale or missing. Do NOT dispatch `isabelle-semantics release` — publishing is a human-only action.
---

Two channels. **Developers** publish and fetch the full working DB via the
Hugging Face Hub (below). **End users** install the read-only **system DB**
from the conda channel (last sections). If unsure which you are, you are a
developer — use Hugging Face. (Mis-picking is survivable: a developer on the
conda path gets only the read-only system layer — do not mistake that for
"missing data"; an end user on the HF path merely needs a repo checkout and
does extra work for a writable full copy.)

The DB is layered (`contrib/Semantic_Embedding/SEMANTIC_DB_LAYERED_PLAN.md`):
the system DB (`$PREFIX/share/isabelle-semantic-data/` from conda, or
`<cache>/system/` from `pull`) is read-only under the writable user DB at
`~/.cache/Isabelle_Semantic_Embedding` (or `$SEMANTIC_DB_DIR`); reads consult
user first, deletions are tombstones in the user layer. **Nothing downloads
automatically at runtime** (a conda install may bring the data package in as a
dependency — that is solver-time, not runtime). After installing/updating
**either layer** — a system-DB install, or the dev sync's extraction over the
user DB — restart any running RPC host / REPL server (the mmap pins the old
files). `isabelle-semantics status` shows both layers.

All developer commands below run at the **MLML checkout root**.
`isabelle-semantics` is the console script of an installed
`isabelle-semantic-embedding` (conda) / `Isabelle_Semantic_Embedding` (pip);
on a source checkout without an install, run
`python contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/isabelle_semantics.py …`
instead.

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
2. **Update MLML** (`git pull` refreshes the tarball pointer —
   `data/manifest.json` in the super-repo; the submodule update refreshes the
   Semantic_Embedding code, a separate concern):
   ```bash
   git pull && git submodule update --init contrib/Semantic_Embedding
   ```
3. **Download the snapshot tarball.** `-y` overwrites without prompting (required
   for non-interactive / detached runs — `get` otherwise blocks on a `[y/N]`
   prompt and dies with `EOFError` when the tarball already exists locally,
   whatever its size):
   ```bash
   ./manage_data.py get -y contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst
   ```
4. **Stop any running RPC host / REPL server, extract over the cache, restart.**
   The extraction replaces live LMDB files in place — a running host keeps
   serving the old mmap'd inodes, and a concurrent writer can interleave writes
   into the freshly extracted stores. Tarball top-level dir is
   `Isabelle_Semantic_Embedding/`, so extract into `~/.cache`:
   ```bash
   tar --zstd -xf contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst -C ~/.cache
   ```

## Publishing the local cache as the new snapshot

To package the current `~/.cache/Isabelle_Semantic_Embedding` and upload it as the
published snapshot. This upload is ALSO the exact input of the next conda data
release: CI downloads this very tarball, drops the tombstones, and packages the
result — what you upload is what everyone eventually gets.

1. **Make sure nothing is writing the cache** (a mid-write LMDB packages a corrupt
   snapshot). Confirm no live collection/embedding process holds open data fds —
   idle shells whose cwd is the dir are fine:
   ```bash
   lsof +D ~/.cache/Isabelle_Semantic_Embedding | grep -iv 'cwd\|zsh'
   ```
   Proceed only when nothing remains but the header line; any surviving line
   names a process to stop first. NB `lsof +D` exits non-zero when nothing
   matches — no output plus exit 1 is the GOOD case, not a failure.
2. **Package** the whole cache dir (top-level dir must stay `Isabelle_Semantic_Embedding/`
   so the download step extracts cleanly into `~/.cache`). **Exclude the entire
   `embed_cache/` directory** — it is a purely local embedding-request cache
   (a diskcache LMDB keyed by API request, 3-day TTL, often >1 GB), not part of
   the published DB, so it should never ride along in the snapshot. **Also
   exclude a pulled `system/` copy and the install lock** — the system layer is
   the published artifact itself and must never ride into its own source
   snapshot. Everything else in the cache dir does ride along:
   `semantics.lmdb/`, the `vector_*.lmdb/` store(s), `theory_hash.lmdb/` (the
   theory-hash registry — shared data, not a local cache), and also
   `experience_index.lmdb/` and `AoA_Collected/` — tombstones and WIP included
   (CI's export strips what must not ship):
   ```bash
   tar --zstd -cf contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst \
       --exclude='Isabelle_Semantic_Embedding/embed_cache' \
       --exclude='Isabelle_Semantic_Embedding/system' \
       --exclude='Isabelle_Semantic_Embedding/.install_system_db.lock' \
       -C ~/.cache Isabelle_Semantic_Embedding
   ```
3. **Upload** to the Hub and refresh the manifest size (`update` re-uploads an
   existing manifest entry; `-y` skips the confirm prompt). HF write access
   comes from the cached `huggingface-cli login` token
   (`~/.cache/huggingface/token`) — log in once on a new machine; sourcing
   `secret.sh` does NOT provide it:
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

## End users: installing the system DB

No repo checkout, no HF token, no credentials. In a conda environment the
`isabelle-ai` metapackage already brings the DB in as a hard dependency;
standalone:

```bash
conda install -c https://conda.qiyuan.me isabelle-semantic-data
```

Outside conda (the `Isabelle_Semantic_Embedding` pip package provides the
`isabelle-semantics` script):

```bash
isabelle-semantics pull
```

`pull` resolves the newest package on the channel, verifies it, and atomically
swaps it into `<cache>/system/`; re-run it any time to update (prints "Already
current" when there is nothing new). It refuses when a conda-delivered system
DB would shadow the pulled copy — update through conda there. Then restart any
running RPC host / REPL server.

## Releasing the published data package (human-only)

`isabelle-semantics release` warns when the local DB looks newer than the last
HF upload (publish to HF first — the release ships the HF state, see above),
then dispatches the `release-semantic-db` workflow in
`xqyww123/isabelle-packaging-ci`: it runs `isabelle-semantics export` over the
HF tarball (tombstones dropped, experience index rebuilt, manifest stamped,
gates run) and publishes `isabelle-semantic-data` to conda.qiyuan.me. The
package version derives from the export timestamp — there is nothing to
choose. **Do not dispatch this yourself — it is a human's call.** Ordering: a
new `isabelle-semantic-embedding` must be on the channel before the first data
release that changes format expectations.
