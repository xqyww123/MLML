---
name: sync-isabelle-afp-distribution
description: How to repackage/upload and download/unpack the Isabelle + paired AFP distribution, published together as contrib/Isabelle2026_and_afp-2026-10-26.tar.zst on the Hugging Face Hub (via manage_data.py update/get). Use when publishing a rebuilt Isabelle+AFP tarball (after isabelle scala_build, patches, etc.) or installing/refreshing the distribution on another machine.
---

## Packaging and syncing the Isabelle + AFP distribution

Isabelle + its paired AFP snapshot are published together as
`contrib/Isabelle2026_and_afp-2026-10-26.tar.zst` on the Hugging Face Hub.

**Repackage and upload** (after rebuilding the shared jar with `isabelle scala_build`,
applying patches, etc.). `-y` skips the `[y/N]` confirmation (required for
non-interactive / detached runs — else `update` blocks on the prompt and dies with
`EOFError`); `update` regenerates `data/manifest.json`, so commit and push it:
```bash
cd contrib
tar --zstd --exclude=Isabelle2026/.git -cvf Isabelle2026_and_afp-2026-10-26.tar.zst Isabelle2026 afp-2026-10-26
cd .. && ./manage_data.py update -y contrib/Isabelle2026_and_afp-2026-10-26.tar.zst
git add data/manifest.json
git commit -m "data: bump Isabelle+AFP tarball size"
git push
```

**Download and unpack** on another machine — mirror of the above:
```bash
./manage_data.py get -y contrib/Isabelle2026_and_afp-2026-10-26.tar.zst
cd contrib
tar --zstd -xf Isabelle2026_and_afp-2026-10-26.tar.zst   # overwrites Isabelle2026/ + afp-2026-10-26/
```
