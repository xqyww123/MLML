#!/usr/bin/env python3
"""Manage MLML data files on Hugging Face Hub."""

import argparse
import json
import os
import subprocess
import sys

MLML_BASE = os.path.dirname(os.path.abspath(__file__))
MANIFEST_PATH = os.path.join(MLML_BASE, "data", "manifest.json")
GROUPS = ["core", "tools", "optional"]
GITIGNORE_PATH = os.path.join(MLML_BASE, ".gitignore")


def remote_path(path):
    if path.endswith(".zst"):
        return path
    return path + ".zst"


def needs_compression(path):
    return not path.endswith(".zst")


def load_gitignore():
    try:
        with open(GITIGNORE_PATH) as f:
            return f.read()
    except FileNotFoundError:
        return ""


def ensure_gitignore(path):
    content = load_gitignore()
    lines = content.splitlines()
    entries = [f"/{path}"]
    if needs_compression(path):
        entries.append(f"/{remote_path(path)}")
    new_entries = [e for e in entries if e not in lines]
    if not new_entries:
        return
    with open(GITIGNORE_PATH, "a") as f:
        if content and not content.endswith("\n"):
            f.write("\n")
        for e in new_entries:
            f.write(e + "\n")


def load_manifest():
    try:
        with open(MANIFEST_PATH) as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"Error: {MANIFEST_PATH} not found.", file=sys.stderr)
        sys.exit(1)


def save_manifest(manifest):
    with open(MANIFEST_PATH, "w") as f:
        json.dump(manifest, f, indent=2)
        f.write("\n")


def format_size(size_bytes):
    if size_bytes < 1024:
        return f"{size_bytes} B"
    elif size_bytes < 1024 ** 2:
        return f"{size_bytes / 1024:.1f} KB"
    elif size_bytes < 1024 ** 3:
        return f"{size_bytes / 1024 ** 2:.1f} MB"
    else:
        return f"{size_bytes / 1024 ** 3:.1f} GB"


def file_status(entry):
    path = os.path.join(MLML_BASE, entry["path"])
    if not os.path.exists(path):
        return "missing"
    actual = os.path.getsize(path)
    if actual != entry["size"]:
        return "size_mismatch"
    return "present"


def resolve_files(manifest, paths=None, group=None, all_files=False):
    files = manifest["files"]
    if all_files:
        return list(files)
    if group:
        matched = [f for f in files if f["group"] == group]
        if not matched:
            print(f"Error: no files in group '{group}'.", file=sys.stderr)
            sys.exit(1)
        return matched
    if not paths:
        print("Error: specify file paths, --group, or --all.", file=sys.stderr)
        sys.exit(1)
    result = []
    for p in paths:
        exact = [f for f in files if f["path"] == p]
        if exact:
            result.extend(exact)
            continue
        prefix = [f for f in files if f["path"].startswith(p)]
        if prefix:
            result.extend(prefix)
            continue
        print(f"Error: '{p}' matches no files in manifest.", file=sys.stderr)
        sys.exit(1)
    seen = set()
    deduped = []
    for f in result:
        if f["path"] not in seen:
            seen.add(f["path"])
            deduped.append(f)
    return deduped


def cmd_list(_args):
    manifest = load_manifest()
    files = manifest["files"]
    if not files:
        print("No files in manifest.")
        return

    total_size = 0
    downloaded = 0
    for group in GROUPS:
        group_files = [f for f in files if f["group"] == group]
        if not group_files:
            continue
        print(f"\n{group.capitalize()}:")
        for entry in group_files:
            status = file_status(entry)
            mark = "x" if status == "present" else "!" if status == "size_mismatch" else " "
            size = format_size(entry["size"])
            print(f"  [{mark}] {entry['path']:<55s} {size:>8s}   {entry['description']}")
            total_size += entry["size"]
            if status == "present":
                downloaded += 1

    print(f"\nDownloaded: {downloaded}/{len(files)} files "
          f"({format_size(sum(e['size'] for e in files if file_status(e) == 'present'))} / {format_size(total_size)})")


def cmd_get(args):
    try:
        from huggingface_hub import hf_hub_download
    except ImportError:
        print("Error: huggingface_hub is required. Install with: pip install huggingface_hub",
              file=sys.stderr)
        sys.exit(1)

    manifest = load_manifest()
    targets = resolve_files(manifest, paths=args.paths, group=args.group, all_files=args.all)

    for i, entry in enumerate(targets, 1):
        status = file_status(entry)
        size = format_size(entry["size"])

        if status == "present" and args.skip_existing:
            print(f"  Skipped {entry['path']} (already exists).")
            continue
        elif status == "present" and not args.yes:
            ans = input(f"{entry['path']} already exists ({size}). Overwrite? [y/N] ").strip().lower()
            if ans != "y":
                print(f"  Skipped.")
                continue
        elif status == "size_mismatch" and not args.yes:
            actual = os.path.getsize(os.path.join(MLML_BASE, entry["path"]))
            ans = input(f"{entry['path']} exists but size differs "
                        f"(expected {size}, got {format_size(actual)}). Overwrite? [y/N] ").strip().lower()
            if ans != "y":
                print(f"  Skipped.")
                continue

        rpath = remote_path(entry["path"])
        print(f"[{i}/{len(targets)}] Downloading {entry['path']} ({size})...")
        hf_hub_download(
            repo_id=manifest["repo_id"],
            filename=rpath,
            repo_type=manifest["repo_type"],
            local_dir=MLML_BASE,
            force_download=True,
        )

        if needs_compression(entry["path"]):
            zst_file = os.path.join(MLML_BASE, rpath)
            orig_file = os.path.join(MLML_BASE, entry["path"])
            print(f"  Decompressing...")
            subprocess.run(["zstd", "-d", "-f", zst_file, "-o", orig_file], check=True)
            os.remove(zst_file)

    print("Done.")


def cmd_verify(args):
    manifest = load_manifest()
    if args.paths:
        targets = resolve_files(manifest, paths=args.paths)
    else:
        targets = manifest["files"]

    ok = 0
    for entry in targets:
        status = file_status(entry)
        if status == "present":
            ok += 1
        elif status == "missing":
            print(f"  MISSING  {entry['path']}")
        else:
            actual = os.path.getsize(os.path.join(MLML_BASE, entry["path"]))
            print(f"  SIZE     {entry['path']}  (expected {entry['size']}, got {actual})")

    print(f"\n{ok}/{len(targets)} files OK.")
    if ok < len(targets):
        sys.exit(1)


def cmd_add(args):
    manifest = load_manifest()

    path = args.path
    if os.path.isabs(path):
        path = os.path.relpath(path, MLML_BASE)

    full_path = os.path.join(MLML_BASE, path)
    if not os.path.isfile(full_path):
        print(f"Error: '{full_path}' does not exist.", file=sys.stderr)
        sys.exit(1)

    existing = [f for f in manifest["files"] if f["path"] == path]
    if existing:
        if not args.yes:
            ans = input(f"'{path}' already in manifest. Update? [y/N] ").strip().lower()
            if ans != "y":
                print("Aborted.")
                return
        manifest["files"] = [f for f in manifest["files"] if f["path"] != path]

    size = os.path.getsize(full_path)
    entry = {
        "path": path,
        "size": size,
        "description": args.description,
        "group": args.group,
    }
    manifest["files"].append(entry)
    save_manifest(manifest)
    ensure_gitignore(path)
    print(f"Added {path} ({format_size(size)}) to manifest [{args.group}].")

    if args.upload:
        try:
            from huggingface_hub import HfApi
        except ImportError:
            print("Error: huggingface_hub is required for upload. Install with: pip install huggingface_hub",
                  file=sys.stderr)
            sys.exit(1)

        rpath = remote_path(path)
        compress = needs_compression(path)
        if compress:
            zst_file = full_path + ".zst"
            print(f"Compressing {path}...")
            subprocess.run(["zstd", "-f", full_path, "-o", zst_file], check=True)
            upload_path = zst_file
        else:
            upload_path = full_path

        print(f"Uploading {rpath} to {manifest['repo_id']}...")
        api = HfApi()
        api.upload_file(
            path_or_fileobj=upload_path,
            path_in_repo=rpath,
            repo_id=manifest["repo_id"],
            repo_type=manifest["repo_type"],
        )
        print(f"Uploaded.")

        if compress:
            os.remove(zst_file)


def main():
    parser = argparse.ArgumentParser(description="Manage MLML data files on Hugging Face Hub.")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("list", help="Show available files with download status")

    p_get = sub.add_parser("get", help="Download files from Hugging Face Hub")
    p_get.add_argument("paths", nargs="*", default=[], help="File paths or prefixes to download")
    p_get.add_argument("--all", action="store_true", help="Download all files")
    p_get.add_argument("--group", choices=GROUPS, help="Download all files in a group")
    p_get.add_argument("-y", "--yes", action="store_true", help="Overwrite without prompting")
    p_get.add_argument("--skip-existing", action="store_true", help="Skip files that already exist")

    p_verify = sub.add_parser("verify", help="Verify downloaded file integrity")
    p_verify.add_argument("paths", nargs="*", default=[], help="File paths to verify (default: all)")

    p_add = sub.add_parser("add", help="Add a local file to manifest and optionally upload to HF")
    p_add.add_argument("path", help="Path to the file (relative to repo root or absolute)")
    p_add.add_argument("-d", "--description", required=True, help="Short description of the file")
    p_add.add_argument("-g", "--group", choices=GROUPS, required=True, help="File group")
    p_add.add_argument("--upload", action="store_true", help="Also upload the file to HF Hub")
    p_add.add_argument("-y", "--yes", action="store_true", help="Overwrite existing entry without prompting")

    args = parser.parse_args()
    {"list": cmd_list, "get": cmd_get, "verify": cmd_verify, "add": cmd_add}[args.command](args)


if __name__ == "__main__":
    main()
