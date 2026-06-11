"""Permission support for the missing-lemma-loop agents.

Policy (用户拍板 2026-06-11): permissions are answered EXCLUSIVELY by Claude
Code's built-in ``permission_mode="auto"`` classifier — no self-made judging
("永远不要用你自己写的 PermissionGate"). If auto mode is unavailable, the run
must CRASH loudly, never fall back (watcher sets it via an explicit
``set_permission_mode("auto")``, which raises on unavailability).

The only thing defined here besides the mission texts is
``static_pretooluse_hook``: a deterministic PreToolUse hook enforcing the
repo's hard red lines (git state-changing commands, rm -rf, port 6666,
process killing, hand-edits of golden files) BEFORE the permission flow, so
red-line calls never even reach the classifier. It contains no model and no
judgment — pure pattern rules.
"""

from __future__ import annotations

import re
from datetime import datetime
from pathlib import Path

# (pattern, reason) — checked ONLY against Bash command strings.
# Repo red lines; deterministic, never model-judged.
_STATIC_DENY_BASH: list[tuple[re.Pattern, str]] = [
    # tolerate options (with or without a separate value: -C <dir>, -c k=v)
    # between `git` and the subcommand; restore/switch also discard
    # uncommitted changes.
    (re.compile(r"\bgit\b(?:\s+-\S+(?:\s+[^-\s]\S*)?)*"
                r"\s+(stash|checkout|reset|clean|restore|switch)\b"),
     "git state-changing commands are forbidden in this shared working dir"),
    # rm with both recursive and force flags, in any order/case/spelling
    (re.compile(r"\brm\b(?=[^|;&]*\s(-[a-zA-Z]*[rR]|--recursive))"
                r"(?=[^|;&]*\s(-[a-zA-Z]*[fF]|--force))"),
     "rm -rf is forbidden for loop agents"),
    (re.compile(r"\bfind\b[^|;&]*\s-delete\b"),
     "find -delete is forbidden for loop agents"),
    (re.compile(r"(^|[\s:=/])6666\b"),
     "the 6666 REPL belongs to the watcher — never touch it"),
    (re.compile(r"\bpkill\b|\bkillall\b|\bfuser\b[^|;&]*\s-[a-zA-Z]*k|\bkill\s+(-\S+\s+)*\d"),
     "process killing is the watcher's job (mathbench_repl.py handles 7777)"),
]

# Bash write-ish constructs aimed at protected files (the Edit/Write rules
# below cover the editing tools; these close the shell-redirection bypass).
_BASH_WRITEISH = re.compile(r"(>|>>|\btee\b|\bcp\b|\bmv\b|\bsed\b[^|;&]*\s-i|\btruncate\b|\bdd\b)")

# Checked ONLY against the target path of Edit/Write/NotebookEdit: these files
# must never be hand-edited. (ACCEPT goes through
# `check_putnam_divergence.py --accept-new`, which the user authorized for
# unattended runs on 2026-06-11 — so Bash is NOT blocked on them.)
_STATIC_DENY_WRITE_TARGET: list[tuple[re.Pattern, str]] = [
    (re.compile(r"divergence_golden\.json"),
     "the golden divergence ledger may only be changed via "
     "check_putnam_divergence.py --accept-new, never edited directly"),
    (re.compile(r"Tests/[^\s]*\.ya?ml"),
     "golden test YAMLs must not be edited"),
]


def _static_deny_reason(tool_name: str, tool_input: dict) -> str | None:
    """Hard-rule check. Returns the reason string when *this* call must be
    denied, else None. Bash rules apply only to Bash (a Read with
    offset=6666 must not be denied); write-target rules apply to the editing
    tools and to write-ish Bash constructs."""
    if tool_name == "Bash":
        cmd = str(tool_input.get("command", ""))
        for pat, reason in _STATIC_DENY_BASH:
            if pat.search(cmd):
                return reason
        if ("divergence_golden.json" in cmd
                and "check_putnam_divergence" not in cmd):
            return ("divergence_golden.json may only be touched via "
                    "check_putnam_divergence.py --accept-new")
        if re.search(r"Tests/[^\s]*\.ya?ml", cmd) and _BASH_WRITEISH.search(cmd):
            return "golden test YAMLs must not be modified"
        return None
    if tool_name in ("Edit", "Write", "NotebookEdit", "MultiEdit"):
        path = str(tool_input.get("file_path", "")
                   or tool_input.get("notebook_path", ""))
        for pat, reason in _STATIC_DENY_WRITE_TARGET:
            if pat.search(path):
                return reason
    return None


def static_pretooluse_hook(log_path: Path):
    """PreToolUse hook enforcing the static red lines. Runs before the
    built-in auto-mode classifier; everything it does not deny is decided by
    the classifier alone."""
    async def _hook(hook_input, tool_use_id, context):
        tool_name = hook_input.get("tool_name", "?")
        tool_input = hook_input.get("tool_input") or {}
        reason = _static_deny_reason(tool_name, tool_input)
        if reason is None:
            return {}
        with open(log_path, "a", encoding="utf-8") as f:
            f.write(f"{datetime.now().isoformat()} DENY  [static-hook] "
                    f"{tool_name} {reason}\n")
        return {"hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": f"Hard rule: {reason}.",
        }}
    return _hook


SEARCH_MISSION = """\
Confirmation-search agent of the MathBench missing-lemma loop. It may:
- read/grep/glob anywhere under the repository;
- run READ-ONLY Bash (grep, rg, find, ls, cat, head, tail, wc, sed -n);
- submit its verdicts via the `mcp__results__submit_verdicts` tool.
It must NOT: modify any repository file, build anything, start/stop any
process or server, or access the network.
"""

PHASE2_MISSION = """\
Import-expansion agent of the MathBench missing-lemma loop, following the
mathbench-import-reconcile skill. It may:
- edit tasks/MathBench_Prover/MathBench_Prover.thy,
  tasks/MathBench_Prover/Base/MathBench_ProverBase.thy and
  tasks/MathBench_Prover/ROOT;
- run `python tools/mathbench_repl.py …` (the dedicated port-7777 REPL),
  `python tools/check_putnam_divergence.py` (including `--accept-new`, which
  the user authorized for this loop provided every decision is recorded),
  `python -m tools.test_mathbench_goals`;
- run `isabelle build … MathBench_ProverBase` (with RPC_Host=127.0.0.1:27180),
  and other read-only isabelle/bash commands;
- append to missing_lemma_loop_state/divergence_decisions.md and submit its
  result via the `mcp__results__submit_result` tool.
It must NOT: touch the port-6666 REPL or kill any process directly, hand-edit
golden YAMLs or tools/divergence_golden.json (golden changes go through
--accept-new only), run git state-changing commands, or edit anything outside
the paths above.
"""
