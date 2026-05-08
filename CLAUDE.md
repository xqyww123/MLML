# CLAUDE.md

@AGENTS.md

## Rules

### Never Act on Assumptions — ALWAYS Ask

CRITICAL: You MUST NEVER make autonomous decisions under ANY uncertainty. If anything is ambiguous, unclear, or inconsistent — stop and ask me BEFORE acting. Never guess, never silently work around issues, never make judgment calls on my behalf. Be proactive: if something MIGHT be worth clarifying, ask first. It is always better to ask one question too many than to make one wrong assumption. When in doubt, ask. When not in doubt, consider whether you should be.

### Shared Working Directory

You operate in a shared working directory alongside other agents. Never use git stash, git checkout, git reset --hard, or any command that discards or hides uncommitted changes.

### Always Reuse Code — Never Reinvent the Wheel

IMPORTANT: Before writing ANY new logic, search the codebase first. Reuse what exists — even if it means importing across modules or adding a parameter to an existing function. Do NOT copy-paste-and-modify; refactor instead.

### Verify, Don't Assume

If you are not sure whether something works, run it. Write code, run tests, check output — do not claim results you have not observed. If you do not know something, say so and ask. Never fabricate facts, paths, APIs, or behavior.
