#!/usr/bin/env python3
"""Delete every active `nitpick` command (with its optional `[...]` options) from AFP theories.

Active means outside comments `(* *)`, cartouches, strings, alt strings and verbatim `{* *}`.
Only the command text goes: `lemma "P" nitpick [card = 2] oops` becomes `lemma "P"  oops`.
A changed file is written back with LF line endings (it is read with universal newlines).

Usage: strip_nitpick.py <thys dir>   -- rewrites the theories in place, prints each changed path.
"""

import re
import sys
from pathlib import Path

_WORD = re.compile(r"(?<![A-Za-z0-9_'.])nitpick(?![A-Za-z0-9_'.])")
_OPEN, _CLOSE = "\\<open>", "\\<close>"


def _skip_bracket(text: str, i: int) -> int:
    """`text[i]` is `[`; return the index just past its matching `]`."""
    depth = 0
    while i < len(text):
        c = text[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced [ after nitpick")


def strip(text: str) -> str:
    out = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):                      # nested comment
            depth, j = 0, i
            while j < n:
                if text.startswith("(*", j):
                    depth += 1; j += 2
                elif text.startswith("*)", j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(text[i:j]); i = j
        elif text.startswith(_OPEN, i):                   # nested cartouche
            depth, j = 0, i
            while j < n:
                if text.startswith(_OPEN, j):
                    depth += 1; j += len(_OPEN)
                elif text.startswith(_CLOSE, j):
                    depth -= 1; j += len(_CLOSE)
                    if depth == 0:
                        break
                else:
                    j += 1
            out.append(text[i:j]); i = j
        elif text[i] in "\"`":                            # string, alt string
            q, j = text[i], i + 1
            while j < n and text[j] != q:
                j += 2 if text[j] == "\\" and not text.startswith("\\<", j) else 1
            out.append(text[i:j + 1]); i = j + 1
        elif text.startswith("{*", i):                    # verbatim
            j = text.find("*}", i + 2)
            j = n if j < 0 else j + 2
            out.append(text[i:j]); i = j
        else:
            m = _WORD.match(text, i)                      # the lookbehind sees text[:i]
            if m:
                k = m.end()
                while k < n and text[k] in " \t":
                    k += 1
                i = _skip_bracket(text, k) if k < n and text[k] == "[" else m.end()
            else:
                out.append(text[i]); i += 1
    return "".join(out)


def main(thys: Path) -> None:
    for p in sorted(thys.rglob("*.thy")):
        if p.name.endswith(".unicode.thy"):
            continue
        text = p.read_text(encoding="utf-8", errors="surrogateescape")
        new = strip(text)
        if new != text:
            p.write_text(new, encoding="utf-8", errors="surrogateescape", newline="\n")
            print(p.relative_to(thys))


if __name__ == "__main__":
    main(Path(sys.argv[1]))
