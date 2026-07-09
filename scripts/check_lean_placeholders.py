#!/usr/bin/env python3
"""Fail if tracked Lean sources contain executable `sorry` or `admit` tokens."""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys


TOKEN_RE = re.compile(r"\b(sorry|admit)\b")


def tracked_lean_files() -> list[pathlib.Path]:
    result = subprocess.run(
        ["git", "ls-files", "*.lean"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [pathlib.Path(line) for line in result.stdout.splitlines() if line]


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False

    while i < len(text):
        c = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if in_line_comment:
            if c == "\n":
                in_line_comment = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if c == "/" and nxt == "-":
                block_depth += 1
                extra = 1 if i + 2 < len(text) and text[i + 2] in {"!", "-"} else 0
                out.extend(" " * (2 + extra))
                i += 2 + extra
            elif c == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue

        if in_string:
            if c == "\\":
                out.extend("  " if nxt else " ")
                i += 2 if nxt else 1
            else:
                out.append("\n" if c == "\n" else " ")
                if c == '"':
                    in_string = False
                i += 1
            continue

        if in_char:
            if c == "\\":
                out.extend("  " if nxt else " ")
                i += 2 if nxt else 1
            else:
                out.append("\n" if c == "\n" else " ")
                if c == "'":
                    in_char = False
                i += 1
            continue

        if c == "-" and nxt == "-":
            in_line_comment = True
            out.extend("  ")
            i += 2
        elif c == "/" and nxt == "-":
            block_depth = 1
            extra = 1 if i + 2 < len(text) and text[i + 2] in {"!", "-"} else 0
            out.extend(" " * (2 + extra))
            i += 2 + extra
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif c == "'":
            in_char = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1

    return "".join(out)


def main() -> int:
    failures: list[str] = []
    for path in tracked_lean_files():
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(stripped.splitlines(), start=1):
            if TOKEN_RE.search(line):
                failures.append(f"{path}:{line_no}: placeholder token")

    if failures:
        print("Lean placeholder check failed:", file=sys.stderr)
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1

    print("Lean placeholder check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
