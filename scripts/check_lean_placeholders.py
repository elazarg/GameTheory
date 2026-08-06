#!/usr/bin/env python3
"""Fail if tracked Lean sources contain unexpected `sorry` or `admit` tokens.

The repository states three open conjectures as `sorry`-carrying declarations
on purpose. They are listed in `INTENTIONAL` below, keyed by path and
declaration name, so that this check stays *green* while still failing on any
additional placeholder appearing anywhere.

The allowlist is checked in both directions. An entry that no longer
corresponds to a placeholder is itself a failure: when a conjecture is
discharged or renamed, its entry must be updated, and a silently stale
allowlist is how a guard stops guarding.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys


TOKEN_RE = re.compile(r"\b(sorry|admit)\b")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|instance|abbrev|example)\s+([^\s({\[:]+)"
)

# (path as posix, declaration name) -> why it is allowed to carry a placeholder.
INTENTIONAL: dict[tuple[str, str], str] = {
    (
        "GameTheory/Concepts/Stochastic/QuittingConjecture.lean",
        "quittingGame_exists_uniformEquilibriumPayoff",
    ): "The finite-quitting uniform-equilibrium conjecture.",
    (
        "GameTheory/Concepts/Stochastic/UniformExistenceConjecture.lean",
        "exists_uniformDeviationCapConstructor",
    ): "The general uniform-equilibrium existence problem, quantitative form.",
    (
        "GameTheory/Concepts/Stochastic/QuittingReducedCapConjecture.lean",
        "quittingGame_hasQuittingTruncatedLedgerCapPackage",
    ): "The reduced finite-quitting conjecture: existence, at every tolerance, "
    "of a punishment-free truncated ledger package. It "
    "implies the finite-quitting conjecture with no gap, by "
    "`quittingGame_exists_uniformEquilibriumPayoff_of_truncatedLedgerCapPackage`.",
}


def enclosing_declaration(lines: list[str], index: int) -> str | None:
    """Name of the declaration containing `lines[index]`, scanning upward."""
    for line in reversed(lines[: index + 1]):
        match = DECL_RE.match(line)
        if match:
            return match.group(1)
    return None


def tracked_lean_files() -> list[pathlib.Path]:
    result = subprocess.run(
        ["git", "ls-files", "*.lean"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [path for line in result.stdout.splitlines() if (path := pathlib.Path(line)).exists()]


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
    seen: set[tuple[str, str]] = set()

    for path in tracked_lean_files():
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        lines = stripped.splitlines()
        for index, line in enumerate(lines):
            if not TOKEN_RE.search(line):
                continue
            line_no = index + 1
            declaration = enclosing_declaration(lines, index)
            key = (path.as_posix(), declaration or "")
            if key in INTENTIONAL:
                seen.add(key)
                continue
            where = declaration or "<no enclosing declaration>"
            failures.append(f"{path}:{line_no}: placeholder token in {where}")

    for key, reason in INTENTIONAL.items():
        if key not in seen:
            failures.append(
                f"{key[0]}: allowlisted declaration {key[1]} no longer carries a "
                f"placeholder ({reason}) -- remove it from INTENTIONAL"
            )

    if failures:
        print("Lean placeholder check failed:", file=sys.stderr)
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1

    print(
        f"Lean placeholder check passed "
        f"({len(INTENTIONAL)} intentional open declarations)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
