#!/usr/bin/env python3
"""Repository-level proof hygiene audit.

This script is intentionally conservative: it rejects Lean escape-hatch
declarations in tracked source files and fails if audited headline theorems
depend on axioms outside the allowed classical kernel set.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

from check_lean_placeholders import strip_comments_and_strings, tracked_lean_files


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_PATTERNS = [
    (re.compile(r"^\s*axiom\s+\w"), "axiom declaration"),
    (re.compile(r"^\s*opaque\s+\w"), "opaque declaration"),
    (re.compile(r"^\s*unsafe\s+"), "unsafe declaration"),
    (re.compile(r"\bpartial\s+def\b"), "partial definition"),
    (re.compile(r"@\[\s*implemented_by\s*\]"), "implemented_by escape hatch"),
    (re.compile(r"\bnative_decide\b"), "native_decide proof"),
]
AXIOM_LINE_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")


def static_escape_hatch_audit() -> list[str]:
    failures: list[str] = []
    for path in tracked_lean_files():
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(stripped.splitlines(), start=1):
            for pattern, label in FORBIDDEN_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{line_no}: forbidden {label}")
    return failures


def run_axiom_audit() -> tuple[list[str], str]:
    result = subprocess.run(
        ["lake", "env", "lean", "scripts/AxiomAudit.lean"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode != 0:
        return [f"scripts/AxiomAudit.lean failed with exit code {result.returncode}"], result.stdout

    failures: list[str] = []
    audited = 0
    for line in result.stdout.splitlines():
        match = AXIOM_LINE_RE.match(line.strip())
        if not match:
            continue
        audited += 1
        decl, raw_axioms = match.groups()
        axioms = {part.strip() for part in raw_axioms.split(",") if part.strip()}
        unexpected = sorted(axioms - ALLOWED_AXIOMS)
        if unexpected:
            failures.append(f"{decl}: unexpected axioms {unexpected}")

    if audited == 0:
        failures.append("scripts/AxiomAudit.lean produced no parsable axiom reports")
    return failures, result.stdout


def main() -> int:
    failures = static_escape_hatch_audit()
    axiom_failures, axiom_output = run_axiom_audit()
    failures.extend(axiom_failures)

    if failures:
        print("Repository audit failed:", file=sys.stderr)
        for failure in failures:
            print(failure, file=sys.stderr)
        if axiom_output:
            print("\nLean axiom output:", file=sys.stderr)
            print(axiom_output, file=sys.stderr)
        return 1

    print("Repository audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
