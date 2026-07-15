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
DEFAULT_ROOTS = {
    "GameTheory",
    "Math",
    "Semantics",
    "GameTheoryTest",
    "GameTheoryExamples",
}
STANDALONE_LEAN_MODULES = {"lakefile", "scripts.AxiomAudit"}
RAW_SEMANTIC_MODULES = {"GameTheory.Core.GameForm"}


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


def module_name(path: pathlib.Path) -> str:
    return ".".join(path.with_suffix("").parts)


def module_imports(path: pathlib.Path) -> list[str]:
    deps: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("import "):
            parts = line.split()
            if len(parts) >= 2:
                deps.append(parts[1])
    return deps


def tracked_import_graph() -> tuple[dict[str, pathlib.Path], dict[str, list[str]]]:
    tracked_modules = {module_name(path): path for path in tracked_lean_files()}
    imports = {mod: module_imports(path) for mod, path in tracked_modules.items()}
    return tracked_modules, imports


def semantic_layer_audit(
    tracked_modules: dict[str, pathlib.Path], imports: dict[str, list[str]]
) -> list[str]:
    """Keep raw/core semantics independent of downstream game-theory layers."""
    failures: list[str] = []
    for mod, path in tracked_modules.items():
        if not mod.startswith("GameTheory.Core.") and mod not in RAW_SEMANTIC_MODULES:
            continue

        deps = imports[mod]
        for dep in deps:
            allowed = (
                dep == "GameTheory.Basic"
                or dep.startswith("GameTheory.Core.")
                or dep == "Math"
                or dep.startswith("Math.")
                or dep.startswith("Mathlib")
            )
            if not allowed:
                failures.append(
                    f"{path}: core module imports downstream/non-core module {dep}"
                )

        if mod in RAW_SEMANTIC_MODULES and "GameTheory.Core.KernelGame" in deps:
            failures.append(
                f"{path}: raw semantic module imports utility-bearing KernelGame"
            )

    return failures


def import_reachability_audit(
    tracked_modules: dict[str, pathlib.Path], imports: dict[str, list[str]]
) -> list[str]:
    missing_roots = sorted(root for root in DEFAULT_ROOTS if root not in tracked_modules)
    failures = [f"default target root {root}.lean is not tracked" for root in missing_roots]

    reachable: set[str] = set()
    stack = list(DEFAULT_ROOTS)
    while stack:
        mod = stack.pop()
        if mod in reachable:
            continue
        reachable.add(mod)
        stack.extend(dep for dep in imports.get(mod, []) if dep in tracked_modules)

    orphaned = sorted(
        mod for mod in tracked_modules
        if mod not in reachable and mod not in STANDALONE_LEAN_MODULES
    )
    failures.extend(f"{tracked_modules[mod]}: tracked Lean module is not reachable from default targets"
                    for mod in orphaned)
    return failures


def main() -> int:
    tracked_modules, imports = tracked_import_graph()
    failures = static_escape_hatch_audit()
    failures.extend(semantic_layer_audit(tracked_modules, imports))
    failures.extend(import_reachability_audit(tracked_modules, imports))
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
