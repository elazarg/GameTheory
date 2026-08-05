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

from check_lean_placeholders import TOKEN_RE, strip_comments_and_strings, tracked_lean_files


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
# The `BlockPairK11` research island: a self-contained, mutually-importing
# cluster (see docs/uniform-equilibrium/audits/2026-08-04-QuittingTreeCensus.md
# and .../2026-08-04-ModelFaithfulness.md) whose `native_decide`/`opaque`
# numeric certificates the static escape-hatch audit above forbids. It is
# deliberately unreachable from the default targets so its
# `Lean.ofReduceBool` axiom cannot reach the quitting/uniform-equilibrium
# chain. Wiring it into `GameTheory.lean` would make the escape-hatch audit
# fail for a different reason, so it is allowlisted here instead of left to
# show up as orphan noise that could hide a real orphan.
BLOCK_PAIR_K11_ISLAND = {
    f"GameTheory.Concepts.Stochastic.{name}"
    for name in (
        "BlockPairK11System",
        "BlockPairK11LocalInterval",
        "BlockPairK11LocalValue",
        "BlockPairK11DyadicData",
        "BlockPairK11DyadicPhaseGroupZeroTwo",
        "BlockPairK11DyadicPhaseGroupThreeFive",
        "BlockPairK11DyadicPhaseGroupSixEight",
        "BlockPairK11DyadicPhaseNine",
        "BlockPairK11DyadicPhaseTenRootZero",
        "BlockPairK11DyadicPhaseTenRootOne",
        "BlockPairPredecessorCharts",
        "BlockPairPredecessorComposition",
        "BlockPairQuadraticRootSelection",
    )
}
STANDALONE_LEAN_MODULES |= BLOCK_PAIR_K11_ISLAND
RAW_SEMANTIC_MODULES = {"GameTheory.Core.GameForm"}
ROOT_AGGREGATOR = "GameTheory"


def module_name_of(path: pathlib.Path) -> str:
    return ".".join(path.with_suffix("").parts)


def static_escape_hatch_audit() -> tuple[list[str], list[str]]:
    """Forbidden constructs, split into hard failures and accepted exceptions.

    The `BlockPairK11` island is exempt *only* because it is unreachable from
    the default targets, so its `Lean.ofReduceBool` axiom cannot reach any
    landed theorem.  That containment is not assumed here: it is checked by
    `island_containment_audit`, and if it ever breaks these become failures
    again.  Reporting them as notices rather than failures is what lets the
    audit exit zero, so a genuinely new escape hatch fails loudly instead of
    hiding behind a permanently red run.
    """
    failures: list[str] = []
    notices: list[str] = []
    for path in tracked_lean_files():
        exempt = module_name_of(path) in BLOCK_PAIR_K11_ISLAND
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(stripped.splitlines(), start=1):
            for pattern, label in FORBIDDEN_PATTERNS:
                if pattern.search(line):
                    bucket = notices if exempt else failures
                    bucket.append(f"{path}:{line_no}: forbidden {label}")
    return failures, notices


def island_containment_audit(
    tracked_modules: dict[str, pathlib.Path], imports: dict[str, list[str]]
) -> list[str]:
    """The island's escape-hatch exemption is void if anything imports it."""
    failures: list[str] = []
    for mod, deps in imports.items():
        if mod in BLOCK_PAIR_K11_ISLAND or mod not in tracked_modules:
            continue
        for dep in deps:
            if dep in BLOCK_PAIR_K11_ISLAND:
                failures.append(
                    f"{tracked_modules[mod]}: imports quarantined island module {dep}; "
                    "its native_decide/opaque certificates would reach landed theorems"
                )
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


def sorry_carrying_modules(tracked_modules: dict[str, pathlib.Path]) -> set[str]:
    """Modules with a live `sorry`/`admit`, discovered by scanning rather than
    hard-coded, so this stays correct if the set of open conjectures changes."""
    modules: set[str] = set()
    for mod, path in tracked_modules.items():
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        if TOKEN_RE.search(stripped):
            modules.add(mod)
    return modules


def root_aggregator_non_import_lines(path: pathlib.Path) -> list[int]:
    """Line numbers in `path` that are neither blank nor an `import` line."""
    stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    offending: list[int] = []
    for line_no, line in enumerate(stripped.splitlines(), start=1):
        text = line.strip()
        if not text or text.startswith("import "):
            continue
        offending.append(line_no)
    return offending


def leaf_invariant_audit(
    tracked_modules: dict[str, pathlib.Path], imports: dict[str, list[str]]
) -> list[str]:
    """Make the repository's soundness argument build-checkable.

    No landed theorem can transitively depend on `sorryAx` only if (a) every
    `sorry`-carrying module is imported by nothing but the root aggregator and
    the other `sorry`-carrying module, and (b) the root aggregator itself
    declares nothing -- otherwise a declaration added directly to the root
    could depend on `sorryAx` while (a) still held.
    """
    failures: list[str] = []

    importers: dict[str, list[str]] = {mod: [] for mod in tracked_modules}
    for mod, deps in imports.items():
        for dep in deps:
            if dep in importers:
                importers[dep].append(mod)

    if ROOT_AGGREGATOR not in tracked_modules:
        failures.append(f"root aggregator module {ROOT_AGGREGATOR} is not tracked")
    else:
        root_path = tracked_modules[ROOT_AGGREGATOR]
        for line_no in root_aggregator_non_import_lines(root_path):
            failures.append(
                f"{root_path}:{line_no}: root aggregator must be a pure import "
                f"list but has non-import content here"
            )

    sorry_modules = sorry_carrying_modules(tracked_modules)
    for mod in sorted(sorry_modules):
        allowed = {ROOT_AGGREGATOR} | (sorry_modules - {mod})
        for importer in sorted(importers.get(mod, [])):
            if importer not in allowed:
                failures.append(
                    f"{tracked_modules[mod]}: sorry-carrying module is imported "
                    f"by {importer}, outside {{{ROOT_AGGREGATOR}}} ∪ other "
                    f"sorry-carrying modules"
                )

    return failures


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
    failures, escape_hatch_notices = static_escape_hatch_audit()
    failures.extend(semantic_layer_audit(tracked_modules, imports))
    failures.extend(import_reachability_audit(tracked_modules, imports))
    failures.extend(leaf_invariant_audit(tracked_modules, imports))
    failures.extend(island_containment_audit(tracked_modules, imports))
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

    if escape_hatch_notices:
        print("Accepted escape hatches in the quarantined island "
              "(contained; not reachable from default targets):")
        for notice in escape_hatch_notices:
            print(f"  {notice}")
    print("Repository audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
