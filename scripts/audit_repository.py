#!/usr/bin/env python3
"""Repository-level proof hygiene audit.

This script is intentionally conservative: it rejects Lean escape-hatch
declarations in tracked source files and fails if audited headline theorems
depend on axioms outside the allowed classical kernel set.  One precisely
identified external theorem may be admitted only through the Solan
three-player quitting-game source boundary; its downstream dependency is
checked declaration by declaration.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

from check_lean_placeholders import TOKEN_RE, strip_comments_and_strings, tracked_lean_files


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

SOLAN_SOURCE_PATH = (
    "UniformEquilibrium/Quitting/Classification/ThreePlayer/"
    "SolanSourceStatement.lean"
)
SOLAN_SOURCE_DECL = "solan1999_threePlayerQuitting_terminalTargetBounds"
SOLAN_SOURCE_AXIOM = (
    "GameTheory.solan1999_threePlayerQuitting_terminalTargetBounds"
)

# External mathematical inputs are allowed only at the exact declaration
# sites listed here.  This is deliberately a path-and-name allowlist rather
# than a global relaxation of the axiom ban.
EXTERNAL_SOURCE_AXIOMS: dict[tuple[str, str], str] = {
    (SOLAN_SOURCE_PATH, SOLAN_SOURCE_DECL): (
        "Solan 1999, Three-Player Absorbing Games, exact quitting specialization"
    ),
}

# Only these audited declarations may transitively depend on the external
# source axiom.  Their conditional counterparts are audited under the ordinary
# classical-kernel allowance and must remain source-independent.
ALLOWED_AXIOMS_BY_DECL: dict[str, set[str]] = {
    "GameTheory.threePlayerQuittingGame_exists_terminalNash_all_errors": {
        SOLAN_SOURCE_AXIOM
    },
    "GameTheory.quittingGame_exists_uniformEquilibriumPayoff_threePlayer": {
        SOLAN_SOURCE_AXIOM
    },
}
EXPECTED_AXIOMS_BY_DECL = ALLOWED_AXIOMS_BY_DECL

FORBIDDEN_PATTERNS = [
    (re.compile(r"^\s*axiom\s+\w"), "axiom declaration"),
    (re.compile(r"^\s*opaque\s+\w"), "opaque declaration"),
    (re.compile(r"^\s*unsafe\s+"), "unsafe declaration"),
    (re.compile(r"\bpartial\s+def\b"), "partial definition"),
    (re.compile(r"@\[\s*implemented_by\s*\]"), "implemented_by escape hatch"),
    (re.compile(r"\bnative_decide\b"), "native_decide proof"),
]
AXIOM_DECL_RE = re.compile(r"^\s*axiom\s+([^\s({\[]+)")
AXIOM_REPORT_RE = re.compile(
    r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL
)
NO_AXIOM_REPORT_RE = re.compile(
    r"'([^']+)' does not depend on any axioms"
)
# `scripts/AxiomAudit.lean` deliberately imports one theorem module from the
# fixed-point submodule which is not in the default root build.  Build that
# precise standalone module before invoking Lean on the audit scripts, so the
# audit is self-contained both on pull requests and on push CI.
AXIOM_AUDIT_PREBUILD_TARGETS = ["FixedPointTheorems.kakutani"]
DEFAULT_ROOTS = {
    "GameTheory",
    "UniformEquilibrium",
    "Math",
    "Semantics",
    "GameTheoryTest",
    "GameTheoryExamples",
}
STANDALONE_LEAN_MODULES = {
    "lakefile",
    "scripts.AxiomAudit",
    "scripts.ThreePlayerSolanAxiomAudit",
}
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
    f"UniformEquilibrium.Quitting.Examples.BlockPair.{name}"
    for name in (
        "K11System",
        "K11LocalInterval",
        "K11LocalValue",
        "K11DyadicData",
        "K11DyadicPhaseGroupZeroTwo",
        "K11DyadicPhaseGroupThreeFive",
        "K11DyadicPhaseGroupSixEight",
        "K11DyadicPhaseNine",
        "K11DyadicPhaseTenRootZero",
        "K11DyadicPhaseTenRootOne",
        "PredecessorCharts",
        "PredecessorComposition",
        "QuadraticRootSelection",
    )
}
STANDALONE_LEAN_MODULES |= BLOCK_PAIR_K11_ISLAND
RAW_SEMANTIC_MODULES = {"GameTheory.Core.GameForm"}
ROOT_AGGREGATORS = {
    "GameTheory",
    "UniformEquilibrium",
}


def module_name_of(path: pathlib.Path) -> str:
    return ".".join(path.with_suffix("").parts)


def static_escape_hatch_audit() -> tuple[list[str], list[str]]:
    """Forbidden constructs, split into hard failures and accepted exceptions.

    The `BlockPairK11` island is exempt *only* because it is unreachable from
    the default targets, so its `Lean.ofReduceBool` axiom cannot reach any
    landed theorem.  The Solan source boundary is exempt only for one exact
    path-and-declaration pair, and downstream use is checked separately by the
    Lean axiom audit.
    """
    failures: list[str] = []
    notices: list[str] = []
    seen_external: set[tuple[str, str]] = set()

    for path in tracked_lean_files():
        exempt_island = module_name_of(path) in BLOCK_PAIR_K11_ISLAND
        stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(stripped.splitlines(), start=1):
            for pattern, label in FORBIDDEN_PATTERNS:
                if not pattern.search(line):
                    continue

                if label == "axiom declaration":
                    match = AXIOM_DECL_RE.match(line)
                    key = (path.as_posix(), match.group(1) if match else "")
                    if key in EXTERNAL_SOURCE_AXIOMS:
                        seen_external.add(key)
                        notices.append(
                            f"{path}:{line_no}: accepted external source axiom "
                            f"{key[1]} ({EXTERNAL_SOURCE_AXIOMS[key]})"
                        )
                        continue

                bucket = notices if exempt_island else failures
                bucket.append(f"{path}:{line_no}: forbidden {label}")

    for key, reason in EXTERNAL_SOURCE_AXIOMS.items():
        if key not in seen_external:
            failures.append(
                f"{key[0]}: allowlisted external source declaration {key[1]} "
                f"was not found ({reason})"
            )

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


def parse_axiom_reports(output: str) -> list[tuple[str, set[str]]]:
    """Parse Lean `#print axioms` output, including pretty-printed line wraps."""
    reports: list[tuple[str, set[str]]] = []
    seen: set[str] = set()

    for match in AXIOM_REPORT_RE.finditer(output):
        decl, raw_axioms = match.groups()
        axioms = {
            part.strip()
            for part in raw_axioms.split(",")
            if part.strip()
        }
        reports.append((decl, axioms))
        seen.add(decl)

    for match in NO_AXIOM_REPORT_RE.finditer(output):
        decl = match.group(1)
        if decl not in seen:
            reports.append((decl, set()))

    return reports


def run_axiom_audit() -> tuple[list[str], str]:
    audit_scripts = [
        "scripts/AxiomAudit.lean",
        "scripts/ThreePlayerSolanAxiomAudit.lean",
    ]
    outputs: list[str] = []
    failures: list[str] = []

    prebuild = subprocess.run(
        ["lake", "build", *AXIOM_AUDIT_PREBUILD_TARGETS],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    outputs.append(prebuild.stdout)
    if prebuild.returncode != 0:
        failures.append(
            "axiom-audit dependency prebuild failed with exit code "
            f"{prebuild.returncode}"
        )
        return failures, "\n".join(outputs)

    for script in audit_scripts:
        result = subprocess.run(
            ["lake", "env", "lean", script],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        outputs.append(result.stdout)
        if result.returncode != 0:
            failures.append(f"{script} failed with exit code {result.returncode}")

    combined_output = "\n".join(outputs)
    if failures:
        return failures, combined_output

    reports = parse_axiom_reports(combined_output)
    seen_expected: set[str] = set()
    for decl, axioms in reports:
        allowed = ALLOWED_AXIOMS | ALLOWED_AXIOMS_BY_DECL.get(decl, set())
        unexpected = sorted(axioms - allowed)
        if unexpected:
            failures.append(f"{decl}: unexpected axioms {unexpected}")

        if decl in EXPECTED_AXIOMS_BY_DECL:
            seen_expected.add(decl)
            missing = sorted(EXPECTED_AXIOMS_BY_DECL[decl] - axioms)
            if missing:
                failures.append(f"{decl}: missing expected source axioms {missing}")

    if not reports:
        failures.append("Lean axiom audits produced no parsable axiom reports")

    for decl in EXPECTED_AXIOMS_BY_DECL:
        if decl not in seen_expected:
            failures.append(
                f"{decl}: no parsable axiom report; external-source dependency "
                "boundary was not checked"
            )

    return failures, combined_output


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
    """Modules with a live `sorry`/`admit`, discovered rather than hard-coded."""
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
    """Make the repository's `sorryAx` containment argument build-checkable."""
    failures: list[str] = []

    importers: dict[str, list[str]] = {mod: [] for mod in tracked_modules}
    for mod, deps in imports.items():
        for dep in deps:
            if dep in importers:
                importers[dep].append(mod)

    for root_aggregator in sorted(ROOT_AGGREGATORS):
        if root_aggregator not in tracked_modules:
            failures.append(f"root aggregator module {root_aggregator} is not tracked")
            continue
        root_path = tracked_modules[root_aggregator]
        for line_no in root_aggregator_non_import_lines(root_path):
            failures.append(
                f"{root_path}:{line_no}: root aggregator must be a pure import "
                f"list but has non-import content here"
            )

    sorry_modules = sorry_carrying_modules(tracked_modules)
    for mod in sorted(sorry_modules):
        allowed = ROOT_AGGREGATORS | (sorry_modules - {mod})
        for importer in sorted(importers.get(mod, [])):
            if importer not in allowed:
                failures.append(
                    f"{tracked_modules[mod]}: sorry-carrying module is imported "
                    f"by {importer}, outside the root aggregators and other "
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
    failures.extend(
        f"{tracked_modules[mod]}: tracked Lean module is not reachable from default targets"
        for mod in orphaned
    )
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
        print("Accepted narrowly scoped proof-boundary declarations:")
        for notice in escape_hatch_notices:
            print(f"  {notice}")
    print("Repository audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
