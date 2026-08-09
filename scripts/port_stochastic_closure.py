#!/usr/bin/env python3
"""Port the local stochastic-game dependency closure from a source commit.

Only ``GameTheory.*`` and ``Math.*`` imports are followed.  Source contents are
read through ``git show`` at the pinned commit, and an existing target module
is treated as a boundary: it is never overwritten and is not copied again.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


DEFAULT_ROOTS = [
    "GameTheory.Concepts.Stochastic",
    "GameTheory.Concepts.Stochastic.Core.StageGame",
    "GameTheory.Concepts.Stochastic.Classes.Absorbing",
    "GameTheory.Concepts.Stochastic.Strategy.Potential.Adaptive",
    "GameTheory.Concepts.Stochastic.Core.Basic",
    "GameTheory.Concepts.Stochastic.Equilibrium.Uniform",
    "GameTheory.Concepts.Stochastic.Equilibrium.Uniform.PayoffExistenceClosure",
    "GameTheory.Concepts.Stochastic.Equilibrium.Uniform.AsymptoticPayoffEquivalence",
    "GameTheory.Concepts.Stochastic.Equilibrium.Uniform.ExpectedPotentialShaping",
    "GameTheory.Concepts.Stochastic.Models.Quitting.Asymptotic",
    "GameTheory.Concepts.Stochastic.Transform.ActionLegality.BehaviorTransfer",
    "GameTheory.Concepts.Stochastic.Equilibrium.Discounted",
    "GameTheory.Concepts.Stochastic.Models.Quitting.RootPerturbation",
    "GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches",
    "GameTheory.Concepts.Stochastic.Models.Quitting.Game",
    "GameTheory.Concepts.Stochastic.Models.Quitting.RootContinuation",
    "GameTheory.Concepts.Stochastic.Models.Quitting.PunishmentLevel",
    "GameTheory.Concepts.Stochastic.Classes.TransitionIndependent",
    "GameTheory.Concepts.Stochastic.Strategy.Controller.MemoryController",
    "GameTheory.Concepts.Stochastic.Transform.Payoff.AffinePayoff",
    "GameTheory.Concepts.Stochastic.ZeroSum.DiscountedShapleyAlgebraic",
    "GameTheory.Concepts.Stochastic.Equilibrium.Discounted.Fink",
    "GameTheory.Concepts.Stochastic.ZeroSum.Basic",
]

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)", re.MULTILINE)
LOCAL_PREFIXES = ("GameTheory.", "Math.")


def run_git(source_repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(source_repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout


def module_path(module: str) -> Path:
    return Path(*module.split(".")) .with_suffix(".lean")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-repo", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--target-repo", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--root", action="append", dest="roots")
    args = parser.parse_args()

    source_repo = args.source_repo.resolve()
    target_repo = args.target_repo.resolve()
    roots = args.roots or DEFAULT_ROOTS

    source_paths = {
        Path(line.strip())
        for line in run_git(
            source_repo, "ls-tree", "-r", "--name-only", args.source_commit, "--"
        ).splitlines()
        if line.strip().endswith(".lean")
    }
    source_modules = {
        str(path.with_suffix("")).replace("\\", ".").replace("/", "."): path
        for path in source_paths
        if path.as_posix().startswith(("GameTheory/", "Math/"))
    }

    def source_text(module: str) -> str:
        path = source_modules[module]
        return run_git(source_repo, "show", f"{args.source_commit}:{path.as_posix()}")

    def target_path(module: str) -> Path:
        return target_repo / module_path(module)

    queue = list(dict.fromkeys(roots))
    seen: set[str] = set()
    copied: list[str] = []
    existing: list[str] = []
    missing_source: list[str] = []
    unresolved: list[tuple[str, str]] = []
    unresolved_target: list[tuple[str, str]] = []
    imports: dict[str, list[str]] = {}

    while queue:
        module = queue.pop(0)
        if module in seen:
            continue
        seen.add(module)
        if module not in source_modules:
            missing_source.append(module)
            continue

        text = source_text(module)
        local_imports = [
            name for name in IMPORT_RE.findall(text)
            if name.startswith(LOCAL_PREFIXES)
        ]
        imports[module] = list(dict.fromkeys(local_imports))
        for imported in imports[module]:
            if imported not in source_modules:
                unresolved.append((module, imported))
            elif imported not in seen:
                queue.append(imported)

        destination = target_path(module)
        if destination.exists():
            existing.append(module)
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8", newline="")
        copied.append(module)

    boundary = sorted(set(existing))
    copied.sort()
    unresolved_target = [
        (owner, imported)
        for owner, names in imports.items()
        for imported in names
        if imported in source_modules and not target_path(imported).exists()
    ]
    report_lines = [
        f"source_repo: {source_repo}",
        f"source_commit: {args.source_commit}",
        f"target_repo: {target_repo}",
        f"roots: {len(roots)}",
        f"closure_modules: {len(seen)}",
        f"copied_modules: {len(copied)}",
        f"existing_boundary_modules: {len(boundary)}",
        f"missing_source_modules: {len(missing_source)}",
        f"unresolved_source_imports: {len(unresolved)}",
        f"unresolved_target_imports: {len(unresolved_target)}",
        "",
        "Copied modules:",
        *[f"- {module}" for module in copied],
        "",
        "Existing same-path boundary modules (not copied):",
        *[f"- {module}" for module in boundary],
        "",
        "Missing source modules:",
        *[f"- {module}" for module in sorted(set(missing_source))],
        "",
        "Unresolved local imports in source:",
        *[f"- {owner} -> {imported}" for owner, imported in sorted(set(unresolved))],
        "",
        "Unresolved local imports after copy:",
        *[f"- {owner} -> {imported}" for owner, imported in sorted(set(unresolved_target))],
    ]
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text("\n".join(report_lines) + "\n", encoding="utf-8", newline="")
    print("closure_modules", len(seen))
    print("copied_modules", len(copied))
    print("existing_boundary_modules", len(boundary))
    print("missing_source_modules", len(set(missing_source)))
    print("unresolved_source_imports", len(set(unresolved)))
    print("unresolved_target_imports", len(set(unresolved_target)))


if __name__ == "__main__":
    main()
