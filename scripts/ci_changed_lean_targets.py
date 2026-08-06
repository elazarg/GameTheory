#!/usr/bin/env python3
"""Choose a fast, dependency-aware Lean build scope for a pull request.

Changed library modules are passed to Lake as ``+Module.Name`` targets, which
builds each module and its imports. Changes to build configuration, standalone
Lean scripts, deleted modules, or renamed modules request a full build because
their impact cannot be localized safely.
"""

from __future__ import annotations

import argparse
import subprocess
from dataclasses import dataclass
from pathlib import PurePosixPath


BUILD_CONFIGURATION = {
    ".gitmodules",
    "lake-manifest.json",
    "lakefile.lean",
    "lean-toolchain",
    "fixed-point-theorems-lean4",
}

LIBRARY_ROOTS = {
    "GameTheory",
    "GameTheoryExamples",
    "GameTheoryTest",
    "Math",
    "Semantics",
}


@dataclass(frozen=True)
class BuildPlan:
    mode: str
    targets: tuple[str, ...] = ()


def changed_entries(base: str, head: str) -> list[tuple[str, tuple[str, ...]]]:
    output = subprocess.run(
        [
            "git",
            "diff",
            "--name-status",
            "--find-renames",
            base,
            head,
        ],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout

    entries: list[tuple[str, tuple[str, ...]]] = []
    for line in output.splitlines():
        fields = line.split("\t")
        status = fields[0]
        paths = tuple(path.replace("\\", "/") for path in fields[1:])
        entries.append((status, paths))
    return entries


def is_build_configuration(path: str) -> bool:
    return path in BUILD_CONFIGURATION or path.startswith(
        "fixed-point-theorems-lean4/"
    )


def module_target(path: str) -> str | None:
    source = PurePosixPath(path)
    if source.suffix != ".lean":
        return None

    parts = source.with_suffix("").parts
    if not parts or parts[0] not in LIBRARY_ROOTS:
        return None
    return "+" + ".".join(parts)


def build_plan(base: str, head: str) -> BuildPlan:
    targets: set[str] = set()
    for status, paths in changed_entries(base, head):
        if any(is_build_configuration(path) for path in paths):
            return BuildPlan("full")

        if status.startswith(("D", "R")) and any(
            path.endswith(".lean") for path in paths
        ):
            return BuildPlan("full")

        for path in paths:
            if not path.endswith(".lean"):
                continue
            target = module_target(path)
            if target is None:
                # Standalone Lean scripts and unusual source roots need the
                # complete environment rather than an unsafe guessed target.
                return BuildPlan("full")
            targets.add(target)

    if not targets:
        return BuildPlan("none")
    return BuildPlan("focused", tuple(sorted(targets)))


def main() -> None:
    parser = argparse.ArgumentParser()
    output = parser.add_mutually_exclusive_group(required=True)
    output.add_argument("--mode", action="store_true")
    output.add_argument("--targets", action="store_true")
    parser.add_argument("base")
    parser.add_argument("head")
    args = parser.parse_args()

    plan = build_plan(args.base, args.head)
    if args.mode:
        print(plan.mode)
    elif plan.mode == "focused":
        print(*plan.targets, sep="\n")


if __name__ == "__main__":
    main()
