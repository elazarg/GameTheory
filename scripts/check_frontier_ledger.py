#!/usr/bin/env python3
"""Validate the finite-quitting proof frontier and its commit transitions.

The JSON ledger contains the mechanically exhaustive antichain, not every
diagnostic predicate in the repository.  With ``--base`` and ``--head``, this
script also requires every change to production quitting diagnostics to append
an explicit transition naming the affected stable leaf IDs.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from typing import Any


LEDGER = pathlib.Path("docs/uniform-equilibrium/QuittingProofFrontier.json")
PRODUCTION_PREFIX = "UniformEquilibrium/Diagnostics/Quitting/"
ALLOWED_STATUSES = {"open", "eliminated", "merged"}
ALLOWED_KINDS = {
    "census",
    "eliminated",
    "merged",
    "hypothesis_dropped",
    "architectural_nogo",
    "maintenance",
}


def load_bytes(raw: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"{label}: invalid JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label}: top level must be an object")
    return value


def load_worktree() -> dict[str, Any]:
    return load_bytes(LEDGER.read_bytes(), str(LEDGER))


def validate(data: dict[str, Any], label: str) -> list[str]:
    failures: list[str] = []
    if data.get("schema_version") != 1:
        failures.append(f"{label}: schema_version must be 1")

    classes = data.get("obstruction_classes")
    leaves = data.get("formal_leaves")
    transitions = data.get("transitions")
    if not isinstance(classes, list):
        return failures + [f"{label}: obstruction_classes must be a list"]
    if not isinstance(leaves, list):
        return failures + [f"{label}: formal_leaves must be a list"]
    if not isinstance(transitions, list):
        return failures + [f"{label}: transitions must be a list"]

    class_ids = [item.get("id") for item in classes if isinstance(item, dict)]
    if len(class_ids) != len(classes) or len(set(class_ids)) != len(class_ids):
        failures.append(f"{label}: obstruction-class IDs must be present and unique")

    leaf_ids = [item.get("id") for item in leaves if isinstance(item, dict)]
    if len(leaf_ids) != len(leaves) or len(set(leaf_ids)) != len(leaf_ids):
        failures.append(f"{label}: formal-leaf IDs must be present and unique")
    leaf_id_set = set(leaf_ids)
    for leaf in leaves:
        if not isinstance(leaf, dict):
            continue
        leaf_id = leaf.get("id", "<missing>")
        if leaf.get("status") not in ALLOWED_STATUSES:
            failures.append(f"{label}: {leaf_id} has invalid status")
        if leaf.get("obstruction_class") not in set(class_ids):
            failures.append(f"{label}: {leaf_id} has unknown obstruction class")
        for key in ("representative", "source", "producer"):
            if not isinstance(leaf.get(key), str) or not leaf[key].strip():
                failures.append(f"{label}: {leaf_id} needs nonempty {key}")

    open_count = sum(
        isinstance(leaf, dict) and leaf.get("status") == "open" for leaf in leaves
    )
    limit = data.get("open_leaf_limit")
    if not isinstance(limit, int) or limit < 0:
        failures.append(f"{label}: open_leaf_limit must be a nonnegative integer")
    elif open_count > limit:
        failures.append(
            f"{label}: {open_count} open leaves exceed fixed limit {limit}"
        )

    transition_ids: list[str] = []
    for transition in transitions:
        if not isinstance(transition, dict):
            failures.append(f"{label}: every transition must be an object")
            continue
        transition_id = transition.get("id")
        transition_ids.append(transition_id)
        kind = transition.get("kind")
        if kind not in ALLOWED_KINDS:
            failures.append(f"{label}: {transition_id} has invalid kind {kind!r}")
        targets = transition.get("target_ids")
        if not isinstance(targets, list) or not targets:
            failures.append(f"{label}: {transition_id} must name target_ids")
        elif any(target not in leaf_id_set for target in targets):
            failures.append(f"{label}: {transition_id} names an unknown leaf")
        evidence = transition.get("evidence")
        if not isinstance(evidence, list) or not evidence or any(
            not isinstance(path, str) or not path for path in evidence
        ):
            failures.append(f"{label}: {transition_id} needs evidence paths")
        if not isinstance(transition.get("summary"), str) or not transition["summary"].strip():
            failures.append(f"{label}: {transition_id} needs a summary")

    if len(set(transition_ids)) != len(transition_ids):
        failures.append(f"{label}: transition IDs must be unique")
    return failures


def validate_worktree_sources(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    for leaf in data["formal_leaves"]:
        leaf_id = leaf["id"]
        source = pathlib.Path(leaf["source"])
        if not source.is_file():
            failures.append(f"{leaf_id} source does not exist: {source}")
        elif leaf["producer"] not in source.read_text(encoding="utf-8"):
            failures.append(f"{leaf_id} producer is absent from {source}")
    return failures


def git_output(*args: str) -> str:
    return subprocess.run(
        ["git", *args], check=True, text=True, stdout=subprocess.PIPE
    ).stdout


def load_revision(revision: str) -> dict[str, Any] | None:
    result = subprocess.run(
        ["git", "show", f"{revision}:{LEDGER.as_posix()}"],
        text=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        return None
    return load_bytes(result.stdout, f"{revision}:{LEDGER}")


def validate_transition_pair(
    base: str, head: str, old: dict[str, Any] | None, current: dict[str, Any]
) -> list[str]:
    changed = {
        path.strip()
        for path in git_output("diff", "--name-only", base, head).splitlines()
        if path.strip()
    }
    production = {
        path for path in changed
        if path.startswith(PRODUCTION_PREFIX) and path.endswith(".lean")
    }
    if not production:
        return []
    if LEDGER.as_posix() not in changed:
        return [
            "production quitting diagnostics changed without changing the "
            f"frontier ledger: {sorted(production)}"
        ]

    if old is None:
        return []
    failures = validate(old, f"{base}:{LEDGER}")
    old_transitions = old["transitions"]
    new_transitions = current["transitions"]
    if new_transitions[: len(old_transitions)] != old_transitions:
        failures.append("frontier transition history must be append-only")
        return failures
    appended = new_transitions[len(old_transitions):]
    if not appended:
        failures.append("production change must append a frontier transition")
        return failures

    evidence = {
        path for transition in appended for path in transition.get("evidence", [])
    }
    missing = sorted(production - evidence)
    if missing:
        failures.append(
            "new frontier transitions do not cite changed production modules: "
            + ", ".join(missing)
        )

    old_leaves = {leaf["id"]: leaf for leaf in old["formal_leaves"]}
    new_leaves = {leaf["id"]: leaf for leaf in current["formal_leaves"]}
    if set(new_leaves) != set(old_leaves):
        failures.append(
            "stable formal-leaf IDs cannot be added or removed; eliminate or "
            "merge them by changing status"
        )
    old_open = sum(leaf["status"] == "open" for leaf in old_leaves.values())
    new_open = sum(leaf["status"] == "open" for leaf in new_leaves.values())
    if new_open > old_open:
        failures.append(
            f"open formal leaves increased from {old_open} to {new_open}"
        )

    for transition in appended:
        kind = transition["kind"]
        for target in transition["target_ids"]:
            status = new_leaves[target]["status"]
            if kind == "eliminated" and status != "eliminated":
                failures.append(f"{transition['id']}: {target} was not eliminated")
            elif kind == "merged" and status != "merged":
                failures.append(f"{transition['id']}: {target} was not merged")
            elif kind in {"hypothesis_dropped", "architectural_nogo", "maintenance"}:
                if status != old_leaves[target]["status"]:
                    failures.append(
                        f"{transition['id']}: {kind} may not change {target}'s status"
                    )
    return failures


def validate_commit_range(base: str, head: str) -> list[str]:
    """Check every commit, so one ledger edit cannot cover later dispatches."""
    failures: list[str] = []
    commits = [
        commit for commit in
        git_output("rev-list", "--reverse", f"{base}..{head}").splitlines()
        if commit
    ]
    parent = base
    for commit in commits:
        current = load_revision(commit)
        old = load_revision(parent)
        if current is None:
            changed = {
                path.strip()
                for path in git_output("diff", "--name-only", parent, commit).splitlines()
                if path.strip()
            }
            production = sorted(
                path for path in changed
                if path.startswith(PRODUCTION_PREFIX) and path.endswith(".lean")
            )
            if production:
                failures.append(
                    f"{commit}: production diagnostics changed before the "
                    f"frontier ledger existed: {production}"
                )
            parent = commit
            continue
        failures.extend(
            f"{commit}: {failure}"
            for failure in validate(current, f"{commit}:{LEDGER}")
        )
        failures.extend(
            f"{commit}: {failure}"
            for failure in validate_transition_pair(parent, commit, old, current)
        )
        parent = commit
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base")
    parser.add_argument("--head")
    args = parser.parse_args()
    if bool(args.base) != bool(args.head):
        parser.error("--base and --head must be supplied together")

    current = load_worktree()
    failures = validate(current, str(LEDGER))
    failures.extend(validate_worktree_sources(current))
    if args.base:
        failures.extend(validate_commit_range(args.base, args.head))
    if failures:
        print("Proof-frontier ledger check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print("Proof-frontier ledger check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
