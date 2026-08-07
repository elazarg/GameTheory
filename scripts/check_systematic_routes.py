#!/usr/bin/env python3
"""Validate the systematic finite-quitting coordination files.

This is intentionally a lightweight structural check. It validates JSON shape,
enumerated route/role values, referenced module paths, documentation markers,
selected Lean declaration names, conjecture import wiring, and CI invocation.
It does not decide whether a family is mathematically classified correctly or
whether a prose remaining obligation is current; theorem statements and owning
claims remain authoritative for those judgments.
"""

from __future__ import annotations

import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "docs/uniform-equilibrium/systematic-routes.json"
METHOD_PATH = ROOT / "docs/uniform-equilibrium/SystematicApproach.md"
TOOLKIT_PATH = ROOT / "docs/uniform-equilibrium/TOOLKIT.md"
CI_PATH = ROOT / ".github/workflows/ci.yml"
CONJECTURE_PATH = ROOT / "GameTheory/Concepts/Stochastic/QuittingConjecture.lean"

REQUIRED_POSITIVE_ROUTES = {
    "stationary-projective": "stationaryProjective",
    "instant-punishment": "instantPunishment",
    "proper-absorption-path": "properAbsorptionPath",
}
REQUIRED_NEGATIVE_LANE = ("nonexistence", "nonexistence")
REQUIRED_ROLES = {
    "producer",
    "adapter",
    "verifier",
    "compiler",
    "closure",
    "diagnostic",
    "separator",
}
REQUIRED_CLAIM_LEVELS = {
    "semantic-waist",
    "verification",
    "bounded-synthesis",
    "strategy-class-coverage",
    "solved-subclass",
    "diagnostic",
}
POSITIVE_OUTPUT_ROLES = {"producer", "compiler"}
SYSTEMATIC_IMPORT = "import GameTheory.Concepts.Stochastic.QuittingSystematicApproach"
REQUIRED_INTERFACE_NAMES = {
    "QuittingTerminalApproximationFamily",
    "QuittingCertificateProducer",
    "QuittingCertificateAdapter",
    "QuittingPositiveCompiler",
    "QuittingNegativeCompiler",
    "QuittingSystematicSchema",
    "QuittingSystematicResolution",
    "QuittingSemanticResolution",
    "QuittingSystematicDispatcher",
    "QuittingSystematicResolution.semantic",
}


def fail(failures: list[str], message: str) -> None:
    failures.append(message)


def require_mapping(
    failures: list[str], value: Any, location: str
) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(failures, f"{location}: expected an object")
        return {}
    return value


def require_list(
    failures: list[str], value: Any, location: str
) -> list[Any]:
    if not isinstance(value, list):
        fail(failures, f"{location}: expected an array")
        return []
    return value


def require_nonempty_string(
    failures: list[str], value: Any, location: str
) -> str:
    if not isinstance(value, str) or not value.strip():
        fail(failures, f"{location}: expected a nonempty string")
        return ""
    return value.strip()


def module_path(module: str) -> pathlib.Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def require_module(
    failures: list[str], module: Any, location: str
) -> str:
    name = require_nonempty_string(failures, module, location)
    if name:
        path = module_path(name)
        if not path.is_file():
            fail(
                failures,
                f"{location}: module {name} is not tracked at {path.relative_to(ROOT)}",
            )
    return name


def load_manifest(failures: list[str]) -> dict[str, Any]:
    if not MANIFEST_PATH.is_file():
        fail(failures, f"{MANIFEST_PATH.relative_to(ROOT)}: missing route manifest")
        return {}
    try:
        raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(failures, f"{MANIFEST_PATH.relative_to(ROOT)}: {error}")
        return {}
    return require_mapping(failures, raw, str(MANIFEST_PATH.relative_to(ROOT)))


def audit_manifest(manifest: dict[str, Any], failures: list[str]) -> None:
    if manifest.get("schema_version") != 2:
        fail(failures, "systematic-routes.json: schema_version must be 2")

    lean_interface = require_module(
        failures, manifest.get("lean_interface"), "lean_interface"
    )

    project_control = require_mapping(
        failures, manifest.get("project_control"), "project_control"
    )
    for field in ("decision", "method", "spine", "audit"):
        path_text = require_nonempty_string(
            failures, project_control.get(field), f"project_control.{field}"
        )
        if path_text and not (ROOT / path_text).is_file():
            fail(failures, f"project_control.{field}: missing path {path_text}")

    semantic_waist = require_mapping(
        failures, manifest.get("semantic_waist"), "semantic_waist"
    )
    for field in ("predicate", "consumer"):
        require_nonempty_string(
            failures, semantic_waist.get(field), f"semantic_waist.{field}"
        )
    require_module(
        failures,
        semantic_waist.get("interface_module"),
        "semantic_waist.interface_module",
    )
    require_module(
        failures,
        semantic_waist.get("underlying_module"),
        "semantic_waist.underlying_module",
    )

    negative_waist = require_mapping(
        failures,
        manifest.get("negative_semantic_waist"),
        "negative_semantic_waist",
    )
    for field in ("certificate", "exactness"):
        require_nonempty_string(
            failures, negative_waist.get(field), f"negative_semantic_waist.{field}"
        )
    require_module(
        failures,
        negative_waist.get("canonical_module"),
        "negative_semantic_waist.canonical_module",
    )

    schema = require_mapping(
        failures, manifest.get("systematic_schema"), "systematic_schema"
    )
    for field in (
        "schema_type",
        "resolution_type",
        "semantic_resolution_type",
        "dispatcher_type",
        "semantic_function",
        "positive_compiler",
        "negative_compiler",
        "quantifier_order",
    ):
        require_nonempty_string(
            failures, schema.get(field), f"systematic_schema.{field}"
        )

    positive_routes = require_list(
        failures, manifest.get("positive_routes"), "positive_routes"
    )
    seen_routes: dict[str, str] = {}
    for index, raw_route in enumerate(positive_routes):
        route = require_mapping(failures, raw_route, f"positive_routes[{index}]")
        route_id = require_nonempty_string(
            failures, route.get("id"), f"positive_routes[{index}].id"
        )
        constructor = require_nonempty_string(
            failures,
            route.get("lean_constructor"),
            f"positive_routes[{index}].lean_constructor",
        )
        for field in ("purpose", "entry_obligation", "completion_condition"):
            require_nonempty_string(
                failures,
                route.get(field),
                f"positive_routes[{index}].{field}",
            )
        if route_id in seen_routes:
            fail(failures, f"positive_routes: duplicate id {route_id}")
        seen_routes[route_id] = constructor

    if seen_routes != REQUIRED_POSITIVE_ROUTES:
        fail(
            failures,
            "positive_routes must be exactly "
            f"{sorted(REQUIRED_POSITIVE_ROUTES)} with the canonical constructors; "
            f"found {seen_routes}",
        )

    negative_lane = require_mapping(
        failures, manifest.get("negative_lane"), "negative_lane"
    )
    negative_id = require_nonempty_string(
        failures, negative_lane.get("id"), "negative_lane.id"
    )
    negative_constructor = require_nonempty_string(
        failures,
        negative_lane.get("lean_constructor"),
        "negative_lane.lean_constructor",
    )
    for field in ("purpose", "completion_condition"):
        require_nonempty_string(
            failures, negative_lane.get(field), f"negative_lane.{field}"
        )
    if (negative_id, negative_constructor) != REQUIRED_NEGATIVE_LANE:
        fail(
            failures,
            "negative_lane must be the canonical nonexistence lane "
            f"{REQUIRED_NEGATIVE_LANE}",
        )

    roles = set(require_list(failures, manifest.get("roles"), "roles"))
    if roles != REQUIRED_ROLES:
        fail(failures, f"roles must be exactly {sorted(REQUIRED_ROLES)}")

    claim_levels = set(
        require_list(failures, manifest.get("claim_levels"), "claim_levels")
    )
    if claim_levels != REQUIRED_CLAIM_LEVELS:
        fail(
            failures,
            f"claim_levels must be exactly {sorted(REQUIRED_CLAIM_LEVELS)}",
        )

    valid_routes = set(REQUIRED_POSITIVE_ROUTES) | {
        REQUIRED_NEGATIVE_LANE[0],
        "cross-cutting",
    }
    families = require_list(failures, manifest.get("families"), "families")
    seen_family_ids: set[str] = set()
    positive_output_coverage = {
        route_id: False for route_id in REQUIRED_POSITIVE_ROUTES
    }
    negative_separator = False

    for index, raw_family in enumerate(families):
        location = f"families[{index}]"
        family = require_mapping(failures, raw_family, location)
        family_id = require_nonempty_string(
            failures, family.get("id"), f"{location}.id"
        )
        route = require_nonempty_string(
            failures, family.get("route"), f"{location}.route"
        )
        role = require_nonempty_string(
            failures, family.get("role"), f"{location}.role"
        )
        claim_level = require_nonempty_string(
            failures, family.get("claim_level"), f"{location}.claim_level"
        )
        canonical_module = require_module(
            failures,
            family.get("canonical_module"),
            f"{location}.canonical_module",
        )
        require_nonempty_string(
            failures,
            family.get("remaining_obligation"),
            f"{location}.remaining_obligation",
        )

        if family_id in seen_family_ids:
            fail(failures, f"families: duplicate id {family_id}")
        seen_family_ids.add(family_id)

        if route not in valid_routes:
            fail(failures, f"{location}.route: unknown route {route}")
        if role not in REQUIRED_ROLES:
            fail(failures, f"{location}.role: unknown role {role}")
        if claim_level not in REQUIRED_CLAIM_LEVELS:
            fail(failures, f"{location}.claim_level: unknown {claim_level}")
        if not isinstance(family.get("generic_producer"), bool):
            fail(failures, f"{location}.generic_producer: expected a boolean")

        if route in positive_output_coverage and role in POSITIVE_OUTPUT_ROLES:
            positive_output_coverage[route] = True
        if route == REQUIRED_NEGATIVE_LANE[0] and role == "separator":
            negative_separator = True
        if role == "separator" and route != REQUIRED_NEGATIVE_LANE[0]:
            fail(failures, f"{location}: separator must use nonexistence route")
        if family.get("generic_producer") is True and claim_level not in {
            "solved-subclass",
            "strategy-class-coverage",
        }:
            fail(
                failures,
                f"{location}: generic_producer needs solved-subclass or "
                "strategy-class-coverage",
            )
        if canonical_module and not module_path(canonical_module).is_file():
            fail(failures, f"{location}: missing canonical module")

    for route_id, covered in positive_output_coverage.items():
        if not covered:
            fail(failures, f"route {route_id} has no producer or compiler entry")
    if not negative_separator:
        fail(failures, "nonexistence lane has no separator entry")

    if lean_interface:
        lean_path = module_path(lean_interface)
        if lean_path.is_file():
            lean = lean_path.read_text(encoding="utf-8")
            for constructor in REQUIRED_POSITIVE_ROUTES.values():
                if f"| {constructor}" not in lean:
                    fail(failures, f"{lean_path.relative_to(ROOT)}: missing {constructor}")
            for name in REQUIRED_INTERFACE_NAMES:
                if name not in lean:
                    fail(failures, f"{lean_path.relative_to(ROOT)}: missing {name}")

    negative_module = negative_waist.get("canonical_module")
    if isinstance(negative_module, str) and module_path(negative_module).is_file():
        negative_text = module_path(negative_module).read_text(encoding="utf-8")
        for name in (
            "QuittingTerminalGapCertificate",
            "not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap",
        ):
            if name not in negative_text:
                fail(failures, f"{module_path(negative_module).relative_to(ROOT)}: missing {name}")


def audit_documents(manifest: dict[str, Any], failures: list[str]) -> None:
    required_files = (METHOD_PATH, TOOLKIT_PATH, CI_PATH, CONJECTURE_PATH)
    for path in required_files:
        if not path.is_file():
            fail(failures, f"{path.relative_to(ROOT)}: missing required file")
    if any(not path.is_file() for path in required_files):
        return

    method = METHOD_PATH.read_text(encoding="utf-8")
    toolkit = TOOLKIT_PATH.read_text(encoding="utf-8")
    ci = CI_PATH.read_text(encoding="utf-8")
    conjecture = CONJECTURE_PATH.read_text(encoding="utf-8")

    for route in manifest.get("positive_routes", []):
        route_id = route.get("id") if isinstance(route, dict) else None
        if isinstance(route_id, str):
            marker = f"<!-- systematic-route:{route_id} -->"
            if marker not in method:
                fail(failures, f"SystematicApproach.md: missing marker {marker}")

    negative_lane = manifest.get("negative_lane", {})
    if isinstance(negative_lane, dict) and isinstance(negative_lane.get("id"), str):
        marker = f"<!-- systematic-route:{negative_lane['id']} -->"
        if marker not in method:
            fail(failures, f"SystematicApproach.md: missing marker {marker}")

    for family in manifest.get("families", []):
        family_id = family.get("id") if isinstance(family, dict) else None
        if isinstance(family_id, str):
            marker = f"<!-- systematic-family:{family_id} -->"
            if marker not in method:
                fail(failures, f"SystematicApproach.md: missing marker {marker}")

    for required_text in (
        "SystematicApproach.md",
        "systematic-routes.json",
        "QuittingSystematicApproach.lean",
        "QuittingSystematicSchema",
        "QuittingNegativeCompiler",
    ):
        if required_text not in toolkit:
            fail(failures, f"TOOLKIT.md: missing systematic entry {required_text}")

    if ci.count("python3 scripts/check_systematic_routes.py") < 2:
        fail(
            failures,
            ".github/workflows/ci.yml: route audit must run in fast and full jobs",
        )

    if SYSTEMATIC_IMPORT not in conjecture:
        fail(failures, "QuittingConjecture.lean: systematic interface not imported")


def main() -> int:
    failures: list[str] = []
    manifest = load_manifest(failures)
    if manifest:
        audit_manifest(manifest, failures)
        audit_documents(manifest, failures)

    if failures:
        print("Systematic route audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("Systematic route audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
