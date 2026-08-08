"""Proof-status-aware reports for exact repairs and finite filters."""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from typing import Any, Mapping
import json

from .model import (
    RationalQuittingGame,
    fraction_text,
    parse_fraction,
)
from .profiles import (
    evaluate_cutoff_one,
    evaluate_cyclic_word,
    evaluate_stationary,
)
from .search import LadderResult, RepairFinding, RungTrace, SearchConfig

REPORT_SCHEMA = "quitting-repair-report/v1"


def canonical_json(data: Any) -> str:
    return json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def table_fingerprint(game: RationalQuittingGame) -> str:
    return "sha256:" + sha256(canonical_json(game.to_dict()).encode("utf-8")).hexdigest()


def trace_dict(trace: RungTrace) -> dict[str, Any]:
    return {
        "rung": trace.rung,
        "tested": trace.tested,
        "exhausted": trace.exhausted,
        "best_regret": (
            fraction_text(trace.best_regret) if trace.best_regret is not None else None
        ),
        "note": trace.note,
    }


def _lean_checker_for(kind: str) -> dict[str, str]:
    if kind == "cutoff_one":
        return {
            "certificate_type": "GameTheory.QuittingCutoffOneRepairCertificate",
            "conclusion": "GameTheory.QuittingCutoffOneRepairCertificate.isUniformEquilibriumPayoff",
        }
    if kind in {
        "stationary_full_rate",
        "quitter_subset",
        "quitter_pair",
    }:
        return {
            "certificate_type": "GameTheory.QuittingStationaryRepairCertificate",
            "conclusion": "GameTheory.QuittingStationaryRepairCertificate.isUniformEquilibriumPayoff",
        }
    if kind == "accepted_holonomy_word":
        return {
            "certificate_type": "GameTheory.QuittingCyclicRepairCertificate",
            "conclusion": "GameTheory.QuittingCyclicRepairCertificate.isUniformEquilibriumPayoff",
        }
    raise ValueError(f"no stable Lean checker is registered for {kind!r}")


def _finding_certificate(finding: RepairFinding) -> dict[str, Any]:
    certificate = finding.certificate
    if finding.rung == "quitter_subset":
        return certificate.to_certificate_dict(kind="quitter_subset")
    if finding.rung == "quitter_pair":
        return certificate.to_certificate_dict(kind="quitter_pair")
    return certificate.to_certificate_dict()


def make_repair_report(
    game: RationalQuittingGame,
    result: LadderResult,
    config: SearchConfig,
) -> dict[str, Any]:
    finding = result.finding
    if finding is None or not finding.exact:
        raise ValueError("repair reports require an exact accepted finding")
    certificate = _finding_certificate(finding)
    return {
        "schema": REPORT_SCHEMA,
        "table": game.name,
        "table_fingerprint": table_fingerprint(game),
        "classification": "repair",
        "claim": "exact_terminal_nash_and_uniform_payoff",
        "rung": finding.rung,
        "source": finding.source,
        "certificate": certificate,
        "machine_check": {
            "exact_arithmetic": "fractions.Fraction",
            "python_command": "python3 -m experiments.quitting_repair_cegis verify-report",
            "lean": _lean_checker_for(certificate["kind"]),
        },
        "search": config.to_dict(),
        "trace": [trace_dict(entry) for entry in result.trace],
    }


def make_filter_report(
    game: RationalQuittingGame,
    *,
    fixed_gap: Fraction,
    scope: Mapping[str, Any],
    tested: int,
    minimum_regret: Fraction | None,
    reason: str,
) -> dict[str, Any]:
    if fixed_gap <= 0:
        raise ValueError("a fixed-gap filter needs a positive gap")
    return {
        "schema": REPORT_SCHEMA,
        "table": game.name,
        "table_fingerprint": table_fingerprint(game),
        "classification": "filter",
        "claim": "bounded_search_filter_only",
        "proves_nonexistence": False,
        "fixed_gap": fraction_text(fixed_gap),
        "tested": tested,
        "minimum_regret": (
            fraction_text(minimum_regret) if minimum_regret is not None else None
        ),
        "scope": dict(scope),
        "reason": reason,
        "required_for_nonexistence": (
            "GameTheory.HasTerminalExploitabilityGap against every behavioral profile"
        ),
    }


def make_gap_counterexample_report(
    game: RationalQuittingGame,
    *,
    fixed_gap: Fraction,
    certificate: dict[str, Any],
    regret: Fraction,
    source: str,
) -> dict[str, Any]:
    if not 0 <= regret < fixed_gap:
        raise ValueError("the supplied profile does not refute the fixed gap")
    return {
        "schema": REPORT_SCHEMA,
        "table": game.name,
        "table_fingerprint": table_fingerprint(game),
        "classification": "gap_counterexample",
        "claim": "counterexample_to_fixed_gap_candidate",
        "is_repair": regret == 0,
        "fixed_gap": fraction_text(fixed_gap),
        "exact_terminal_exploitability": fraction_text(regret),
        "source": source,
        "certificate": certificate,
    }


def validate_claim_discipline(report: Mapping[str, Any]) -> None:
    if report.get("schema") != REPORT_SCHEMA:
        raise ValueError(f"unsupported report schema {report.get('schema')!r}")
    classification = report.get("classification")
    if classification == "filter":
        if report.get("proves_nonexistence") is not False:
            raise ValueError("finite filters must explicitly deny a nonexistence claim")
        if report.get("claim") != "bounded_search_filter_only":
            raise ValueError("finite negative reports must be labelled as filters")
        return
    if classification == "repair":
        if report.get("claim") != "exact_terminal_nash_and_uniform_payoff":
            raise ValueError("positive reports must carry the exact repair claim")
        return
    if classification == "gap_counterexample":
        if report.get("claim") != "counterexample_to_fixed_gap_candidate":
            raise ValueError("gap counterexamples need their narrow claim")
        return
    if classification == "nonexistence":
        certificate = report.get("certificate", {})
        if certificate.get("kind") != "all_behavior_terminal_gap":
            raise ValueError(
                "nonexistence requires an all-behavior terminal-gap certificate"
            )
        if certificate.get("lean_predicate") != "GameTheory.HasTerminalExploitabilityGap":
            raise ValueError("nonexistence must target HasTerminalExploitabilityGap")
        if not certificate.get("lean_declaration"):
            raise ValueError("nonexistence requires a named Lean proof declaration")
        if parse_fraction(certificate.get("gap")) <= 0:
            raise ValueError("nonexistence gap must be positive")
        return
    raise ValueError(f"unknown report classification {classification!r}")


def _expected_certificate(
    game: RationalQuittingGame, certificate: Mapping[str, Any]
) -> dict[str, Any]:
    kind = certificate.get("kind")
    if kind == "cutoff_one":
        evaluation = evaluate_cutoff_one(game, certificate["hazards"])
        if not evaluation.exact:
            raise ValueError("reported cutoff-one repair is not exact")
        return evaluation.to_certificate_dict()
    if kind in {"stationary_full_rate", "quitter_subset", "quitter_pair"}:
        evaluation = evaluate_stationary(game, certificate["hazards"])
        if not evaluation.exact:
            raise ValueError("reported stationary repair is not exact")
        return evaluation.to_certificate_dict(kind=kind)
    if kind == "accepted_holonomy_word":
        evaluation = evaluate_cyclic_word(game, certificate["word"])
        if not evaluation.exact:
            raise ValueError("reported cyclic word misses the exact compiler hypotheses")
        return evaluation.to_certificate_dict()
    raise ValueError(f"cannot verify certificate kind {kind!r}")


def verify_report(game: RationalQuittingGame, report: Mapping[str, Any]) -> None:
    validate_claim_discipline(report)
    if report.get("table_fingerprint") != table_fingerprint(game):
        raise ValueError("report/table fingerprint mismatch")
    classification = report["classification"]
    if classification == "repair":
        certificate = report["certificate"]
        expected = _expected_certificate(game, certificate)
        if dict(certificate) != expected:
            raise ValueError(
                "repair certificate payload does not match exact recomputation"
            )
        _lean_checker_for(expected["kind"])
    elif classification == "gap_counterexample":
        certificate = report["certificate"]
        kind = certificate.get("kind")
        if kind == "cutoff_one":
            evaluation = evaluate_cutoff_one(game, certificate["hazards"])
            regret = max(evaluation.regrets)
            expected = evaluation.to_certificate_dict()
        elif kind in {"stationary_full_rate", "quitter_subset", "quitter_pair"}:
            evaluation = evaluate_stationary(game, certificate["hazards"])
            regret = max(evaluation.regrets)
            expected = evaluation.to_certificate_dict(kind=kind)
        elif kind == "accepted_holonomy_word":
            evaluation = evaluate_cyclic_word(game, certificate["word"])
            regret = evaluation.initial_max_regret()
            expected = evaluation.to_certificate_dict()
        else:
            raise ValueError(f"unknown gap-counterexample certificate {kind!r}")
        if dict(certificate) != expected:
            raise ValueError("gap-counterexample payload is stale or corrupted")
        if fraction_text(regret) != report["exact_terminal_exploitability"]:
            raise ValueError("gap-counterexample regret does not recompute")
        if not regret < parse_fraction(report["fixed_gap"]):
            raise ValueError("profile does not refute the reported fixed gap")
    # Filters and Lean-backed all-behavior nonexistence reports are schema-
    # checked here.  Their respective finite trace or external Lean theorem is
    # the evidence; a finite Python runner never upgrades the former to the latter.


def dump_report(report: Mapping[str, Any], path: str | Path | None = None) -> str:
    text = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=False) + "\n"
    if path is not None:
        Path(path).write_text(text, encoding="utf-8")
    return text


def load_report(path: str | Path) -> dict[str, Any]:
    with Path(path).open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("report root must be an object")
    return data
