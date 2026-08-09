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
    max_regret,
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
            "status": "theorem_schema_only",
            "certificate_type": "GameTheory.QuittingCutoffOneRepairCertificate",
            "conclusion": "GameTheory.QuittingCutoffOneRepairCertificate.isUniformEquilibriumPayoff",
        }
    if kind in {
        "stationary_full_rate",
        "quitter_subset",
        "quitter_pair",
    }:
        return {
            "status": "theorem_schema_only",
            "certificate_type": "GameTheory.QuittingStationaryRepairCertificate",
            "conclusion": "GameTheory.QuittingStationaryRepairCertificate.isUniformEquilibriumPayoff",
        }
    if kind == "accepted_holonomy_word":
        return {
            "status": "theorem_schema_only",
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
            # The JSON payload is exact external evidence, not a Lean term.
            # This identifies the theorem schema that a promoted certificate
            # must instantiate; it never claims that Python authenticated one.
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
    if tested <= 0:
        raise ValueError("a finite filter must record at least one tested profile")
    if minimum_regret is None:
        raise ValueError("a finite filter must record its exact minimum regret")
    if minimum_regret < fixed_gap:
        raise ValueError(
            "a tested profile refutes the proposed fixed gap; emit a "
            "gap_counterexample report instead"
        )
    return {
        "schema": REPORT_SCHEMA,
        "table": game.name,
        "table_fingerprint": table_fingerprint(game),
        "classification": "filter",
        "claim": "bounded_search_filter_only",
        "proves_nonexistence": False,
        "fixed_gap": fraction_text(fixed_gap),
        "tested": tested,
        "minimum_regret": fraction_text(minimum_regret),
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
        # A low-regret profile is not a repair unless it separately satisfies a
        # stable Lean certificate type.  Exact repairs are emitted by
        # ``make_repair_report`` instead, never through this narrow class.
        "is_repair": False,
        "fixed_gap": fraction_text(fixed_gap),
        "exact_terminal_exploitability": fraction_text(regret),
        "source": source,
        "certificate": certificate,
    }


def _require_filter_fields(report: Mapping[str, Any]) -> None:
    try:
        fixed_gap = parse_fraction(report["fixed_gap"])
        minimum_regret = parse_fraction(report["minimum_regret"])
        tested = int(report["tested"])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError(
            "finite filters must record fixed_gap, tested, and minimum_regret"
        ) from exc
    if fixed_gap <= 0:
        raise ValueError("finite filters need a positive fixed gap")
    if tested <= 0:
        raise ValueError("finite filters must test at least one profile")
    if minimum_regret < fixed_gap:
        raise ValueError("a tested profile refutes the reported fixed gap")


def validate_claim_discipline(report: Mapping[str, Any]) -> None:
    if report.get("schema") != REPORT_SCHEMA:
        raise ValueError(f"unsupported report schema {report.get('schema')!r}")
    classification = report.get("classification")
    if classification == "filter":
        if report.get("proves_nonexistence") is not False:
            raise ValueError("finite filters must explicitly deny a nonexistence claim")
        if report.get("claim") != "bounded_search_filter_only":
            raise ValueError("finite negative reports must be labelled as filters")
        _require_filter_fields(report)
        return
    if classification == "repair":
        if report.get("claim") != "exact_terminal_nash_and_uniform_payoff":
            raise ValueError("positive reports must carry the exact repair claim")
        return
    if classification == "gap_counterexample":
        if report.get("claim") != "counterexample_to_fixed_gap_candidate":
            raise ValueError("gap counterexamples need their narrow claim")
        if report.get("is_repair") is not False:
            raise ValueError(
                "gap-counterexample reports cannot claim a repair; use a "
                "machine-checkable repair report"
            )
        try:
            fixed_gap = parse_fraction(report["fixed_gap"])
            exploitability = parse_fraction(report["exact_terminal_exploitability"])
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(
                "gap counterexamples must record their positive gap and exact regret"
            ) from exc
        if fixed_gap <= 0 or not 0 <= exploitability < fixed_gap:
            raise ValueError("gap-counterexample arithmetic is inconsistent")
        return
    if classification == "nonexistence":
        # A declaration name in JSON is not kernel evidence.  This Python
        # verifier therefore rejects the class unconditionally.  Genuine
        # all-behavior refutations are represented directly in Lean by
        # ``QuittingAllBehaviorTerminalGapCertificate`` and its theorem.
        raise ValueError(
            "Python cannot authenticate a Lean all-behavior proof declaration; "
            "construct and check QuittingAllBehaviorTerminalGapCertificate in Lean"
        )
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


def _expected_cyclic_profile_certificate(
    game: RationalQuittingGame, certificate: Mapping[str, Any]
) -> tuple[dict[str, Any], Fraction]:
    evaluation = evaluate_cyclic_word(game, certificate["word"])
    try:
        entry_phase = int(certificate["entry_phase"])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("cyclic profiles must name an entry_phase") from exc
    if not 0 <= entry_phase < evaluation.period:
        raise ValueError("cyclic profile entry_phase is outside the word")
    expected = evaluation.to_certificate_dict()
    expected["kind"] = "cyclic_profile"
    expected["entry_phase"] = entry_phase
    regret = max_regret(evaluation.behavioral_regrets[entry_phase])
    return expected, regret


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
        expected_lean = _lean_checker_for(expected["kind"])
        if report.get("machine_check", {}).get("lean") != expected_lean:
            raise ValueError(
                "repair report misstates its Lean theorem-schema status"
            )
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
        elif kind == "cyclic_profile":
            expected, regret = _expected_cyclic_profile_certificate(game, certificate)
        else:
            raise ValueError(f"unknown gap-counterexample certificate {kind!r}")
        if dict(certificate) != expected:
            raise ValueError("gap-counterexample payload is stale or corrupted")
        if fraction_text(regret) != report["exact_terminal_exploitability"]:
            raise ValueError("gap-counterexample regret does not recompute")
        if not regret < parse_fraction(report["fixed_gap"]):
            raise ValueError("profile does not refute the reported fixed gap")
    # Filters are exact-arithmetic summaries of an explicitly bounded run.  The
    # committed regressions rerun that search; this verifier checks their schema,
    # fingerprint, and arithmetic claim boundary.  Nonexistence JSON reports are
    # rejected above because a declaration string is not kernel evidence.


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
