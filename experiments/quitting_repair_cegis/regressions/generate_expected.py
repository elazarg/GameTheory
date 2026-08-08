#!/usr/bin/env python3
"""Regenerate the committed exact rational regression reports."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import shutil

from experiments.quitting_repair_cegis.cegis import run_cegis_manifest
from experiments.quitting_repair_cegis.model import RationalQuittingGame, max_regret
from experiments.quitting_repair_cegis.profiles import (
    evaluate_cyclic_word,
    evaluate_stationary,
)
from experiments.quitting_repair_cegis.report import dump_report, make_repair_report
from experiments.quitting_repair_cegis.search import (
    LadderResult,
    RepairFinding,
    RungTrace,
    SearchConfig,
    run_repair_ladder,
)

ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "experiments" / "quitting_repair_cegis"
TABLES = PACKAGE / "tables"
EXPECTED = PACKAGE / "regressions" / "expected"


def direct_result(rung: str, evaluation, source: str) -> LadderResult:
    if rung == "holonomy_word":
        regret = evaluation.all_phase_max_regret()
    else:
        regret = max_regret(evaluation.regrets)
    return LadderResult(
        finding=RepairFinding(rung, evaluation, 1, source),
        trace=(
            RungTrace(
                rung=rung,
                tested=1,
                exhausted=False,
                best_regret=regret,
                note="committed exact rational regression",
            ),
        ),
    )


def main() -> None:
    EXPECTED.mkdir(parents=True, exist_ok=True)
    config = SearchConfig.from_dict(
        {
            "probabilities": ["0", "1/4", "1/2", "2/3", "1"],
            "max_period": 2,
            "max_word_roots": 6,
            "max_words": 1000,
        }
    )

    cutoff_game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
    cutoff_result = run_repair_ladder(cutoff_game, config)
    assert cutoff_result.finding is not None
    dump_report(
        make_repair_report(cutoff_game, cutoff_result, config),
        EXPECTED / "cutoff-one.json",
    )

    stationary_game = RationalQuittingGame.from_path(
        TABLES / "full_interval_stationary_repair.json"
    )
    stationary = evaluate_stationary(
        stationary_game, (Fraction(1, 2), Fraction(1), Fraction(1, 4))
    )
    assert stationary.exact
    dump_report(
        make_repair_report(
            stationary_game,
            direct_result(
                "quitter_pair",
                stationary,
                "known exact two-mixer/sure-quitter regression",
            ),
            config,
        ),
        EXPECTED / "stationary-pair.json",
    )

    cyclic_game = RationalQuittingGame.from_path(TABLES / "constant_one_cycle.json")
    cyclic = evaluate_cyclic_word(
        cyclic_game,
        ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))),
    )
    assert cyclic.exact
    dump_report(
        make_repair_report(
            cyclic_game,
            direct_result(
                "holonomy_word", cyclic, "known exact two-phase regression"
            ),
            config,
        ),
        EXPECTED / "accepted-holonomy-word.json",
    )

    cegis_dir = EXPECTED / "fixed-gap-cegis"
    if cegis_dir.exists():
        shutil.rmtree(cegis_dir)
    cegis_dir.mkdir(parents=True)
    manifest = PACKAGE / "regressions" / "fixed_gap_cegis.json"
    run = run_cegis_manifest(manifest)
    index = []
    for number, report in enumerate(run.reports):
        filename = f"{number:04d}.json"
        dump_report(report, cegis_dir / filename)
        index.append(
            {
                "file": filename,
                "table": report["table"],
                "classification": report["classification"],
            }
        )
    (cegis_dir / "index.json").write_text(
        json.dumps(
            {
                "schema": "quitting-table-cegis-summary/v1",
                "candidates": run.candidates,
                "reused_witnesses": len(run.witnesses),
                "reports": index,
            },
            sort_keys=True,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
