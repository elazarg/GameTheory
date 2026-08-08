from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import json
import tempfile
import unittest

from experiments.quitting_repair_cegis.cegis import (
    _template_games,
    run_cegis_manifest,
)
from experiments.quitting_repair_cegis.model import RationalQuittingGame
from experiments.quitting_repair_cegis.report import (
    dump_report,
    make_repair_report,
    validate_claim_discipline,
    verify_report,
)
from experiments.quitting_repair_cegis.search import SearchConfig, run_repair_ladder

PACKAGE = Path(__file__).resolve().parents[1]
TABLES = PACKAGE / "tables"
REGRESSIONS = PACKAGE / "regressions"
EXPECTED = REGRESSIONS / "expected"


class SearchAndReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.config = SearchConfig.from_dict(
            {
                "probabilities": ["0", "1/4", "1/2", "2/3", "1"],
                "max_period": 2,
                "max_word_roots": 6,
                "max_words": 1000,
            }
        )

    def test_positive_report_recomputes_exactly(self) -> None:
        game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        result = run_repair_ladder(game, self.config)
        self.assertIsNotNone(result.finding)
        report = make_repair_report(game, result, self.config)
        verify_report(game, report)

        corrupted = deepcopy(report)
        corrupted["certificate"]["value"][0] = "1"
        with self.assertRaises(ValueError):
            verify_report(game, corrupted)

    def test_negative_claim_discipline(self) -> None:
        invalid = {
            "schema": "quitting-repair-report/v1",
            "classification": "nonexistence",
            "certificate": {"kind": "stationary_gap", "gap": "1/10"},
        }
        with self.assertRaises(ValueError):
            validate_claim_discipline(invalid)

        valid_filter = {
            "schema": "quitting-repair-report/v1",
            "classification": "filter",
            "claim": "bounded_search_filter_only",
            "proves_nonexistence": False,
        }
        validate_claim_discipline(valid_filter)

    def test_fixed_gap_cegis_has_filter_and_repair(self) -> None:
        manifest = REGRESSIONS / "fixed_gap_cegis.json"
        run = run_cegis_manifest(manifest)
        self.assertEqual(run.candidates, 2)
        self.assertEqual(
            [report["classification"] for report in run.reports],
            ["filter", "repair"],
        )
        self.assertFalse(run.reports[0]["proves_nonexistence"])

        with manifest.open("r", encoding="utf-8") as handle:
            raw_manifest = json.load(handle)
        games = list(_template_games(raw_manifest, manifest.resolve()))
        self.assertEqual(len(games), 2)
        verify_report(games[1], run.reports[1])

    def test_committed_reports_are_reproducible(self) -> None:
        cutoff_game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        report = json.loads((EXPECTED / "cutoff-one.json").read_text(encoding="utf-8"))
        verify_report(cutoff_game, report)

        # Regeneration is tested in a temporary copy to ensure the script's
        # deterministic payload, not filesystem timestamps, is the artifact.
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "report.json"
            dump_report(report, output)
            self.assertEqual(
                output.read_text(encoding="utf-8"),
                (EXPECTED / "cutoff-one.json").read_text(encoding="utf-8"),
            )


if __name__ == "__main__":
    unittest.main()
