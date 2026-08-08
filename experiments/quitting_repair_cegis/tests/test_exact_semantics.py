from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import unittest

from experiments.quitting_repair_cegis.model import (
    RationalQuittingGame,
    parse_fraction,
)
from experiments.quitting_repair_cegis.profiles import (
    evaluate_cutoff_one,
    evaluate_cyclic_word,
    evaluate_stationary,
)

PACKAGE = Path(__file__).resolve().parents[1]
TABLES = PACKAGE / "tables"


class ExactSemanticsTests(unittest.TestCase):
    def test_binary_float_is_rejected(self) -> None:
        with self.assertRaises(TypeError):
            parse_fraction(0.5)

    def test_cutoff_one_mixed_certificate(self) -> None:
        game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        result = evaluate_cutoff_one(game, ("1/2", "1/2"))
        self.assertTrue(result.exact)
        self.assertEqual(result.value, (Fraction(0), Fraction(0)))
        self.assertEqual(result.behavioral_caps, result.value)

    def test_full_interval_stationary_repair(self) -> None:
        game = RationalQuittingGame.from_path(
            TABLES / "full_interval_stationary_repair.json"
        )
        result = evaluate_stationary(game, ("1/2", "1", "1/4"))
        self.assertTrue(result.exact)
        self.assertEqual(
            result.value, (Fraction(1), Fraction(3, 4), Fraction(1, 2))
        )
        self.assertEqual(result.behavioral_caps, result.value)

    def test_accepted_cyclic_word_checks_every_phase(self) -> None:
        game = RationalQuittingGame.from_path(TABLES / "constant_one_cycle.json")
        result = evaluate_cyclic_word(game, (("1", "0"), ("0", "1")))
        self.assertTrue(result.exact)
        self.assertEqual(result.period, 2)
        self.assertEqual(
            result.player_cycle_continue_products, (Fraction(0), Fraction(0))
        )
        self.assertTrue(all(regrets == (0, 0) for regrets in result.root_regrets))
        self.assertTrue(
            all(regrets == (0, 0) for regrets in result.behavioral_regrets)
        )

    def test_stationary_nonattainment_regression(self) -> None:
        game = RationalQuittingGame.from_path(
            TABLES / "stationary_nonattainment.json"
        )
        expected = {
            Fraction(1, 2): Fraction(1, 10),
            Fraction(1, 4): Fraction(1, 36),
            Fraction(1, 8): Fraction(1, 136),
        }
        for first_hazard, expected_regret in expected.items():
            result = evaluate_stationary(game, (first_hazard, Fraction(2, 3)))
            self.assertEqual(max(result.regrets), expected_regret)
            self.assertFalse(result.exact)


if __name__ == "__main__":
    unittest.main()
