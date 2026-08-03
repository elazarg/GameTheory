#!/usr/bin/env python3
"""Exact negative-fence audit for one block-pair payoff perturbation.

The candidate changes only

    r_0({0}) = -2 + 11/100.

It is *not* a counterexample certificate.  This script proves only that three
previous negative filters survive:

* Never is excluded by the unchanged positive singleton rewards of players
  1, 2, and 3;
* there is no nonzero stationary complementarity root with every quit
  probability below one; and
* the exact sure-quitter/credible-First audit is unchanged.

The period-eleven roots, longer product-jump paths, zero-hazard paths, and
arbitrary behavior profiles are outside this script's scope.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this assertion-based exact certificate must not run under python -O"
    )

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_stationary_certificate as base  # noqa: E402


THETA = Fraction(11, 100)
PARAMETER_STATIONARY_UPPER = Fraction(175562, 128233)


def perturbed_gains() -> tuple[base.Poly, ...]:
    old_row = base.TERMINAL[1]
    try:
        base.TERMINAL[1] = (
            Fraction(old_row[0]) + THETA,
            old_row[1],
            old_row[2],
            old_row[3],
        )
        return base.stationary_gain_numerators()
    finally:
        base.TERMINAL[1] = old_row


def perturbed_root_differences() -> tuple[base.Poly, ...]:
    old_row = base.TERMINAL[1]
    try:
        base.TERMINAL[1] = (
            Fraction(old_row[0]) + THETA,
            old_row[1],
            old_row[2],
            old_row[3],
        )
        return tuple(
            base.root_action_difference(player) for player in range(base.N)
        )
    finally:
        base.TERMINAL[1] = old_row


def assert_direct_support_fences(
    gain: tuple[base.Poly, ...],
) -> None:
    x0, x1, x2, x3 = base.X

    # Singleton supports.  Only the player-0 witness on support {2} changes.
    singleton_witnesses = {
        1: (
            3,
            base.mul(
                base.scale(2, x0),
                base.add(base.scale(2, x0), base.const(1)),
            ),
        ),
        2: (
            2,
            base.mul(
                base.scale(2, x1),
                base.add(base.scale(2, x1), base.const(1)),
            ),
        ),
        4: (
            0,
            base.add(
                base.mul(base.scale(2, x2), base.add(x2, base.const(1))),
                base.scale(
                    THETA,
                    base.mul(x2, base.sub(base.const(1), x2)),
                ),
            ),
        ),
        8: (
            1,
            base.mul(
                base.scale(2, x3),
                base.add(base.scale(2, x3), base.const(1)),
            ),
        ),
    }
    for mask, (player, expected) in singleton_witnesses.items():
        assert base.restrict_to_support(gain[player], mask) == expected
    assert 0 <= THETA < 2

    # Pair supports.  Supports {0,1} and {0,2} use the changed player-0 row.
    pair_witnesses = {
        3: (
            0,
            base.add(
                base.neg(
                    base.mul(
                        base.scale(3, x1),
                        base.add(x1, base.const(2)),
                    )
                ),
                base.scale(
                    THETA,
                    base.mul(x1, base.sub(base.const(1), x1)),
                ),
            ),
        ),
        5: (
            0,
            base.add(
                base.mul(
                    base.scale(2, x2),
                    base.add(x2, base.const(1)),
                ),
                base.scale(
                    THETA,
                    base.mul(x2, base.sub(base.const(1), x2)),
                ),
            ),
        ),
        6: (
            1,
            base.mul(
                base.scale(2, x2),
                base.sub(base.const(1), x2),
            ),
        ),
        9: (
            3,
            base.mul(
                base.scale(2, x0),
                base.add(base.scale(2, x0), base.const(1)),
            ),
        ),
        10: (
            1,
            base.mul(
                base.scale(2, x3),
                base.add(base.scale(2, x3), base.const(1)),
            ),
        ),
        12: (3, base.scale(-6, x2)),
    }
    for mask, (player, expected) in pair_witnesses.items():
        assert base.restrict_to_support(gain[player], mask) == expected
    assert THETA < 6

    # The three direct triple-support witnesses use players 2, 3, and 1, so
    # the perturbation of player 0 leaves them literally unchanged.
    bracket_7 = base.sub(
        base.mul(
            x0,
            base.add(
                base.add(base.scale(5, base.mul(x1, x1)), base.scale(-3, x1)),
                base.const(-2),
            ),
        ),
        base.add(base.scale(4, base.mul(x1, x1)), base.scale(2, x1)),
    )
    expected_7 = base.mul(base.sub(x0, base.const(1)), bracket_7)
    assert base.restrict_to_support(gain[2], 7) == expected_7

    positive_11 = base.add(
        base.add(
            base.mul(
                base.mul(x0, x0),
                base.mul(
                    base.sub(base.const(1), x1),
                    base.sub(base.const(2), x1),
                ),
            ),
            base.mul(x0, base.sub(base.const(1), base.mul(x1, x1))),
        ),
        x1,
    )
    assert base.restrict_to_support(gain[3], 11) == base.scale(2, positive_11)

    expected_14 = base.scale(
        2,
        base.mul(
            base.mul(
                base.sub(x2, base.const(1)),
                base.add(base.scale(2, x3), base.const(1)),
            ),
            base.sub(base.sub(base.mul(x2, x3), x2), x3),
        ),
    )
    assert base.restrict_to_support(gain[1], 14) == expected_14


def support_thirteen_bernstein_minimum(
    gain: tuple[base.Poly, ...],
) -> Fraction:
    _, _, x2, x3 = base.X
    mu0 = base.add(
        base.add(base.const(53490), base.scale(-2311, x3)),
        base.scale(-7574, x2),
    )
    mu2 = base.add(
        base.add(base.const(10698), base.scale(-37052, x3)),
        base.scale(-62134, x2),
    )
    certificate = base.restrict_to_support(
        base.add(
            base.add(base.mul(mu0, gain[0]), base.mul(mu2, gain[2])),
            base.mul(base.const(10698), gain[3]),
        ),
        13,
    )
    coefficients = base.bernstein_coefficients(
        certificate,
        variables=(0, 2, 3),
        degrees=(3, 3, 3),
    )
    assert coefficients[(0, 0, 0)] == 0
    minimum = min(
        coefficient
        for index, coefficient in coefficients.items()
        if index != (0, 0, 0)
    )
    assert minimum == 14264
    return minimum


def full_support_bernstein_minimum(
    gain: tuple[base.Poly, ...],
) -> Fraction:
    x0, x1, x2, x3 = base.X
    multipliers = (
        base.add(
            base.add(
                base.add(base.const(-15553008), base.scale(-7528932, x3)),
                base.scale(3755590, x0),
            ),
            base.scale(5098574, base.mul(x0, x2)),
        ),
        base.add(
            base.add(
                base.add(base.const(-15553008), base.scale(-15304880, x2)),
                base.scale(8520888, x1),
            ),
            base.scale(4172497, base.mul(x1, x3)),
        ),
        base.add(
            base.add(base.const(-15553008), base.scale(13687356, x2)),
            base.scale(1804402, x1),
        ),
        base.add(
            base.add(base.const(-15553008), base.scale(-5558092, x1)),
            base.scale(1700604, x0),
        ),
    )
    certificate: base.Poly = {}
    for multiplier, player_gain in zip(multipliers, gain):
        certificate = base.add(
            certificate,
            base.mul(multiplier, player_gain),
        )
    coefficients = base.bernstein_coefficients(
        certificate,
        variables=(0, 1, 2, 3),
        degrees=(3, 3, 3, 3),
    )
    assert coefficients[(0, 0, 0, 0)] == 0
    minimum = min(
        coefficient
        for index, coefficient in coefficients.items()
        if index != (0, 0, 0, 0)
    )
    assert minimum == Fraction(57960235, 6)
    return minimum


def assert_credible_first_unchanged() -> None:
    nominal = tuple(
        base.root_action_difference(player) for player in range(base.N)
    )
    perturbed = perturbed_root_differences()
    differences = tuple(
        base.sub(perturbed[player], nominal[player])
        for player in range(base.N)
    )
    x1, x2, x3 = base.X[1:]
    expected_player_zero = base.scale(
        THETA,
        base.prod_poly(
            (
                base.sub(base.const(1), x1),
                base.sub(base.const(1), x2),
                base.sub(base.const(1), x3),
            )
        ),
    )
    assert differences[0] == expected_player_zero
    assert all(not differences[player] for player in (1, 2, 3))

    # If player 1, 2, or 3 is the designated sure quitter, the added factor
    # vanishes identically on that face.
    for sure_player in (1, 2, 3):
        assert not base.substitute_one(differences[0], sure_player)

    # On the nominal sure-player-0 root set, the unchanged other-player Nash
    # conditions force player 3 to quit surely.  The added term therefore also
    # vanishes there.
    assert not base.substitute_one(differences[0], 3)

    # Re-run the nominal exhaustive sure-face audit whose root sets and gaps
    # have just been shown unchanged.
    base.assert_credible_first_certificate()


def main() -> None:
    assert THETA < PARAMETER_STATIONARY_UPPER
    assert base.TERMINAL[2][1] == 2
    assert base.TERMINAL[4][2] == 2
    assert base.TERMINAL[8][3] == 2

    gain = perturbed_gains()
    assert_direct_support_fences(gain)
    support_thirteen = support_thirteen_bernstein_minimum(gain)
    full_support = full_support_bernstein_minimum(gain)
    assert_credible_first_unchanged()

    print("exact r_0({0}) perturbation negative-fence audit passed")
    print(f"theta = {THETA}")
    print("Never gap retained = 2")
    print(f"support-13 Bernstein minimum = {support_thirteen}")
    print(f"full-support Bernstein minimum = {full_support}")
    print("credible-First gap retained >= 13/15")
    print(
        "scope: negative simple/stationary fences only; "
        "no all-path exclusion"
    )


if __name__ == "__main__":
    main()
