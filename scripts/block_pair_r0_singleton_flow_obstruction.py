#!/usr/bin/env python3
"""Exact algebra for the perturbed block-pair singleton-flow obstruction.

For the block-pair table with r_0({0}) = -2 + 11/100, let q_i be player i's
solo-quitting payoff and put

    R_ij = (r_i({j}) - q_i) / 2.

The ordinary zero-hazard singleton-flow normalization is

    z' = z - R alpha,

where alpha is a measurable simplex control supported on the zero coordinates
of z.  This checker verifies the exact matrix facts used by the same
Baire-stratum/pair-collision proof as for the nominal table:

* a strictly positive left vector sends every column of R to one positive
  constant, forcing every bounded complete trajectory onto one weighted
  hyperplane;
* every principal block of size at least two is nonsingular, so an exact zero
  stratum can only carry one singleton mode;
* in each singleton mode the paired coordinate hits zero before either cross
  coordinate; and
* after the pair collision, every measurable mixture of the two pair modes
  drives the pair sum strictly negative.

This excludes only bounded complete ordinary absolutely-continuous
singleton-flow paths.  Product jumps and hybrid paths remain outside scope.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this assertion-based exact certificate must not run under python -O"
    )

from fractions import Fraction
from itertools import combinations
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


Q = Fraction
THETA = Q(11, 100)
ZERO = Q(0)
ONE = Q(1)


def terminal(mask: int, player: int) -> Fraction:
    value = Q(TERMINAL[mask][player])
    if mask == 1 and player == 0:
        value += THETA
    return value


SOLO = tuple(terminal(1 << player, player) for player in range(N))
RESIDUAL = tuple(
    tuple(
        (terminal(1 << quitter, player) - SOLO[player]) / 2
        for quitter in range(N)
    )
    for player in range(N)
)

EXPECTED_RESIDUAL = (
    (Q(0), Q(589, 200), Q(-211, 200), Q(-211, 200)),
    (Q(3), Q(0), Q(-1), Q(-1)),
    (Q(-1), Q(-1), Q(0), Q(3)),
    (Q(-1), Q(-1), Q(3), Q(0)),
)

LEFT_CLOCK = (Q(1), Q(589, 600), Q(2989, 3000), Q(2989, 3000))
CLOCK_RATE = Q(2857, 3000)
MATE = (1, 0, 3, 2)


def determinant(matrix: tuple[tuple[Fraction, ...], ...]) -> Fraction:
    size = len(matrix)
    if size == 0:
        return ONE
    if size == 1:
        return matrix[0][0]
    return sum(
        (
            (-1 if column % 2 else 1)
            * matrix[0][column]
            * determinant(
                tuple(
                    tuple(
                        row[index]
                        for index in range(size)
                        if index != column
                    )
                    for row in matrix[1:]
                )
            )
            for column in range(size)
        ),
        ZERO,
    )


def principal_determinants(size: int) -> tuple[Fraction, ...]:
    return tuple(
        determinant(
            tuple(
                tuple(RESIDUAL[row][column] for column in support)
                for row in support
            )
        )
        for support in combinations(range(N), size)
    )


def main() -> None:
    assert N == 4
    assert SOLO == (Q(-189, 100), Q(2), Q(2), Q(2))
    assert RESIDUAL == EXPECTED_RESIDUAL
    assert all(weight > 0 for weight in LEFT_CLOCK)

    weighted_columns = tuple(
        sum(
            LEFT_CLOCK[player] * RESIDUAL[player][column]
            for player in range(N)
        )
        for column in range(N)
    )
    assert weighted_columns == (CLOCK_RATE,) * N
    assert CLOCK_RATE > 0

    expected_determinants = {
        2: (
            Q(-1767, 200),
            Q(-211, 200),
            Q(-211, 200),
            Q(-1),
            Q(-1),
            Q(-9),
        ),
        3: (Q(611, 100), Q(611, 100), Q(633, 100), Q(6)),
        4: (Q(8571, 200),),
    }
    for size in (2, 3, 4):
        actual = principal_determinants(size)
        assert actual == expected_determinants[size]
        assert all(value != 0 for value in actual)

    # On the weighted hyperplane LEFT_CLOCK dot z = CLOCK_RATE with z >= 0,
    # the mate coordinate starts below CLOCK_RATE / LEFT_CLOCK[mate].
    # Its singleton-mode equation is z_m' = z_m - R_mj.
    for quitter in range(N):
        mate = MATE[quitter]
        mate_charge = RESIDUAL[mate][quitter]
        assert mate_charge > 0
        assert CLOCK_RATE / LEFT_CLOCK[mate] < mate_charge
        for cross in range(N):
            if cross not in (quitter, mate):
                assert RESIDUAL[cross][quitter] < 0

    # Once both coordinates of a hostile pair are zero, alpha is supported on
    # that pair.  Every allowed column charges the unweighted pair sum by a
    # strictly positive amount, so X' <= X - pair_charge and X immediately
    # becomes negative.
    pair_minimum_charges = []
    for left, right in ((0, 1), (2, 3)):
        charges = tuple(
            RESIDUAL[left][quitter] + RESIDUAL[right][quitter]
            for quitter in (left, right)
        )
        assert all(charge > 0 for charge in charges)
        pair_minimum_charges.append(min(charges))
    assert tuple(pair_minimum_charges) == (Q(589, 200), Q(3))

    print("exact perturbed singleton-flow obstruction algebra passed")
    print(f"theta = {THETA}")
    print(f"positive left clock = {LEFT_CLOCK}")
    print(f"common clock rate = {CLOCK_RATE}")
    print(
        "principal determinants = "
        + ", ".join(
            str(value)
            for size in (2, 3, 4)
            for value in expected_determinants[size]
        )
    )
    print(
        "pair collision charges >= "
        f"{pair_minimum_charges[0]}, {pair_minimum_charges[1]}"
    )
    print("scope: ordinary AC singleton flow only; product jumps remain open")


if __name__ == "__main__":
    main()
