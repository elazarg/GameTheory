#!/usr/bin/env python3
"""Exact run ranks for the support families {1,6} and {2,9}.

The perturbed block-pair table contains two identical active-coordinate
packets:

* at support 6={1,2}, player 2 has solo payoff 2, pair payoff 6, and receives
  0 when singleton player 0 (support 1) quits;
* at support 9={0,3}, player 3 has solo payoff 2, pair payoff 6, and receives
  0 when singleton player 1 (support 2) quits.

Let ``x`` be the other active player's hazard at one pair-support visit and
``X`` the corresponding hazard at the next pair-support visit.  Collapse any
finite intervening run of the designated singleton to its effective
absorption probability ``H``.  Active indifference at the first pair visit
and the singleton Bellman recurrence give

    (1-H)*(2+4*X) = 2+6*x/(1-x).

After clearing positive denominators,

    2*(1-H)*(1-x)*(X-x)
      = (2*x+1)*(H+x-H*x) > 0.

Thus ``X>x``.  The same identity with ``H=0`` covers a direct pair-to-pair
transition.  Therefore no finite strict cyclic profile that visits the pair
mode can be confined to supports {1,6} or to supports {2,9}, even with
arbitrary finite same-support runs and phase-dependent hazards.  The two
remaining singleton-only cycles are excluded separately below by their exact
payoff packets, completing the family-level exclusions.

This is a finite-cycle rank, not a nonperiodic-path exclusion.  It also does
not cover a singleton block that changes owner, or an excursion through a
third support.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
Poly = dict[tuple[int, int, int], Fraction]


def add(left: Poly, right: Poly) -> Poly:
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, Q(0)) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def scale(coefficient: int | Fraction, poly: Poly) -> Poly:
    coefficient = Q(coefficient)
    return {
        exponent: coefficient * value
        for exponent, value in poly.items()
        if coefficient * value != 0
    }


def mul(left: Poly, right: Poly) -> Poly:
    result: Poly = {}
    for left_exp, left_coefficient in left.items():
        for right_exp, right_coefficient in right.items():
            exponent = tuple(left_exp[index] + right_exp[index] for index in range(3))
            result[exponent] = (
                result.get(exponent, Q(0))
                + left_coefficient * right_coefficient
            )
    return {
        exponent: coefficient
        for exponent, coefficient in result.items()
        if coefficient != 0
    }


one: Poly = {(0, 0, 0): Q(1)}
x: Poly = {(1, 0, 0): Q(1)}
next_x: Poly = {(0, 1, 0): Q(1)}
block_hazard: Poly = {(0, 0, 1): Q(1)}


def sub(left: Poly, right: Poly) -> Poly:
    return add(left, scale(-1, right))


def assert_payoff_packets() -> None:
    # (solo payoff, pair payoff, intervening singleton reward).
    support_six = (terminal(4, 2), terminal(6, 2), terminal(1, 2))
    support_nine = (terminal(8, 3), terminal(9, 3), terminal(2, 3))
    assert support_six == support_nine == (2, 6, 0)


def assert_singleton_only_fences() -> None:
    # Repeating support 1 forever absorbs at player 0's negative solo payoff;
    # Never is a strict improvement.  At repeated support 2, inactive player
    # 2's immediate-Quit gain is 2+4h for active hazard h in (0,1).
    assert terminal(1, 0) == Q(-189, 100) < 0
    assert terminal(4, 2) - terminal(2, 2) == 2
    assert terminal(6, 2) - terminal(4, 2) == 4


def assert_rank_factorization() -> None:
    one_minus_h = sub(one, block_hazard)
    one_minus_x = sub(one, x)

    # Denominator-cleared Bellman equality:
    # (1-H)(1-x)(2+4X) - 2(1-x) - 6x = 0.
    bellman = add(
        mul(mul(one_minus_h, one_minus_x), add(scale(2, one), scale(4, next_x))),
        add(scale(-2, one_minus_x), scale(-6, x)),
    )

    cleared_increment = scale(
        2,
        mul(mul(one_minus_h, one_minus_x), sub(next_x, x)),
    )
    positive_factor = mul(
        add(scale(2, x), one),
        add(add(block_hazard, x), scale(-1, mul(block_hazard, x))),
    )

    # The desired identity holds modulo exactly half of the Bellman equation.
    assert sub(cleared_increment, positive_factor) == scale(Q(1, 2), bellman)


def main() -> None:
    assert_payoff_packets()
    assert_singleton_only_fences()
    assert_rank_factorization()
    assert_credible_first_unchanged()

    print("exact singleton/pair arbitrary-run ranks passed")
    print("support family {1,6}: next player-1 pair hazard X is strictly > x")
    print("support family {2,9}: next player-0 pair hazard X is strictly > x")
    print("excluded: all finite strict cycles confined to either support family")
    print("scope: changing singleton owners and third-support excursions remain")


if __name__ == "__main__":
    main()
