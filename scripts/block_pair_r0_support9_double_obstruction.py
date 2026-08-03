#!/usr/bin/env python3
"""Exclude ``{2,6} -> 9 -> 9`` in the strict perturbed core.

Entry from support 2 or 6 fixes player 1's first support-9 value to its solo
payoff 2.  Write ``c,d`` for player 0 and player 3's hazards there.  Player
1's inactive Quit inequality is

    -3c + 4d <= 0,

so ``d<=3c/4``.  If another strict support-9 phase follows, active transport
gives

    c' = (3/2)c/(1-c),       d' = (200/411)d/(1-d).

Player 1's prescribed offset at that phase is

    y' = -(6c-2d-3cd)/((1-c)(1-d)).

Exact elimination gives its next inactive Quit-minus-prescribed difference

    (-3c'+4d') - y'
      = -(367cd-1233c+44d)/(822(c-1)(d-1)).

Strictness of ``c'`` gives ``c<2/5``.  On
``c=(2/5)u, d=(3/10)ur``, the negated numerator has the positive factor

    u(4110-110r-367ur),

whose degree-(1,1) Bernstein coefficients are ``4110,4000,4110,3633``.
The denominator is positive, so player 1 has a strictly profitable Quit
deviation at the second support-9 phase.

Thus every strict support-9 block entered from support 2 or 6 has length
exactly one.  Boundary and zero-hazard limits are not covered.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_9_3_9_obstruction as entry  # noqa: E402
from block_pair_r0_support3_endpoint_rank import (  # noqa: E402
    RationalPoly,
    rat,
    rat_add,
    rat_equal,
    rat_scale,
)
from block_pair_r0_support9_run_rank import bernstein_coefficients  # noqa: E402


Q = Fraction
one = algebra.one
c, d, c_next, d_next, u, r = tuple(
    algebra.var(index) for index in range(6)
)


def transported_hazards() -> tuple[RationalPoly, RationalPoly]:
    next_c = RationalPoly(
        algebra.scale(3, c),
        algebra.scale(2, algebra.sub(one, c)),
    )
    next_d = RationalPoly(
        algebra.scale(200, d),
        algebra.scale(411, algebra.sub(one, d)),
    )
    return next_c, next_d


def assert_second_inactive_difference() -> None:
    next_c, next_d = transported_hazards()
    survival = algebra.mul(algebra.sub(one, c), algebra.sub(one, d))
    h = algebra.sum_polys(
        [
            algebra.scale(6, c),
            algebra.scale(-2, d),
            algebra.scale(-3, algebra.mul(c, d)),
        ]
    )
    # Entry offset is zero, so the Bellman recurrence y= h+s*y' gives
    # y'=-h/s.  Therefore Quit-y' is q'+h/s.
    difference = rat_add(
        rat_add(rat_scale(-3, next_c), rat_scale(4, next_d)),
        RationalPoly(h, survival),
    )
    numerator = algebra.scale(
        -1,
        algebra.sum_polys(
            [
                algebra.scale(367, algebra.mul(c, d)),
                algebra.scale(-1233, c),
                algebra.scale(44, d),
            ]
        ),
    )
    denominator = algebra.scale(
        822,
        algebra.mul(algebra.sub(c, one), algebra.sub(d, one)),
    )
    rat_equal(difference, numerator, denominator)


def assert_positive_numerator() -> None:
    # Substitute c=(2/5)u and d=(3/4)c*r=(3/10)u*r.  After removing the
    # positive factor (3/25)u, the numerator is the core below.
    core = algebra.sum_polys(
        [
            algebra.const(4110),
            algebra.scale(-110, r),
            algebra.scale(-367, algebra.mul(u, r)),
        ]
    )
    coefficients = bernstein_coefficients(
        core, variables=(4, 5), degrees=(1, 1)
    )
    assert coefficients == {
        (0, 0): Q(4110),
        (0, 1): Q(4000),
        (1, 0): Q(4110),
        (1, 1): Q(3633),
    }
    assert min(coefficients.values()) == Q(3633) > 0

    c_scaled = algebra.scale(Q(2, 5), u)
    d_scaled = algebra.scale(Q(3, 10), algebra.mul(u, r))
    positive_numerator = algebra.sum_polys(
        [
            algebra.scale(-367, algebra.mul(c_scaled, d_scaled)),
            algebra.scale(1233, c_scaled),
            algebra.scale(-44, d_scaled),
        ]
    )
    assert positive_numerator == algebra.scale(
        Q(3, 25), algebra.mul(u, core)
    )


def assert_entry_clock() -> None:
    entry.assert_first_inactive_clock()
    # c'=(3/2)odds(c)<1 is equivalent to c<2/5.
    cleared = algebra.sub(
        algebra.scale(2, algebra.sub(one, c)), algebra.scale(3, c)
    )
    assert cleared == algebra.sub(algebra.const(2), algebra.scale(5, c))


def main() -> None:
    assert_entry_clock()
    assert_second_inactive_difference()
    assert_positive_numerator()

    print("exact support motif {2,6}->9->9 obstruction passed")
    print("the second support-9 player-1 Quit difference is strictly positive")
    print("every entered finite strict support-9 block has length one")
    print("scope: strict interior hazards; zero-hazard boundaries remain")


if __name__ == "__main__":
    main()
