#!/usr/bin/env python3
"""Exclude the strict support motif ``{2,6} -> 9 -> 3 -> 9`` exactly.

Suppose a support-9 phase is entered from support 2 or 6, then followed by
one support-3 phase and another support-9 phase.  Active player 1 at either
entering support fixes the first support-9 player-1 value to 2.  Write c,d
for the first support-9 hazards of players 0,3 and e,f for the support-3
hazards of players 0,1.

The first support-9 inactive player-1 inequality gives ``d<=3c/4``.  The
active equalities determine

    e=(6c-2d-3cd)/(3(1-c)(1-d)),
    f=(200/311)*d/(1-d),

and determine the hazards C,D at the second support 9.  Player 1's deviation
difference at that second support reduces, after ``d=(3/4)c*r``, to

    -3c P(c,r)
    -----------------------------------------------------------,
    137(1533cr-1244)(6c^2r-cr-12c+4)

where P is the degree-(2,2) polynomial certified below.

Strictness of the support-3 and second support-9 hazards implies c<2/5:
player 3's active transport requires ``2+6c/(1-c)`` to be a convex-stage
value strictly below 6.  On ``c=(2/5)u``, 0<=u,r<=1, every Bernstein
coefficient of P is positive.  The first denominator factor is negative;
the second is positive exactly because e<1.  Therefore the displayed
difference is strictly positive, contradicting player 1's inactive Nash
inequality at the second support 9.

This is a finite single-phase motif obstruction.  Repeated support-9 or
support-3 blocks and nonperiodic zero-hazard limits remain outside it.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)
from block_pair_r0_support3_endpoint_rank import (  # noqa: E402
    RationalPoly,
    rat,
    rat_add,
    rat_equal,
    rat_mul,
    rat_scale,
    rat_sub,
)
from block_pair_r0_support9_run_rank import bernstein_coefficients  # noqa: E402


Q = Fraction
one = algebra.one
c, d, e, f, C, D = tuple(algebra.var(index) for index in range(6))


def derived_middle_hazards() -> tuple[RationalPoly, RationalPoly]:
    survival = algebra.mul(algebra.sub(one, c), algebra.sub(one, d))
    drift = algebra.sum_polys(
        [
            algebra.scale(6, c),
            algebra.scale(-2, d),
            algebra.scale(-3, algebra.mul(c, d)),
        ]
    )
    e_value = RationalPoly(drift, algebra.scale(3, survival))
    f_value = RationalPoly(
        algebra.scale(200, d),
        algebra.scale(311, algebra.sub(one, d)),
    )

    # Replay the two defining active-coordinate equations.
    player_one_value = rat_sub(
        rat(drift),
        rat_scale(3, rat_mul(rat(survival), e_value)),
    )
    assert player_one_value.numerator == {}
    shared_zero = rat_sub(
        rat_scale(311, rat_mul(f_value, rat(algebra.sub(one, d)))),
        rat_scale(200, rat(d)),
    )
    assert shared_zero.numerator == {}
    return e_value, f_value


def second_support_hazards(
    e_value: RationalPoly, f_value: RationalPoly
) -> tuple[RationalPoly, RationalPoly]:
    # Player 3's active equality at the first support 9 says its successor
    # support-3 value is 2+6*odds(c).  At support 3, singleton absorptions pay
    # player 3 zero, joint absorption pays 2, and survival leads to the next
    # support-9 current value 2+4C.  Solve this equality for C.
    target_three = rat_add(
        rat(algebra.const(2)),
        RationalPoly(algebra.scale(6, c), algebra.sub(one, c)),
    )
    survival_three = rat_mul(
        rat_sub(rat(one), e_value), rat_sub(rat(one), f_value)
    )
    joint_three = rat_scale(2, rat_mul(e_value, f_value))
    c_numerator = rat_sub(
        rat_sub(target_three, joint_three),
        rat_scale(2, survival_three),
    )
    c_value = RationalPoly(
        algebra.mul(c_numerator.numerator, survival_three.denominator),
        algebra.scale(
            4,
            algebra.mul(c_numerator.denominator, survival_three.numerator),
        ),
    )
    # The preceding construction assumes survival_three's denominator is
    # carried by c_numerator; verify C against the defining equation rather
    # than trusting the hand-written quotient representation.
    defining_c = rat_sub(
        rat_add(joint_three, rat_mul(survival_three, rat_add(rat(algebra.const(2)), rat_scale(4, c_value)))),
        target_three,
    )
    assert defining_c.numerator == {}

    # Shared active player 0 across 3->9 gives D=(300/137)*odds(f).
    d_value = RationalPoly(
        algebra.scale(300, f_value.numerator),
        algebra.scale(
            137,
            algebra.sub(f_value.denominator, f_value.numerator),
        ),
    )
    shared_zero = rat_sub(
        rat_scale(137, rat_mul(d_value, rat_sub(rat(one), f_value))),
        rat_scale(300, f_value),
    )
    assert shared_zero.numerator == {}
    return c_value, d_value


def assert_second_inactive_difference(
    e_value: RationalPoly,
    c_value: RationalPoly,
    d_value: RationalPoly,
) -> None:
    # Active player 1 at support 3 fixes its successor offset at the second
    # support 9 to -9*odds(e).  Quit there has offset -3C+4D.
    successor_offset = RationalPoly(
        algebra.scale(-9, e_value.numerator),
        algebra.sub(e_value.denominator, e_value.numerator),
    )
    deviation = rat_sub(
        rat_add(rat_scale(-3, c_value), rat_scale(4, d_value)),
        successor_offset,
    )

    expected_core = algebra.sum_polys(
        [
            algebra.scale(1462242, algebra.mul(c, algebra.mul(d, d))),
            algebra.scale(-3165789, algebra.mul(c, d)),
            algebra.scale(894747, c),
            algebra.scale(567470, algebra.mul(d, d)),
            algebra.scale(-28270, d),
        ]
    )
    expected_numerator = algebra.scale(-3, expected_core)
    expected_denominator = algebra.scale(
        274,
        algebra.mul(
            algebra.sub(algebra.scale(511, d), algebra.const(311)),
            algebra.sum_polys(
                [
                    algebra.scale(6, algebra.mul(c, d)),
                    algebra.scale(-9, c),
                    algebra.scale(-1, d),
                    algebra.const(3),
                ]
            ),
        ),
    )
    rat_equal(deviation, expected_numerator, expected_denominator)


def assert_payoff_upper_bound() -> None:
    assert tuple(terminal(mask, 3) for mask in (1, 2, 3, 8, 9)) == (0, 0, 2, 2, 6)

    # With 0<C<1, the support-3 prescribed value for player 3 is strictly
    # below the expression obtained by replacing 2+4C with 6.  Its gap from
    # 6 is a sum of nonnegative products, strict for e,f>0.
    upper_value = algebra.add(
        algebra.scale(2, algebra.mul(e, f)),
        algebra.scale(
            6,
            algebra.mul(algebra.sub(one, e), algebra.sub(one, f)),
        ),
    )
    upper_gap = algebra.sub(algebra.const(6), upper_value)
    assert upper_gap == algebra.sum_polys(
        [
            algebra.scale(4, algebra.mul(e, f)),
            algebra.scale(6, algebra.mul(e, algebra.sub(one, f))),
            algebra.scale(6, algebra.mul(f, algebra.sub(one, e))),
        ]
    )
    # Thus 2+6c/(1-c)<6, equivalently c<2/5.
    target_gap_cleared = algebra.sub(
        algebra.scale(6, algebra.sub(one, c)),
        algebra.add(
            algebra.scale(2, algebra.sub(one, c)), algebra.scale(6, c)
        ),
    )
    assert target_gap_cleared == algebra.scale(
        2, algebra.sub(algebra.const(2), algebra.scale(5, c))
    )


def assert_clock_sign_certificate() -> None:
    # Put d=(3/4)c*r from the first support-9 inactive inequality and then
    # c=(2/5)u using the strict payoff bound above.
    u = algebra.var(0)
    r = algebra.var(1)
    c_scaled = algebra.scale(Q(2, 5), u)
    polynomial = algebra.sum_polys(
        [
            algebra.scale(2193363, algebra.mul(algebra.mul(c_scaled, c_scaled), algebra.mul(r, r))),
            algebra.scale(851205, algebra.mul(c_scaled, algebra.mul(r, r))),
            algebra.scale(-6331578, algebra.mul(c_scaled, r)),
            algebra.scale(-56540, r),
            algebra.const(2385992),
        ]
    )
    coefficients = bernstein_coefficients(
        polynomial, variables=(0, 1), degrees=(2, 2)
    )
    assert len(coefficients) == 9
    assert min(coefficients.values()) == Q(12206022, 25)
    assert all(value > 0 for value in coefficients.values())

    # The denominator factors after the same clock substitution are
    #   1533*c*r-1244 < 0
    # and
    #   6*c^2*r-c*r-12*c+4 = (4/3)(3s-h) > 0.
    # The first sign already follows on c<=2/5,r<=1.
    assert Q(1533) * Q(2, 5) - Q(1244) < 0

    c_raw = algebra.var(2)
    d_clock = algebra.scale(Q(3, 4), algebra.mul(c_raw, r))
    survival = algebra.mul(algebra.sub(one, c_raw), algebra.sub(one, d_clock))
    drift = algebra.sum_polys(
        [
            algebra.scale(6, c_raw),
            algebra.scale(-2, d_clock),
            algebra.scale(-3, algebra.mul(c_raw, d_clock)),
        ]
    )
    second_denominator_factor = algebra.sum_polys(
        [
            algebra.scale(6, algebra.mul(algebra.mul(c_raw, c_raw), r)),
            algebra.scale(-1, algebra.mul(c_raw, r)),
            algebra.scale(-12, c_raw),
            algebra.const(4),
        ]
    )
    # e=drift/(3*survival)<1 makes the right side strictly positive.
    assert algebra.scale(
        Q(4, 3), algebra.sub(algebra.scale(3, survival), drift)
    ) == second_denominator_factor


def assert_first_inactive_clock() -> None:
    # At entry the player-1 value is 2, so its first support-9 inactive
    # difference is exactly -3c+4d.  Nash gives d<=3c/4.
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)
    one_minus_c = algebra.sub(one, c)
    one_minus_d = algebra.sub(one, d)
    quit_value = algebra.sum_polys(
        [
            algebra.scale(2, algebra.mul(one_minus_c, one_minus_d)),
            algebra.scale(-1, algebra.mul(c, one_minus_d)),
            algebra.scale(6, algebra.mul(one_minus_c, d)),
            algebra.scale(3, algebra.mul(c, d)),
        ]
    )
    assert algebra.sub(quit_value, algebra.const(2)) == algebra.add(
        algebra.scale(-3, c), algebra.scale(4, d)
    )


def assert_single_phase_obstruction() -> None:
    """Replay the exact contradiction for one intervening support-3 phase."""

    assert_first_inactive_clock()
    e_value, f_value = derived_middle_hazards()
    c_value, d_value = second_support_hazards(e_value, f_value)
    assert_second_inactive_difference(e_value, c_value, d_value)
    assert_payoff_upper_bound()
    assert_clock_sign_certificate()
    assert_credible_first_unchanged()


def main() -> None:
    assert_single_phase_obstruction()

    print("exact support motif {2,6}->9->3->9 obstruction passed")
    print("second support-9 player-1 deviation is strictly profitable")
    print("degree-(2,2) Bernstein minimum = 12206022/25")
    print("scope: single 9/3/9 phases; repeated blocks and boundaries remain")


if __name__ == "__main__":
    main()
