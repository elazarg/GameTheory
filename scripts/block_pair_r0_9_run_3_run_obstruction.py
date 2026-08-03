#!/usr/bin/env python3
"""Exclude ``{2,6} -> 9+ -> 3+ -> 9`` in the strict perturbed core.

The support-3 block obstruction already covers one initial support-9 phase.
This checker proves that an arbitrary finite strict support-9 waiting block
does not evade it.

Measure player 1's prescribed value at support 9 by its offset ``y`` from 2.
For support-9 hazards ``c,d``, put

    s = (1-c)(1-d),
    h = 6c - 2d - 3cd,
    q = -3c + 4d.

The Bellman recurrence through another support-9 phase is
``y = h + s*y_next`` and the inactive Quit inequality is ``q <= y``.
Entry from support 2 or 6 gives ``y=0``.  If ``y<=0``, then ``q<=0`` gives
``d<=3c/4``; on that clock cone ``h>0``.  Hence every later support-9 offset
is strictly negative.

At the transition to support 3, with player-0 hazard ``e``, active player 1
gives

    y = h - 3s e.

Thus ``y<=0`` means ``e>=e0=h/(3s)``.  Let ``Delta(c,d,e)`` be player 1's
final support-9 deviation after this support-3 phase, with the remaining
active coordinates eliminated.  Exact subtraction gives

    Delta(c,d,e) - Delta(c,d,E)
      = 3(e-E) N(c,d)
        / (2(E-1)(c-1)(511d-311)(e-1)),

where

    N(c,d)=3488cd-2488c-2555d+1555.

The future support-3/9 block bounds ``c<2/5``; together with
``d<=3c/4``, an exact Bernstein certificate gives ``N>0``.  All four
denominator factors are negative in the strict chart, so ``Delta`` is
increasing in ``e``.  The old zero-offset case ``e=e0`` is exactly the
already-certified one-initial-9 obstruction.  Therefore every negative
incoming offset only strengthens its profitable final deviation.  The
support-3 insertion theorem then supplies an arbitrary nonempty 3 block.

The result is finite and strict.  It does not cover a final support-9 block
of length greater than one, cycles using only supports 3 and 9, boundary
hazards, or nonperiodic zero-hazard limits.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_9_3_run_obstruction as support_three_run  # noqa: E402
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
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
c, d, e, E, y, y_next = tuple(algebra.var(index) for index in range(6))


def odds(value: RationalPoly) -> RationalPoly:
    return RationalPoly(
        value.numerator,
        algebra.sub(value.denominator, value.numerator),
    )


def support_nine_packet() -> tuple[algebra.Poly, algebra.Poly, algebra.Poly]:
    """Replay the player-1 offset recurrence and inactive Quit difference."""

    assert tuple(terminal(mask, 1) for mask in (1, 8, 9)) == (8, 0, 3)
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)
    survival = algebra.mul(algebra.sub(one, c), algebra.sub(one, d))
    prescribed = algebra.sum_polys(
        [
            algebra.scale(8, algebra.mul(c, algebra.sub(one, d))),
            algebra.scale(3, algebra.mul(c, d)),
            algebra.mul(
                survival,
                algebra.add(algebra.const(2), y_next),
            ),
        ]
    )
    h = algebra.sum_polys(
        [
            algebra.scale(6, c),
            algebra.scale(-2, d),
            algebra.scale(-3, algebra.mul(c, d)),
        ]
    )
    assert algebra.sub(prescribed, algebra.const(2)) == algebra.add(
        h, algebra.mul(survival, y_next)
    )

    quit_value = algebra.sum_polys(
        [
            algebra.scale(
                2,
                algebra.mul(algebra.sub(one, c), algebra.sub(one, d)),
            ),
            algebra.scale(-1, algebra.mul(c, algebra.sub(one, d))),
            algebra.scale(6, algebra.mul(algebra.sub(one, c), d)),
            algebra.scale(3, algebra.mul(c, d)),
        ]
    )
    q = algebra.add(algebra.scale(-3, c), algebra.scale(4, d))
    assert algebra.sub(quit_value, algebra.const(2)) == q

    # At a successor support-3 phase, active player 1's current payoff is
    # 2(1-e)-e=2-3e, so its offset is -3e.
    assert (terminal(2, 1), terminal(3, 1)) == (2, -1)
    transition = algebra.add(h, algebra.scale(-3, algebra.mul(survival, e)))
    return survival, h, transition


def assert_negative_offset_propagation() -> None:
    """Certify h>0 whenever an offset y<=0 satisfies inactive Nash."""

    # q<=y<=0 implies d=(3/4)c*r for some r in [0,1].  After factoring c,
    # h/c = 6 -(3/2)r -(9/4)cr is positive on the whole unit square.
    u = algebra.var(0)
    r = algebra.var(1)
    bracket = algebra.sum_polys(
        [
            algebra.const(6),
            algebra.scale(Q(-3, 2), r),
            algebra.scale(Q(-9, 4), algebra.mul(u, r)),
        ]
    )
    coefficients = bernstein_coefficients(
        bracket, variables=(0, 1), degrees=(1, 1)
    )
    assert coefficients == {
        (0, 0): Q(6),
        (0, 1): Q(9, 2),
        (1, 0): Q(6),
        (1, 1): Q(9, 4),
    }
    assert min(coefficients.values()) == Q(9, 4) > 0


def eliminated_deviation(e_value: RationalPoly) -> RationalPoly:
    """Eliminate the middle support-3 and final support-9 coordinates."""

    f_value = rat_scale(Q(200, 311), odds(rat(d)))
    final_d = rat_scale(Q(300, 137), odds(f_value))
    target_three = rat_add(
        rat(algebra.const(2)), rat_scale(6, odds(rat(c)))
    )
    survival_three = rat_mul(
        rat_sub(rat(one), e_value), rat_sub(rat(one), f_value)
    )
    joint_three = rat_scale(2, rat_mul(e_value, f_value))
    c_numerator = rat_sub(
        rat_sub(target_three, joint_three),
        rat_scale(2, survival_three),
    )
    final_c = RationalPoly(
        algebra.mul(c_numerator.numerator, survival_three.denominator),
        algebra.scale(
            4,
            algebra.mul(c_numerator.denominator, survival_three.numerator),
        ),
    )
    return rat_add(
        rat_add(rat_scale(-3, final_c), rat_scale(4, final_d)),
        rat_scale(9, odds(e_value)),
    )


def assert_deviation_monotonicity_identity() -> None:
    """Verify the exact two-point difference formula for Delta."""

    difference = rat_sub(
        eliminated_deviation(rat(e)), eliminated_deviation(rat(E))
    )
    monotonicity_core = algebra.sum_polys(
        [
            algebra.scale(3488, algebra.mul(c, d)),
            algebra.scale(-2488, c),
            algebra.scale(-2555, d),
            algebra.const(1555),
        ]
    )
    expected_numerator = algebra.scale(
        3, algebra.mul(algebra.sub(e, E), monotonicity_core)
    )
    expected_denominator = algebra.scale(
        2,
        algebra.mul(
            algebra.mul(algebra.sub(E, one), algebra.sub(c, one)),
            algebra.mul(
                algebra.sub(algebra.scale(511, d), algebra.const(311)),
                algebra.sub(e, one),
            ),
        ),
    )
    rat_equal(difference, expected_numerator, expected_denominator)


def assert_monotonicity_core_positive() -> None:
    """Certify N(c,d)>0 on c<=2/5, d<=3c/4."""

    u = algebra.var(0)
    r = algebra.var(1)
    c_scaled = algebra.scale(Q(2, 5), u)
    d_scaled = algebra.scale(Q(3, 4), algebra.mul(c_scaled, r))
    core = algebra.sum_polys(
        [
            algebra.scale(3488, algebra.mul(c_scaled, d_scaled)),
            algebra.scale(-2488, c_scaled),
            algebra.scale(-2555, d_scaled),
            algebra.const(1555),
        ]
    )
    coefficients = bernstein_coefficients(
        core, variables=(0, 1), degrees=(2, 1)
    )
    assert coefficients == {
        (0, 0): Q(1555),
        (0, 1): Q(1555),
        (1, 0): Q(5287, 5),
        (1, 1): Q(13483, 20),
        (2, 0): Q(2799, 5),
        (2, 1): Q(10593, 50),
    }
    assert min(coefficients.values()) == Q(10593, 50) > 0


def assert_zero_offset_matches_base() -> None:
    """Identify Delta(c,d,e0) with the certified zero-offset numerator."""

    survival, h, _transition = support_nine_packet()
    e_zero = RationalPoly(h, algebra.scale(3, survival))
    # Directly replay y=h-3se0=0.
    assert rat_sub(
        rat(h), rat_scale(3, rat_mul(rat(survival), e_zero))
    ).numerator == {}

    deviation = eliminated_deviation(e_zero)
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


def main() -> None:
    support_three_run.main()
    support_nine_packet()
    assert_negative_offset_propagation()
    assert_deviation_monotonicity_identity()
    assert_monotonicity_core_positive()
    assert_zero_offset_matches_base()

    print("exact support motif {2,6}->9+->3+->9 obstruction passed")
    print("support-9 waiting makes player 1's incoming offset negative")
    print("the final deviation is increasing in the successor support-3 hazard")
    print("scope: finite strict 9/3 blocks and one final support-9 phase")


if __name__ == "__main__":
    main()
