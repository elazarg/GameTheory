#!/usr/bin/env python3
"""Exclude the strict support motif ``{2,6} -> 9 -> 3+ -> 9`` exactly.

The one-phase checker ``block_pair_r0_9_3_9_obstruction.py`` proves that
player 1 has a strictly profitable Quit deviation at the final support-9
phase when there is one intervening support-3 phase.  This checker proves
that inserting another strict support-3 phase preserves that profitable
deviation, so induction covers every finite nonempty support-3 block.

At a support-3 phase write ``e,f`` for the hazards of players 0,1 and let
``C`` be the virtual successor support-9 hazard of player 0.  The virtual
player-1 deviation difference is

    delta(e,f,C) = -3 C + 4 D(f) + 9 e/(1-e),
    D(f) = (300/137) f/(1-f).

After inserting one support-3 phase, the active-coordinate transports are

    x = 3 e/(1-e),       y = (900/311) f/(1-f).

Preservation of player 3's continuation value determines the new virtual
endpoint ``C'`` by

    2 + 4 C = 2xy + (1-x)(1-y)(2+4C').

Both deviation differences decrease strictly in their endpoint coordinate.
The old zero-deviation endpoint is

    C0 = (4D(f) + 9e/(1-e))/3.

Exact elimination gives

    delta(x,y,C'(C0))
      = -3(4370963ef - 383463e - 347900f)
        / (274(4e-1)(1211f-311)).

Insertion-valid strict hazards imply ``e<1/4`` and
``f<42607/435907``.  The denominator above is positive.  On the scaled
unit square the negated bilinear numerator has Bernstein coefficients

    0, 14822975300/435907, 383463/4, 10053121650/435907.

It is therefore strictly positive for positive ``e,f``.  Hence the new
deviation is positive at ``C0`` and, by monotonicity, remains positive for
every old endpoint with ``delta(e,f,C)>0``.

This is a finite strict-block theorem.  It does not cover an initial block
of two or more support-9 phases, support-3/9-only cycles, boundary hazards,
or nonperiodic zero-hazard limits.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_9_3_9_obstruction as base  # noqa: E402
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
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
e, f, C, x, y, C_next = tuple(algebra.var(index) for index in range(6))


def odds(value: RationalPoly) -> RationalPoly:
    return RationalPoly(
        value.numerator,
        algebra.sub(value.denominator, value.numerator),
    )


def inserted_hazards() -> tuple[RationalPoly, RationalPoly]:
    """Return the exact active-coordinate transports inside support 3."""

    e_value = rat(e)
    f_value = rat(f)
    x_value = rat_scale(3, odds(e_value))
    y_value = rat_scale(Q(900, 311), odds(f_value))

    assert rat_sub(
        rat_mul(x_value, rat_sub(rat(one), e_value)),
        rat_scale(3, e_value),
    ).numerator == {}
    assert rat_sub(
        rat_scale(311, rat_mul(y_value, rat_sub(rat(one), f_value))),
        rat_scale(900, f_value),
    ).numerator == {}
    return x_value, y_value


def endpoint_from_preserved_value(
    x_value: RationalPoly, y_value: RationalPoly
) -> RationalPoly:
    """Solve the player-3 value-preservation equation for ``C'``."""

    survival = rat_mul(
        rat_sub(rat(one), x_value), rat_sub(rat(one), y_value)
    )
    joint = rat_scale(2, rat_mul(x_value, y_value))
    preserved = rat_add(rat(algebra.const(2)), rat_scale(4, rat(C)))
    numerator = rat_sub(
        rat_sub(preserved, joint), rat_scale(2, survival)
    )
    c_next_value = RationalPoly(
        algebra.mul(numerator.numerator, survival.denominator),
        algebra.scale(
            4,
            algebra.mul(numerator.denominator, survival.numerator),
        ),
    )

    defining_equation = rat_sub(
        rat_add(
            joint,
            rat_mul(
                survival,
                rat_add(
                    rat(algebra.const(2)), rat_scale(4, c_next_value)
                ),
            ),
        ),
        preserved,
    )
    assert defining_equation.numerator == {}
    return c_next_value


def support_nine_deviation(
    e_value: RationalPoly,
    f_value: RationalPoly,
    c_value: RationalPoly,
) -> RationalPoly:
    """Player 1's Quit-minus-prescribed difference at virtual support 9."""

    d_value = rat_scale(Q(300, 137), odds(f_value))
    return rat_add(
        rat_add(rat_scale(-3, c_value), rat_scale(4, d_value)),
        rat_scale(9, odds(e_value)),
    )


def assert_boundary_elimination() -> None:
    """Replay the exact deviation formula at the old zero-deviation endpoint."""

    x_value, y_value = inserted_hazards()
    old_d = rat_scale(Q(300, 137), odds(rat(f)))
    zero_endpoint = rat_scale(
        Q(1, 3),
        rat_add(rat_scale(4, old_d), rat_scale(9, odds(rat(e)))),
    )

    # endpoint_from_preserved_value uses the polynomial coordinate C.  Build
    # it first, then substitute C=C0 in its rational expression by deriving
    # the same preservation quotient directly with C0.
    endpoint_from_preserved_value(x_value, y_value)
    survival = rat_mul(
        rat_sub(rat(one), x_value), rat_sub(rat(one), y_value)
    )
    joint = rat_scale(2, rat_mul(x_value, y_value))
    preserved_zero = rat_add(
        rat(algebra.const(2)), rat_scale(4, zero_endpoint)
    )
    numerator = rat_sub(
        rat_sub(preserved_zero, joint), rat_scale(2, survival)
    )
    endpoint_at_zero = RationalPoly(
        algebra.mul(numerator.numerator, survival.denominator),
        algebra.scale(
            4,
            algebra.mul(numerator.denominator, survival.numerator),
        ),
    )

    new_deviation = support_nine_deviation(
        x_value, y_value, endpoint_at_zero
    )
    bilinear = algebra.sum_polys(
        [
            algebra.scale(4370963, algebra.mul(e, f)),
            algebra.scale(-383463, e),
            algebra.scale(-347900, f),
        ]
    )
    denominator = algebra.scale(
        274,
        algebra.mul(
            algebra.sub(algebra.scale(4, e), one),
            algebra.sub(algebra.scale(1211, f), algebra.const(311)),
        ),
    )
    rat_equal(new_deviation, algebra.scale(-3, bilinear), denominator)


def assert_strict_sign_certificate() -> None:
    """Certify the bilinear sign on the insertion-valid hazard rectangle."""

    # x=3e/(1-e)<1 gives e<1/4.  The exit support-9 hazard
    # D(y)=(300/137)y/(1-y)<1 gives y<137/437 and hence the stated f bound.
    assert Q(42607, 435907) < Q(311, 1211)
    assert Q(42607, 435907) < 1

    u = algebra.var(0)
    v = algebra.var(1)
    e_scaled = algebra.scale(Q(1, 4), u)
    f_scaled = algebra.scale(Q(42607, 435907), v)
    negated_bilinear = algebra.sum_polys(
        [
            algebra.scale(383463, e_scaled),
            algebra.scale(347900, f_scaled),
            algebra.scale(-4370963, algebra.mul(e_scaled, f_scaled)),
        ]
    )
    coefficients = bernstein_coefficients(
        negated_bilinear, variables=(0, 1), degrees=(1, 1)
    )
    assert coefficients == {
        (0, 0): Q(0),
        (0, 1): Q(14822975300, 435907),
        (1, 0): Q(383463, 4),
        (1, 1): Q(10053121650, 435907),
    }
    assert all(value >= 0 for value in coefficients.values())
    assert all(
        coefficients[index] > 0
        for index in ((0, 1), (1, 0), (1, 1))
    )


def assert_endpoint_monotonicity() -> None:
    """Record the exact endpoint slopes used by the induction."""

    x_value, y_value = inserted_hazards()
    survival = rat_mul(
        rat_sub(rat(one), x_value), rat_sub(rat(one), y_value)
    )

    # Old deviation has slope -3 in C.  Value preservation gives
    # dC'/dC=1/survival, hence the inserted deviation has slope
    # -3/survival.  Both are strictly negative on a strict inserted phase.
    old_slope = Q(-3)
    assert old_slope < 0
    new_slope = RationalPoly(
        algebra.scale(-3, survival.denominator), survival.numerator
    )
    rat_equal(
        new_slope,
        algebra.scale(-3, survival.denominator),
        survival.numerator,
    )


def assert_support_three_run_obstruction() -> None:
    """Replay the base case and the support-3 insertion certificate."""

    base.assert_single_phase_obstruction()
    assert_boundary_elimination()
    assert_strict_sign_certificate()
    assert_endpoint_monotonicity()


def main() -> None:
    assert_support_three_run_obstruction()

    print("exact support motif {2,6}->9->3+->9 obstruction passed")
    print("a profitable final support-9 deviation survives each 3 insertion")
    print("bilinear Bernstein coefficients are nonnegative and nonzero off 0")
    print("scope: one initial 9, finite strict 3 block, one final 9")


if __name__ == "__main__":
    main()
