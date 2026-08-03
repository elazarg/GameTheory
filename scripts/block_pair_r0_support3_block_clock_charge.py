#!/usr/bin/env python3
"""Lift the support-3 clock charge to every finite strict block.

This is the quantitative value argument for the two residual five-mask
excursions

    6 -> 9 -> 3+ -> 6,
    6 -> 2+ -> 9 -> 3+ -> 6.

Write ``a,A`` for player 1's hazards at the initial and final support-6
phases, and ``S`` for survival through the whole intervening excursion.  If
the phases satisfy the active equalities and inactive endpoint conditions
used by ``block_pair_r0_support3_clock_charge.py``, then

    A - a >= (1/12) * (1-S).

For a support-3 self transition its two hazards obey

    e' = 3e/(1-e),       f' = (900/311)f/(1-f).

Both increase, while ``f/e`` decreases on the relevant ray.  The final
support-6 condition gives ``e_last < 2/11`` and hence every support-3 phase
lies in the box on which the endpoint threshold ``R(e,f)`` increases in both
coordinates.  Endpoint credibility at the last phase therefore also makes
the virtual one-phase path through the first support-3 phase credible.  The
one-phase checker supplies a ``1/2`` charge for that virtual path.

Inserting the remaining support-3 tail can only lower player 2's value: its
absorption payoffs there are ``0,0,-1``.  Exact value-to-hazard conversion
charges the tail by ``1/12`` of its additional absorption clock.  The two
charges compose to the displayed bound.  A preceding support-2 block has
zero player-2 absorption reward; the exact singleton bridge charges its
clock by at least ``1/3`` and preserves the common ``1/12`` constant.

This is an exact finite-block certificate inside the already constructed
five-mask atlas.  It does not prove that atlas exhaustive for the full game,
and it does not cover zero hazards, nonperiodic boundary limits, or supports
outside ``{1,2,3,6,9}``.
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
import block_pair_r0_singleton_bridge_ranks as singleton_bridge  # noqa: E402
import block_pair_r0_support3_clock_charge as one_phase  # noqa: E402
import block_pair_r0_support3_endpoint_rank as endpoint  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_support9_run_rank import bernstein_coefficients  # noqa: E402


Q = Fraction
one = algebra.one


def assert_support_three_self_transport() -> None:
    """Replay the self maps and the monotone hazard/ratio packet."""

    e = algebra.var(0)
    f = algebra.var(1)
    e_next = support_three_run.rat_scale(
        3, support_three_run.odds(support_three_run.rat(e))
    )
    f_next = support_three_run.rat_scale(
        Q(900, 311), support_three_run.odds(support_three_run.rat(f))
    )

    expected_e_increment = algebra.mul(
        e, algebra.add(algebra.const(2), e)
    )
    expected_f_increment = algebra.mul(
        f,
        algebra.add(algebra.const(Q(589, 311)), f),
    )
    endpoint.rat_equal(
        endpoint.rat_sub(e_next, endpoint.rat(e)),
        expected_e_increment,
        algebra.sub(one, e),
    )
    endpoint.rat_equal(
        endpoint.rat_sub(f_next, endpoint.rat(f)),
        expected_f_increment,
        algebra.sub(one, f),
    )

    # Exact ratio identity:
    #   (f'/e')/(f/e) = (300/311)*(1-e)/(1-f).
    # Initially f/e<100/311<1.  Hence f<e, the last factor is below one,
    # and the ratio strictly decreases at every strict self transition.
    ratio_left = endpoint.rat_mul(f_next, endpoint.rat(e))
    ratio_right = endpoint.rat_mul(e_next, endpoint.rat(f))
    ratio_quotient = endpoint.RationalPoly(
        algebra.mul(ratio_left.numerator, ratio_right.denominator),
        algebra.mul(ratio_left.denominator, ratio_right.numerator),
    )
    endpoint.rat_equal(
        ratio_quotient,
        algebra.scale(Q(300, 311), algebra.sub(one, e)),
        algebra.sub(one, f),
    )
    assert Q(100, 311) < 1


def threshold_polynomials() -> tuple[algebra.Poly, algebra.Poly]:
    e = algebra.var(0)
    f = algebra.var(1)
    numerator = algebra.sum_polys(
        [
            algebra.scale(1701, e),
            algebra.scale(-3501, algebra.mul(e, f)),
            algebra.scale(1800, f),
        ]
    )
    denominator = algebra.mul(
        algebra.sub(one, f),
        algebra.add(algebra.scale(1979, e), algebra.const(622)),
    )
    return numerator, denominator


def assert_endpoint_threshold_monotonicity() -> None:
    """Certify coordinate monotonicity of R=N/D on the run box."""

    e = algebra.var(0)
    f = algebra.var(1)
    numerator, denominator = threshold_polynomials()

    derivative_e_numerator = algebra.sub(
        algebra.mul(endpoint.derivative(numerator, 0), denominator),
        algebra.mul(numerator, endpoint.derivative(denominator, 0)),
    )
    expected_e = algebra.scale(
        162,
        algebra.mul(
            algebra.sub(algebra.const(6531), algebra.scale(35431, f)),
            algebra.sub(one, f),
        ),
    )
    assert derivative_e_numerator == expected_e

    derivative_f_numerator = algebra.sub(
        algebra.mul(endpoint.derivative(numerator, 1), denominator),
        algebra.mul(numerator, endpoint.derivative(denominator, 1)),
    )
    expected_f = algebra.scale(
        1800,
        algebra.mul(
            algebra.sub(one, e),
            algebra.add(algebra.scale(1979, e), algebra.const(622)),
        ),
    )
    assert derivative_f_numerator == expected_f

    # The last support-3 coordinate satisfies e_last<2/11.  Ratio decay
    # from f_first/e_first<100/311 gives the uniform run bounds below.
    f_upper = Q(100, 311) * Q(2, 11)
    assert f_upper == Q(200, 3421)
    assert f_upper < Q(6531, 35431)
    assert Q(2, 11) < 1

    # The denominator is positive on that box, and both cross-multiplied
    # derivative numerators are positive there.  Thus R rises along every
    # finite strict support-3 run.
    assert Q(622) > 0


def assert_tail_value_charge() -> None:
    """Charge the tail removed by the virtual one-phase comparison."""

    assert tuple(terminal(mask, 2) for mask in (1, 2, 3)) == (0, 0, -1)

    k = algebra.var(0)  # survival through support 9 and the first 3 phase
    tail = algebra.var(1)  # survival through the remaining 3 block
    endpoint_hazard = algebra.var(2)
    loss = algebra.var(3)  # nonnegative magnitude of tail absorption reward

    endpoint_value = algebra.add(
        algebra.const(2), algebra.scale(4, endpoint_hazard)
    )
    direct_minus_actual = algebra.mul(
        k,
        algebra.add(
            algebra.mul(algebra.sub(one, tail), endpoint_value),
            loss,
        ),
    )
    lower_value_loss = algebra.scale(
        2, algebra.mul(k, algebra.sub(one, tail))
    )
    assert algebra.sub(direct_minus_actual, lower_value_loss) == algebra.mul(
        k,
        algebra.add(
            algebra.scale(
                4,
                algebra.mul(
                    algebra.sub(one, tail), endpoint_hazard
                ),
            ),
            loss,
        ),
    )

    # The exact conversion h(V)=(V-2)/(V+4) has difference
    #   h(Vd)-h(Va)=6(Vd-Va)/((Vd+4)(Va+4)).
    actual_value = algebra.var(4)
    direct_value = algebra.var(5)
    conversion_numerator = algebra.sub(
        algebra.mul(
            algebra.sub(direct_value, algebra.const(2)),
            algebra.add(actual_value, algebra.const(4)),
        ),
        algebra.mul(
            algebra.sub(actual_value, algebra.const(2)),
            algebra.add(direct_value, algebra.const(4)),
        ),
    )
    assert conversion_numerator == algebra.scale(
        6, algebra.sub(direct_value, actual_value)
    )

    # Both values lie in [2,8]: the lower bound is their support-6 active
    # representation, while 8 is player 2's global terminal-payoff maximum.
    assert max(terminal(mask, 2) for mask in range(1, 16)) == 8
    va_unit = algebra.var(0)
    vd_unit = algebra.var(1)
    va_scaled = algebra.add(algebra.const(2), algebra.scale(6, va_unit))
    vd_scaled = algebra.add(algebra.const(2), algebra.scale(6, vd_unit))
    denominator_slack = algebra.sub(
        algebra.const(144),
        algebra.mul(
            algebra.add(va_scaled, algebra.const(4)),
            algebra.add(vd_scaled, algebra.const(4)),
        ),
    )
    coefficients = bernstein_coefficients(
        denominator_slack, variables=(0, 1), degrees=(1, 1)
    )
    assert coefficients == {
        (0, 0): Q(108),
        (0, 1): Q(72),
        (1, 0): Q(72),
        (1, 1): Q(0),
    }

    # Consequently the hazard loss is at least 1/24 of the value loss,
    # hence at least (1/12)k(1-tail).
    assert Q(6, 144) == Q(1, 24)
    assert Q(1, 24) * 2 == Q(1, 12)


def assert_pair_block_charge_composition() -> None:
    """Compose the virtual first-phase and tail clock charges."""

    k = algebra.var(0)
    tail = algebra.var(1)
    virtual_charge = algebra.scale(Q(1, 2), algebra.sub(one, k))
    tail_charge = algebra.scale(
        Q(1, 12), algebra.mul(k, algebra.sub(one, tail))
    )
    total_charge = algebra.scale(
        Q(1, 12), algebra.sub(one, algebra.mul(k, tail))
    )
    assert algebra.sub(
        algebra.add(virtual_charge, tail_charge), total_charge
    ) == algebra.scale(Q(5, 12), algebra.sub(one, k))


def assert_singleton_prefix_charge() -> None:
    """Compose an optional nonempty support-2 prefix with the pair block."""

    singleton_bridge.assert_support_two_effective_hazard_rank()
    a = algebra.var(0)
    h = algebra.var(1)
    pair_absorption = algebra.var(2)

    # The bridge numerator factor is >=1 for 0<=a<=1/2, and its
    # denominator is <=3.  The upper bound follows because its effective
    # endpoint value is at most player 2's global maximum 8, equivalently
    # the effective hazard is at most 1/2, and x>=a.
    numerator_factor = algebra.mul(
        algebra.sub(one, a), algebra.add(one, algebra.scale(2, a))
    )
    assert algebra.sub(numerator_factor, one) == algebra.mul(
        a, algebra.sub(one, algebra.scale(2, a))
    )
    denominator = algebra.sub(
        algebra.const(3),
        algebra.scale(2, algebra.mul(h, algebra.sub(one, a))),
    )
    assert algebra.sub(algebra.const(3), denominator) == algebra.scale(
        2, algebra.mul(h, algebra.sub(one, a))
    )

    prefix_charge = algebra.scale(Q(1, 3), h)
    pair_charge = algebra.scale(Q(1, 12), pair_absorption)
    total_absorption = algebra.add(
        h,
        algebra.mul(algebra.sub(one, h), pair_absorption),
    )
    target_charge = algebra.scale(Q(1, 12), total_absorption)
    assert algebra.sub(
        algebra.add(prefix_charge, pair_charge), target_charge
    ) == algebra.scale(
        Q(1, 12),
        algebra.mul(h, algebra.add(algebra.const(3), pair_absorption)),
    )


def assert_arbitrary_support_three_block_charge() -> None:
    """Replay all exact ingredients of the finite-block induction."""

    core, denominator = one_phase.assert_reduced_identity()
    one_phase.assert_bernstein_signs(core, denominator)
    one_phase.assert_monotonicity_packet()
    support_three_run.inserted_hazards()
    assert_support_three_self_transport()
    assert_endpoint_threshold_monotonicity()
    assert_tail_value_charge()
    assert_pair_block_charge_composition()
    assert_singleton_prefix_charge()


def main() -> None:
    assert_arbitrary_support_three_block_charge()

    print("exact arbitrary support-3 block clock charge passed")
    print("6->9->3+->6 has A-a >= (1/12)*(one minus survival)")
    print("the same bound survives an optional nonempty support-2 prefix")
    print("both remaining strict five-mask 6-return families are ranked")
    print("scope: finite strict five-mask atlas; boundary/full-atlas open")


if __name__ == "__main__":
    main()
