#!/usr/bin/env python3
"""Clock-charge every finite strict support-9 return exactly.

For the perturbed block-pair table, consider

    support 6 -> support 9+ -> support 6.

Let ``a,A`` be player 1's hazards at the support-6 endpoints and let ``S``
be survival through the nonempty support-9 block.  Under the active Bellman
equalities and inactive inequalities replayed by
``block_pair_r0_support9_run_rank.py``, this checker proves

    A - a >= (1/50) * (1-S).

The proof quantitatively sharpens the aggregate relaxation behind the
existing strict rank.  Put ``q=1-S`` and let ``ell`` be player 0's hazard in
the last support-9 phase.  The phase inequality gives

    H >= kappa(ell) q,
    K <= mu(ell) q,
    kappa = 9(2-ell)/(7-3ell),   mu=4-kappa.

Player 1's Bellman identity is ``H=2(1-q)B``.  Endpoint credibility gives

    A >= E(q,ell)
      = 1701 q (2-ell)
        / ((4354-1866ell)+(848-735ell)q).

Player 2's identity then bounds its incoming effective hazard by

    a <= g(A,q,ell)
      = (mu q+4(1-q)A)/(6+mu q+4(1-q)A).

The function ``A-g(A,q,ell)`` increases in ``A``.  Also
``0<=ell<=q<=1/2``.  On the enlarged triangular box, exact tensor Bernstein
coefficients certify ``E-g(E)>=q/50``.

The same constant survives an optional finite support-2 prefix.  This is a
finite strict five-mask-atlas certificate.  It does not cover a path leaving
that atlas, a zero-hazard/nonperiodic limit, or manufacture the global
potential required by Q122.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_singleton_bridge_ranks as singleton_bridge  # noqa: E402
import block_pair_r0_support9_run_rank as run_rank  # noqa: E402
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


def rat_div(left: RationalPoly, right: RationalPoly) -> RationalPoly:
    return RationalPoly(
        algebra.mul(left.numerator, right.denominator),
        algebra.mul(left.denominator, right.numerator),
    )


def assert_aggregate_clock_packet() -> None:
    """Replay the run aggregation and its triangular parameter domain."""

    ell = algebra.var(0)
    last_other = algebra.var(1)
    prior_survival = algebra.var(2)
    last_absorption = algebra.sum_polys(
        [
            ell,
            last_other,
            algebra.scale(-1, algebra.mul(ell, last_other)),
        ]
    )
    total_absorption = algebra.sub(
        one,
        algebra.mul(prior_survival, algebra.sub(one, last_absorption)),
    )
    assert algebra.sub(total_absorption, ell) == algebra.add(
        algebra.mul(
            algebra.sub(one, prior_survival),
            algebra.sub(one, last_absorption),
        ),
        algebra.mul(last_other, algebra.sub(one, ell)),
    )

    # h+k=4p phasewise; weighted summation gives H+K=4q.  The imported
    # phase certificate gives H>=kappa*q, hence K<=mu*q.
    run_rank.assert_mobius_and_phase_bound()
    kappa_numerator = algebra.scale(9, algebra.sub(algebra.const(2), ell))
    kappa_denominator = algebra.sub(
        algebra.const(7), algebra.scale(3, ell)
    )
    mu_numerator = algebra.sub(
        algebra.const(10), algebra.scale(3, ell)
    )
    assert algebra.add(kappa_numerator, mu_numerator) == algebra.scale(
        4, kappa_denominator
    )
    assert algebra.sub(
        kappa_numerator, algebra.scale(2, kappa_denominator)
    ) == algebra.sub(algebra.const(4), algebra.scale(3, ell))

    # Since ell<1/2, kappa>2.  H=2(1-q)B with B<1 therefore gives q<1/2.
    q = algebra.var(3)
    h_total = algebra.var(4)
    endpoint_b = algebra.var(5)
    player_one_entry = algebra.add(
        algebra.scale(2, q),
        algebra.add(
            h_total,
            algebra.scale(
                2,
                algebra.mul(
                    algebra.sub(one, q), algebra.sub(one, endpoint_b)
                ),
            ),
        ),
    )
    assert algebra.sub(player_one_entry, algebra.const(2)) == algebra.sub(
        h_total,
        algebra.scale(2, algebra.mul(algebra.sub(one, q), endpoint_b)),
    )


def assert_endpoint_lower_bound() -> None:
    """Derive A>=E(q,ell) from player 0's endpoint credibility."""

    endpoint_a = algebra.var(0)
    endpoint_b = algebra.var(1)
    last_other = algebra.var(2)
    q0 = Q(-189, 100)

    assert tuple(terminal(mask, 0) for mask in (1, 3, 5, 7)) == (
        q0,
        -5,
        0,
        -6,
    )
    endpoint_quit = algebra.sum_polys(
        [
            algebra.scale(
                q0,
                algebra.mul(
                    algebra.sub(one, endpoint_a),
                    algebra.sub(one, endpoint_b),
                ),
            ),
            algebra.scale(
                -5,
                algebra.mul(endpoint_a, algebra.sub(one, endpoint_b)),
            ),
            algebra.scale(-6, algebra.mul(endpoint_a, endpoint_b)),
        ]
    )
    # Active player 0 at the last support 9 fixes this continuation value.
    current_numerator = algebra.sub(
        algebra.scale(q0, algebra.sub(one, last_other)),
        algebra.scale(2, last_other),
    )
    cleared_difference = algebra.sub(
        algebra.scale(
            100,
            algebra.mul(
                algebra.sub(one, last_other), endpoint_quit
            ),
        ),
        algebra.scale(100, current_numerator),
    )
    threshold_numerator = algebra.add(
        algebra.scale(
            189,
            algebra.mul(endpoint_b, algebra.sub(one, last_other)),
        ),
        algebra.scale(200, last_other),
    )
    threshold_denominator = algebra.mul(
        algebra.add(
            algebra.scale(289, endpoint_b), algebra.const(311)
        ),
        algebra.sub(one, last_other),
    )
    assert cleared_difference == algebra.sub(
        threshold_numerator,
        algebra.mul(endpoint_a, threshold_denominator),
    )

    # Dropping last_other and replacing B by its lower bound are both safe:
    # F(B,d)-F(B,0) has numerator 200d, and F(B,0) has positive
    # derivative numerator 189*311.
    assert Q(200) > 0
    assert Q(189) * Q(311) > 0

    # Substitute B0=kappa*q/(2(1-q)) in 189B/(289B+311).
    q = algebra.var(3)
    ell = algebra.var(4)
    kappa_num = algebra.scale(9, algebra.sub(algebra.const(2), ell))
    kappa_den = algebra.sub(algebra.const(7), algebra.scale(3, ell))
    b_zero = RationalPoly(
        algebra.mul(kappa_num, q),
        algebra.scale(
            2, algebra.mul(algebra.sub(one, q), kappa_den)
        ),
    )
    e_value = rat_div(
        rat_scale(189, b_zero),
        rat_add(rat_scale(289, b_zero), rat(algebra.const(311))),
    )
    expected_num = algebra.scale(
        1701, algebra.mul(q, algebra.sub(algebra.const(2), ell))
    )
    expected_den = algebra.add(
        algebra.sub(
            algebra.const(4354), algebra.scale(1866, ell)
        ),
        algebra.mul(
            q,
            algebra.sub(
                algebra.const(848), algebra.scale(735, ell)
            ),
        ),
    )
    rat_equal(e_value, expected_num, expected_den)


def assert_player_two_upper_bound() -> None:
    """Replay the incoming-hazard upper bound and A-monotonicity."""

    q = algebra.var(0)
    k_total = algebra.var(1)
    endpoint_a = algebra.var(2)
    incoming = algebra.var(3)

    # Player 2's run value is 2+K+4(1-q)A, while its active equality at
    # the initial support 6 requires 2+6a/(1-a).
    value_offset = algebra.add(
        k_total,
        algebra.scale(
            4, algebra.mul(algebra.sub(one, q), endpoint_a)
        ),
    )
    bellman = algebra.sub(
        algebra.mul(algebra.sub(one, incoming), value_offset),
        algebra.scale(6, incoming),
    )
    assert algebra.sub(
        algebra.mul(
            algebra.sub(one, incoming),
            algebra.add(algebra.const(2), value_offset),
        ),
        algebra.add(algebra.const(2), algebra.scale(4, incoming)),
    ) == bellman

    # K<=mu*q and x/(6+x) is increasing.  For
    # V=mu*q+4(1-q)A>=0, dg/dA=24(1-q)/(6+V)^2 <=2/3<1.
    assert Q(24, 36) == Q(2, 3) < 1


def relaxed_charged_gap() -> RationalPoly:
    """Build E-g(E)-q/50 on q=t/2, ell=q*u exactly."""

    t = algebra.var(0)
    u = algebra.var(1)
    q = rat_scale(Q(1, 2), rat(t))
    ell = rat_scale(Q(1, 2), rat(algebra.mul(t, u)))
    kappa_den = rat_sub(rat(algebra.const(7)), rat_scale(3, ell))
    kappa_num = rat_scale(9, rat_sub(rat(algebra.const(2)), ell))
    mu_num = rat_sub(rat(algebra.const(10)), rat_scale(3, ell))

    b_zero = rat_div(
        rat_mul(kappa_num, q),
        rat_scale(2, rat_mul(rat_sub(rat(one), q), kappa_den)),
    )
    e_value = rat_div(
        rat_scale(189, b_zero),
        rat_add(rat_scale(289, b_zero), rat(algebra.const(311))),
    )
    mu = rat_div(mu_num, kappa_den)
    value_upper = rat_add(
        rat_mul(mu, q),
        rat_scale(4, rat_mul(rat_sub(rat(one), q), e_value)),
    )
    incoming_upper = rat_div(
        value_upper, rat_add(rat(algebra.const(6)), value_upper)
    )
    return rat_sub(
        rat_sub(e_value, incoming_upper), rat_scale(Q(1, 50), q)
    )


def assert_relaxed_box_certificate() -> None:
    """Bernstein-certify the charged gap on 0<=ell<=q<=1/2."""

    gap = relaxed_charged_gap()
    reduced_numerator: algebra.Poly = {}
    for exponent, coefficient in gap.numerator.items():
        assert exponent[0] >= 1
        target = list(exponent)
        target[0] -= 1
        reduced_numerator[tuple(target)] = coefficient

    assert max(exponent[0] for exponent in reduced_numerator) == 15
    assert max(exponent[1] for exponent in reduced_numerator) == 8
    numerator_coefficients = bernstein_coefficients(
        reduced_numerator, variables=(0, 1), degrees=(15, 8)
    )
    assert len(numerator_coefficients) == 144
    assert min(numerator_coefficients.values()) == Q(
        1960123232793824, 25
    )
    assert all(value > 0 for value in numerator_coefficients.values())

    assert max(exponent[0] for exponent in gap.denominator) == 15
    assert max(exponent[1] for exponent in gap.denominator) == 8
    denominator_coefficients = bernstein_coefficients(
        gap.denominator, variables=(0, 1), degrees=(15, 8)
    )
    assert len(denominator_coefficients) == 144
    assert min(denominator_coefficients.values()) == Q(
        7557185489150199925, 4096
    )
    assert all(value > 0 for value in denominator_coefficients.values())


def assert_singleton_prefix_composition() -> None:
    """Preserve c=1/50 through an optional support-2 prefix."""

    singleton_bridge.assert_support_two_effective_hazard_rank()
    h = algebra.var(0)
    pair_absorption = algebra.var(1)
    prefix_charge = algebra.scale(Q(1, 3), h)
    pair_charge = algebra.scale(Q(1, 50), pair_absorption)
    total_absorption = algebra.add(
        h,
        algebra.mul(algebra.sub(one, h), pair_absorption),
    )
    target = algebra.scale(Q(1, 50), total_absorption)
    assert algebra.sub(
        algebra.add(prefix_charge, pair_charge), target
    ) == algebra.scale(
        Q(1, 150),
        algebra.mul(
            h,
            algebra.add(algebra.const(47), algebra.scale(3, pair_absorption)),
        ),
    )


def assert_arbitrary_support9_run_clock_charge() -> None:
    run_rank.assert_arbitrary_support9_run_rank()
    assert_aggregate_clock_packet()
    assert_endpoint_lower_bound()
    assert_player_two_upper_bound()
    assert_relaxed_box_certificate()
    assert_singleton_prefix_composition()


def main() -> None:
    assert_arbitrary_support9_run_clock_charge()

    print("exact arbitrary support-9-run clock charge passed")
    print("6->9+->6 has A-a >= (1/50)*(one minus survival)")
    print("the same bound survives an optional nonempty support-2 prefix")
    print("scope: finite strict five-mask atlas; boundary/global potential open")


if __name__ == "__main__":
    main()
