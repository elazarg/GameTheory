#!/usr/bin/env python3
"""Endpoint-credible hazard rank for ``6 -> 9 -> 6``.

Consider three consecutive strict phases in the perturbed block-pair quitting
game,

    support 6  ->  support 9  ->  support 6.

Write ``a`` for player 1's hazard at the first support-6 phase, ``c,d`` for
players 0 and 3 at support 9, and ``A,B`` for players 1 and 2 at the second
support-6 phase.  Unlike the older alternating-support rank, this theorem
does not prescribe the support after the second 6.  It assumes only that the
second support-6 phase itself satisfies player 0's inactive Nash inequality
against its actual successor continuation.  Then

    A > a.

The proof uses four exact local facts.  Player 1's first support-6 equality
eliminates B.  Player 1's inactive support-9 inequality gives ``4d<=3c``.
Active player 0 at support 9 fixes player 0's value at the second support 6;
player 0's inactive inequality there then gives

    A >= Num(c,d)/Den(c,d),

where both numerator and denominator are positive on ``4d<=3c``.  Finally a
quadratic transfer polynomial ``T(A,c,d)`` is strictly increasing in A, and
an exact degree-(5,3) Bernstein certificate proves

    T(Num/Den,c,d) > 0.

The remaining active equality identifies the sign of T with the sign of
``A-a``.  No periodic closing equation and no next-support label is used.

Scope: this is a finite local transfer lemma.  It says nothing by itself
about nonperiodic boundary convergence, zero-hazard limits, longer support-9
runs, or excursions through another support.
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


Q = Fraction
a, A, B, c, d, _ = (
    algebra.a,
    algebra.A,
    algebra.b,
    algebra.c,
    algebra.d,
    algebra.C,
)
one = algebra.one
Poly = algebra.Poly


def assert_payoff_origin() -> None:
    # Support 9, prescribed and deviating player-1/player-2 packets.
    assert tuple(terminal(mask, 1) for mask in (1, 8, 9)) == (8, 0, 3)
    assert tuple(terminal(mask, 2) for mask in (1, 8, 9)) == (0, 8, 5)
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)

    # Active player 0 at support 9 has successor coefficient -1.
    assert (terminal(1, 0), terminal(8, 0), terminal(9, 0)) == (
        Q(-189, 100),
        -4,
        -6,
    )

    # Player 0's Quit packet against support 6 at the endpoint.
    assert tuple(terminal(mask, 0) for mask in (1, 3, 5, 7)) == (
        Q(-189, 100),
        -5,
        0,
        -6,
    )


def local_polynomials() -> tuple[Poly, Poly, Poly, Poly, Poly, Poly, Poly]:
    """Return ``E1,E2,D0cleared,N,Den,Num,T``."""

    one_minus_a = algebra.sub(one, a)
    one_minus_A = algebra.sub(one, A)
    one_minus_B = algebra.sub(one, B)
    one_minus_c = algebra.sub(one, c)
    one_minus_d = algebra.sub(one, d)
    survival = algebra.mul(one_minus_c, one_minus_d)

    # The support-9 current value of player 1 is 2.  Subtracting 2 gives E1.
    current_one = algebra.sum_polys(
        [
            algebra.scale(8, algebra.mul(c, one_minus_d)),
            algebra.scale(3, algebra.mul(c, d)),
            algebra.mul(survival, algebra.sub(algebra.const(2), algebra.scale(2, B))),
        ]
    )
    e1 = algebra.sub(current_one, algebra.const(2))
    expected_e1 = algebra.sub(
        algebra.sum_polys(
            [algebra.scale(6, c), algebra.scale(-2, d), algebra.scale(-3, algebra.mul(c, d))]
        ),
        algebra.scale(2, algebra.mul(survival, B)),
    )
    assert e1 == expected_e1

    # The support-9 current value of player 2 equals the successor value
    # required by player 2's mixing at the first support 6.  Multiply by
    # 1-a to clear the latter value's denominator.
    current_two_offset = algebra.sum_polys(
        [
            algebra.scale(8, algebra.mul(d, one_minus_c)),
            algebra.scale(5, algebra.mul(c, d)),
            algebra.mul(survival, algebra.add(algebra.const(2), algebra.scale(4, A))),
            algebra.const(-2),
        ]
    )
    e2 = algebra.sub(
        algebra.mul(one_minus_a, current_two_offset),
        algebra.scale(6, a),
    )
    k = algebra.sum_polys(
        [algebra.scale(-1, algebra.mul(c, d)), algebra.scale(-2, c), algebra.scale(6, d)]
    )
    assert current_two_offset == algebra.add(k, algebra.scale(4, algebra.mul(survival, A)))

    # At the endpoint support 6, player 0's current value is fixed by its
    # active equality one phase earlier: q_0-2d/(1-d).  Its Quit payoff there
    # is the expectation of the four cells below.  Clear 100(1-d).
    q0 = algebra.const(Q(-189, 100))
    endpoint_quit_zero = algebra.sum_polys(
        [
            algebra.mul(q0, algebra.mul(one_minus_A, one_minus_B)),
            algebra.scale(-5, algebra.mul(A, one_minus_B)),
            algebra.scale(-6, algebra.mul(A, B)),
        ]
    )
    d0_cleared = algebra.add(
        algebra.scale(
            100,
            algebra.mul(one_minus_d, algebra.sub(endpoint_quit_zero, q0)),
        ),
        algebra.scale(200, d),
    )

    den = algebra.sum_polys(
        [
            algebra.const(622),
            algebra.scale(1112, c),
            algebra.scale(-1200, d),
            algebra.scale(-245, algebra.mul(c, d)),
        ]
    )
    num = algebra.sum_polys(
        [
            algebra.scale(1134, c),
            algebra.scale(22, d),
            algebra.scale(-967, algebra.mul(c, d)),
        ]
    )
    endpoint_numerator = algebra.sub(num, algebra.mul(A, den))

    # On E1=0, 2(1-c)D0cleared is exactly Num-A*Den.
    assert algebra.sub(
        algebra.sub(
            algebra.scale(2, algebra.mul(one_minus_c, d0_cleared)),
            endpoint_numerator,
        ),
        algebra.mul(algebra.sub(algebra.scale(289, A), algebra.const(189)), e1),
    ) == {}

    # T=(1-A)[2+6A/(1-A)-V_1^2], with its only denominator cleared.
    linear = algebra.sum_polys(
        [
            algebra.scale(-5, algebra.mul(c, d)),
            algebra.scale(2, c),
            algebra.scale(10, d),
            algebra.const(2),
        ]
    )
    constant = algebra.sum_polys(
        [algebra.mul(c, d), algebra.scale(2, c), algebra.scale(-6, d)]
    )
    transfer = algebra.sum_polys(
        [
            algebra.scale(4, algebra.mul(survival, algebra.mul(A, A))),
            algebra.mul(linear, A),
            constant,
        ]
    )

    # Under E2=0, (1-a)T=6(A-a), so T has exactly the desired sign.
    assert algebra.sub(
        algebra.sub(
            algebra.mul(one_minus_a, transfer),
            algebra.scale(6, algebra.sub(A, a)),
        ),
        algebra.mul(algebra.sub(A, one), e2),
    ) == {}

    return e1, e2, d0_cleared, endpoint_numerator, den, num, transfer


def assert_clock_coefficients(den: Poly, num: Poly, transfer: Poly) -> None:
    """Prove threshold positivity on ``d=(3/4)c*r``, 0<=c,r<=1."""

    den_coefficients = algebra.bivariate_bernstein(
        algebra.substitute_clock(den), 2, 1
    )
    assert den_coefficients == (
        (Q(622), Q(622)),
        (Q(1178), Q(728)),
        (Q(1734), Q(2601, 4)),
    )
    assert all(value > 0 for row in den_coefficients for value in row)

    clock_num = algebra.substitute_clock(num)
    reduced_num = {}
    for (c_degree, r_degree), coefficient in clock_num.items():
        assert c_degree >= 1
        reduced_num[c_degree - 1, r_degree] = coefficient
    num_coefficients = algebra.bivariate_bernstein(reduced_num, 1, 1)
    assert num_coefficients == (
        (Q(1134), Q(2301, 2)),
        (Q(1134), Q(1701, 4)),
    )
    assert all(value > 0 for row in num_coefficients for value in row)

    survival = algebra.mul(algebra.sub(one, c), algebra.sub(one, d))
    linear = algebra.sum_polys(
        [
            algebra.scale(-5, algebra.mul(c, d)),
            algebra.scale(2, c),
            algebra.scale(10, d),
            algebra.const(2),
        ]
    )
    # dT/dA=8*s*A+linear, and both summands are positive.  The exact
    # Bernstein table proves positivity of the nontrivial second summand.
    linear_coefficients = algebra.bivariate_bernstein(
        algebra.substitute_clock(linear), 2, 1
    )
    assert linear_coefficients == (
        (Q(2), Q(2)),
        (Q(3), Q(27, 4)),
        (Q(4), Q(31, 4)),
    )
    assert all(value > 0 for row in linear_coefficients for value in row)

    constant = algebra.sum_polys(
        [algebra.mul(c, d), algebra.scale(2, c), algebra.scale(-6, d)]
    )
    threshold_numerator = algebra.sum_polys(
        [
            algebra.scale(4, algebra.mul(survival, algebra.mul(num, num))),
            algebra.mul(linear, algebra.mul(num, den)),
            algebra.mul(constant, algebra.mul(den, den)),
        ]
    )

    # This is Den^2*T(Num/Den).  After the clock substitution it has a
    # positive factor c.  Remove c and certify the remaining rectangle.
    clock_threshold = algebra.substitute_clock(threshold_numerator)
    reduced_threshold = {}
    for (c_degree, r_degree), coefficient in clock_threshold.items():
        assert c_degree >= 1
        reduced_threshold[c_degree - 1, r_degree] = coefficient
    coefficients = algebra.bivariate_bernstein(reduced_threshold, 5, 3)
    expected = (
        (Q(2184464), Q(1610980), Q(1037496), Q(464012)),
        (Q(22765512, 5), Q(18024624, 5), Q(29958513, 10), Q(27258819, 10)),
        (Q(34534344, 5), Q(49940557, 10), Q(151628783, 40), Q(11684565, 4)),
        (Q(46228816, 5), Q(29523354, 5), Q(156959893, 40), Q(414175679, 160)),
        (Q(57848928, 5), Q(32315341, 5), Q(147355777, 40), Q(324463959, 160)),
        (Q(13878936), Q(6795546), Q(25159473, 8), Q(22449231, 16)),
    )
    assert coefficients == expected
    assert min(value for row in coefficients for value in row) == Q(464012)

    # Keep the symbolic transfer itself live in this checker: its quadratic
    # coefficient is exactly 4*survival and the expression reconstructed
    # above is Den^2*T(Num/Den).
    assert transfer == algebra.sum_polys(
        [
            algebra.scale(4, algebra.mul(survival, algebra.mul(A, A))),
            algebra.mul(linear, A),
            constant,
        ]
    )


def assert_inactive_clock() -> None:
    # At support 9, player 1's Quit payoff minus its current value 2 is
    # exactly -3c+4d.  Its inactive Nash inequality therefore supplies the
    # substitution d=(3/4)c*r with r in (0,1].
    one_minus_c = algebra.sub(one, c)
    one_minus_d = algebra.sub(one, d)
    quit_one = algebra.sum_polys(
        [
            algebra.scale(2, algebra.mul(one_minus_c, one_minus_d)),
            algebra.scale(-1, algebra.mul(c, one_minus_d)),
            algebra.scale(6, algebra.mul(one_minus_c, d)),
            algebra.scale(3, algebra.mul(c, d)),
        ]
    )
    assert algebra.sub(quit_one, algebra.const(2)) == algebra.add(
        algebra.scale(-3, c), algebra.scale(4, d)
    )


def main() -> None:
    assert_payoff_origin()
    _, _, _, _, den, num, transfer = local_polynomials()
    assert_inactive_clock()
    assert_clock_coefficients(den, num, transfer)
    assert_credible_first_unchanged()

    print("exact endpoint-credible support 6->9->6 rank passed")
    print("local invariant: second player-1 hazard A is strictly > first a")
    print("outgoing support after the second 6 is unrestricted")
    print("threshold Bernstein minimum = 464012")
    print("scope: finite strict local transfer; nonperiodic boundaries remain")


if __name__ == "__main__":
    main()
