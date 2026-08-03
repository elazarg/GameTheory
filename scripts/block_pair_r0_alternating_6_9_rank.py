#!/usr/bin/env python3
"""Exact hazard rank for every strictly alternating support-6/9 cycle.

This is the perturbed block-pair quitting game with
``r_0({0})=-2+11/100``.  Consider four consecutive strict-support phases

    support 6  ->  support 9  ->  support 6  ->  support 9.

Write ``a`` for player 1's hazard at the first support-6 phase, ``c,d`` for
players 0 and 3's hazards at the intervening support-9 phase, ``A,b`` for
players 1 and 2's hazards at the next support-6 phase, and ``C`` for player
0's hazard at the following support-9 phase.  All six hazards lie in
``(0,1)``.

The exact Bellman recurrences ``E1,E2,E3`` below and player 1's inactive Nash
inequality at support 9 imply the strict rank

    A > a.

The proof is algebraic.  Assuming ``A <= a``, ``E2`` gives ``N(a,c,d)<=0``.
Eliminating ``b`` with ``E1``, positivity of ``C`` in ``E3`` demands
``T(A)>0``.  But ``4d<=3c`` makes ``T`` increasing in ``A`` and an exact
Bernstein certificate proves ``T(a)<0`` whenever ``N<=0``.  This is a
contradiction.

Consequently player 1's support-6 hazard strictly increases at every
support-6/support-9 block.  No finite cyclic profile can therefore have a
strictly alternating support word over ``{6,9}``, at any even period and even
when all hazards vary by phase.

Scope is important: the checker does not cover two or more consecutive
support-9 phases, excursions through another support, nonperiodic paths, or
zero-hazard hybrids.  Constant support-6 repetition and boundary hazards are
covered by separate exact certificates.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
NVARS = 6
Exp = tuple[int, ...]
Poly = dict[Exp, Fraction]
Bivariate = dict[tuple[int, int], Fraction]
ZERO_EXP: Exp = (0,) * NVARS


def const(value: int | Fraction) -> Poly:
    value = Q(value)
    return {} if value == 0 else {ZERO_EXP: value}


def var(index: int) -> Poly:
    exponent = [0] * NVARS
    exponent[index] = 1
    return {tuple(exponent): Q(1)}


def add(left: Poly, right: Poly) -> Poly:
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, Q(0)) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def neg(poly: Poly) -> Poly:
    return {exponent: -coefficient for exponent, coefficient in poly.items()}


def sub(left: Poly, right: Poly) -> Poly:
    return add(left, neg(right))


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
            exponent = tuple(
                left_exp[index] + right_exp[index] for index in range(NVARS)
            )
            result[exponent] = (
                result.get(exponent, Q(0))
                + left_coefficient * right_coefficient
            )
    return {
        exponent: coefficient
        for exponent, coefficient in result.items()
        if coefficient != 0
    }


def sum_polys(terms: list[Poly]) -> Poly:
    result: Poly = {}
    for term in terms:
        result = add(result, term)
    return result


# Variable order: previous support-6 hazard a, next hazard A, its other
# hazard b, intervening support-9 hazards c,d, and following hazard C.
a, A, b, c, d, C = tuple(var(index) for index in range(NVARS))
one = const(1)


def assert_payoff_origin() -> None:
    """Replay every terminal cell used in the three recurrence packets."""

    # Support 6, active players 1 and 2.
    assert (terminal(2, 1), terminal(4, 1), terminal(6, 1)) == (2, 0, 0)
    assert (terminal(4, 2), terminal(2, 2), terminal(6, 2)) == (2, 0, 6)
    # Support 9, active player 3 and inactive players 1 and 2.
    assert (terminal(8, 3), terminal(1, 3), terminal(9, 3)) == (2, 0, 6)
    assert tuple(terminal(mask, 1) for mask in (1, 8, 9)) == (8, 0, 3)
    assert tuple(terminal(mask, 2) for mask in (1, 8, 9)) == (0, 8, 5)
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)
    # Support-6 recurrence for inactive player 3.
    assert tuple(terminal(mask, 3) for mask in (2, 4, 6)) == (0, 8, 3)


def recurrence_packet() -> tuple[Poly, Poly, Poly, Poly, Poly]:
    """Return ``E1,E2,E3,s,h`` in factored exact form."""

    one_minus_c = sub(one, c)
    one_minus_d = sub(one, d)
    survival = mul(one_minus_c, one_minus_d)
    h = sum_polys([scale(6, c), scale(-2, d), scale(-3, mul(c, d))])
    k = sum_polys([scale(-1, mul(c, d)), scale(-2, c), scale(6, d)])

    # Player 1 at support 9: current offset zero, successor offset -2b.
    e1 = sub(h, scale(2, mul(survival, b)))
    # Player 2 at support 9: current offset 6a/(1-a), successor 4A.
    e2 = sub(
        mul(sub(one, a), add(k, scale(4, mul(survival, A)))),
        scale(6, a),
    )
    # Player 3's value from the active support-9 phase must equal the value
    # generated at the following support-6 phase with successor hazard C.
    support_six_p3_offset = sum_polys(
        [
            scale(-3, mul(A, b)),
            scale(-2, A),
            scale(6, b),
            scale(4, mul(C, mul(sub(one, A), sub(one, b)))),
        ]
    )
    e3 = sub(mul(one_minus_c, support_six_p3_offset), scale(6, c))
    return e1, e2, e3, survival, h


def substitute_clock(poly: Poly) -> Bivariate:
    """Substitute ``d=(3/4)c*r`` into a polynomial using only c and d."""

    result: Bivariate = {}
    for exponent, coefficient in poly.items():
        assert all(exponent[index] == 0 for index in (0, 1, 2, 5))
        c_degree = exponent[3]
        d_degree = exponent[4]
        target = (c_degree + d_degree, d_degree)
        result[target] = (
            result.get(target, Q(0))
            + coefficient * Q(3, 4) ** d_degree
        )
    return {key: value for key, value in result.items() if value != 0}


def bivariate_bernstein(
    poly: Bivariate, c_degree: int, r_degree: int
) -> tuple[tuple[Fraction, ...], ...]:
    result = []
    for i in range(c_degree + 1):
        row = []
        for j in range(r_degree + 1):
            value = Q(0)
            for (power_c, power_r), coefficient in poly.items():
                if power_c <= i and power_r <= j:
                    value += coefficient * Q(
                        comb(i, power_c), comb(c_degree, power_c)
                    ) * Q(comb(j, power_r), comb(r_degree, power_r))
            row.append(value)
        result.append(tuple(row))
    return tuple(result)


def assert_clock_signs(
    f_coefficient: Poly, f_constant: Poly, n_linear: Poly
) -> None:
    """Prove the elementary coefficient signs on ``d<=3c/4``."""

    assert bivariate_bernstein(substitute_clock(f_coefficient), 2, 1) == (
        (Q(-4), Q(-4)),
        (Q(-11), Q(-29, 4)),
        (Q(-18), Q(-27, 4)),
    )
    assert bivariate_bernstein(substitute_clock(f_constant), 2, 1) == (
        (Q(0), Q(0)),
        (Q(12), Q(15, 2)),
        (Q(24), Q(21, 2)),
    )
    assert bivariate_bernstein(substitute_clock(n_linear), 2, 1) == (
        (Q(2), Q(2)),
        (Q(3), Q(27, 4)),
        (Q(4), Q(31, 4)),
    )


def assert_positive_threshold_numerator(
    survival: Poly,
    f_coefficient: Poly,
    f_constant: Poly,
    n_linear: Poly,
    n_constant: Poly,
) -> None:
    """Bernstein-prove ``N(-f_constant/f_coefficient)>0``."""

    numerator = sum_polys(
        [
            scale(4, mul(survival, mul(f_constant, f_constant))),
            scale(-1, mul(n_linear, mul(f_constant, f_coefficient))),
            mul(n_constant, mul(f_coefficient, f_coefficient)),
        ]
    )
    clock_numerator = substitute_clock(numerator)

    # The substituted numerator is c/64 times a degree-(5,3)
    # polynomial.  Remove that positive monomial and replay all of the
    # remaining tensor Bernstein coefficients exactly.
    reduced: Bivariate = {}
    for (c_degree, r_degree), coefficient in clock_numerator.items():
        assert 1 <= c_degree
        reduced[c_degree - 1, r_degree] = coefficient * 64
    expected = (
        (Q(14336), Q(11264), Q(8192), Q(5120)),
        (Q(288768, 5), Q(223488, 5), Q(33600), Q(122304, 5)),
        (Q(466176, 5), Q(340992, 5), Q(239856, 5), Q(163092, 5)),
        (Q(603904, 5), Q(419104, 5), Q(274408, 5), Q(172138, 5)),
        (Q(701952, 5), Q(468096, 5), Q(285864, 5), Q(164814, 5)),
        (Q(152064), Q(99648), Q(56952), Q(30051)),
    )
    coefficients = bivariate_bernstein(reduced, 5, 3)
    assert coefficients == expected
    assert all(value > 0 for row in coefficients for value in row)


def assert_rank_certificate(e1: Poly, e2: Poly, e3: Poly, survival: Poly) -> None:
    """Replay the exact identities used to prove ``A>a``."""

    # E2 rewrites the signed hazard increment as N(a,c,d).
    k = sum_polys([scale(-1, mul(c, d)), scale(-2, c), scale(6, d)])
    n_reduced = sum_polys(
        [
            scale(6, a),
            scale(-1, mul(sub(one, a), k)),
            scale(-4, mul(survival, mul(a, sub(one, a)))),
        ]
    )
    n_full = scale(4, mul(survival, mul(sub(one, a), sub(A, a))))
    assert sub(n_full, n_reduced) == e2

    # N=4s*a^2+L*a+K, with a positive derivative coefficient L.
    n_quadratic = scale(4, survival)
    n_linear = sum_polys(
        [
            scale(-5, mul(c, d)),
            scale(2, c),
            scale(10, d),
            const(2),
        ]
    )
    n_constant = sum_polys([mul(c, d), scale(2, c), scale(-6, d)])
    assert n_reduced == sum_polys(
        [mul(n_quadratic, mul(a, a)), mul(n_linear, a), n_constant]
    )

    # E1 eliminates b from the positivity expression forced by E3.
    t = add(
        scale(6, c),
        mul(sub(one, c), sum_polys([
            scale(3, mul(A, b)), scale(2, A), scale(-6, b)
        ])),
    )
    f_coefficient = sum_polys(
        [scale(5, mul(c, d)), scale(-14, c), scale(10, d), const(-4)]
    )
    f_constant = sum_polys(
        [scale(-6, mul(c, d)), scale(24, c), scale(-12, d)]
    )
    g_at_A = add(mul(f_coefficient, A), f_constant)
    assert add(scale(2, mul(sub(one, d), t)), g_at_A) == scale(
        3, mul(sub(const(2), A), e1)
    )

    # E3 says exactly that T is a strictly positive C-term.
    positive_c_term = scale(
        4, mul(C, mul(sub(one, A), mul(sub(one, b), sub(one, c))))
    )
    assert sub(positive_c_term, t) == e3

    assert_clock_signs(f_coefficient, f_constant, n_linear)
    assert_positive_threshold_numerator(
        survival, f_coefficient, f_constant, n_linear, n_constant
    )


def main() -> None:
    assert_payoff_origin()
    e1, e2, e3, survival, _ = recurrence_packet()
    assert_rank_certificate(e1, e2, e3, survival)

    # Boundary replay: the rank proof itself assumes strict hazards.
    assert_credible_first_unchanged()

    print("exact alternating support-6/support-9 hazard rank passed")
    print("local invariant: next player-1 support-6 hazard A is strictly > a")
    print("excluded: every strict alternating 6/9 finite cycle, any even period")
    print("scope: consecutive support-9 phases and other excursions remain open")


if __name__ == "__main__":
    main()
