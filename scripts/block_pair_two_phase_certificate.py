#!/usr/bin/env python3
"""Exact local-obstruction certificate for the two-phase word [9, 6].

The quitting table is imported from ``block_pair_stationary_certificate``.
Phase 0 permits players 0 and 3 to quit (mask 9), while phase 1 permits
players 1 and 2 to quit (mask 6).  The phase-start values obey

    w^t_i = g^t_i + s_t w^(t+1)_i,

with phases read cyclically.  This script reconstructs, from the full terminal
table, the four local quit-minus-continue numerators for the active players.
It proves that they have no complementarity root with

    0 <= a,b,c,d < 1  and  (a,b,c,d) != 0.

All fourteen proper boundary subwords have elementary sign certificates.  The
full-support case is discharged by exact elimination: a Sylvester determinant,
a compact Bezout identity, a Sturm root count, and rational Bernstein bounds.
Only Python's standard-library integer/Fraction arithmetic is used.

This is deliberately a *local* Bellman obstruction.  It does not identify the
local test with the stronger periodic stopping-time best-response cap, and it
does not exclude other support words, longer periods, or private memory.  The
companion stationary certificate separately proves that every sure-First
local root for this table is strategically incredible.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import permutations
from math import comb
from pathlib import Path
import sys

# ``-I`` intentionally removes the script directory from ``sys.path``.  Add
# this resolved sibling directory explicitly so the certificate remains
# runnable in isolated mode without installing a package.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import (
    N,
    X,
    Poly,
    add,
    const,
    mul,
    neg,
    product_probability,
    restrict_to_support,
    root_action_difference,
    scale,
    sub,
    terminal,
)


assert N == 4
A_VAR, B_VAR, C_VAR, D_VAR = range(4)
a, b, c, d = X


def power(poly: Poly, exponent: int) -> Poly:
    assert exponent >= 0
    result = const(1)
    for _ in range(exponent):
        result = mul(result, poly)
    return result


def sum_polys(polys: list[Poly] | tuple[Poly, ...]) -> Poly:
    result: Poly = {}
    for poly in polys:
        result = add(result, poly)
    return result


def poly_from_cd(terms: dict[tuple[int, int], int]) -> Poly:
    """Build a polynomial in c=x_2 and d=x_3."""
    return {
        (0, 0, c_degree, d_degree): Fraction(coefficient)
        for (c_degree, d_degree), coefficient in terms.items()
        if coefficient != 0
    }


def expected_stage_payoffs() -> tuple[Poly, Poly, Poly, Poly]:
    probabilities = tuple(product_probability(mask) for mask in range(1 << N))
    result = []
    for player in range(N):
        payoff: Poly = {}
        for mask in range(1, 1 << N):
            payoff = add(
                payoff, scale(terminal(mask, player), probabilities[mask])
            )
        result.append(payoff)
    return tuple(result)  # type: ignore[return-value]


def local_two_phase_numerators() -> tuple[Poly, Poly, Poly, Poly]:
    """Return (F_a,F_b,F_c,F_d), clearing the positive value denominator."""
    phase0 = 0b1001
    phase1 = 0b0110
    expected = expected_stage_payoffs()
    g0 = tuple(restrict_to_support(payoff, phase0) for payoff in expected)
    g1 = tuple(restrict_to_support(payoff, phase1) for payoff in expected)
    s0 = restrict_to_support(product_probability(0), phase0)
    s1 = restrict_to_support(product_probability(0), phase1)
    value_denominator = sub(const(1), mul(s0, s1))

    def phase0_numerator(player: int) -> Poly:
        immediate = restrict_to_support(root_action_difference(player), phase0)
        no_opponent = restrict_to_support(
            product_probability(0, omitted=player), phase0
        )
        successor_value_numerator = add(g1[player], mul(s1, g0[player]))
        return sub(
            mul(value_denominator, immediate),
            mul(no_opponent, successor_value_numerator),
        )

    def phase1_numerator(player: int) -> Poly:
        immediate = restrict_to_support(root_action_difference(player), phase1)
        no_opponent = restrict_to_support(
            product_probability(0, omitted=player), phase1
        )
        successor_value_numerator = add(g0[player], mul(s0, g1[player]))
        return sub(
            mul(value_denominator, immediate),
            mul(no_opponent, successor_value_numerator),
        )

    # Variables are ordered (a,b,c,d), whereas the active players are
    # phase 0: a=player 0, d=player 3; phase 1: b=player 1, c=player 2.
    return (
        phase0_numerator(0),
        phase1_numerator(1),
        phase1_numerator(2),
        phase0_numerator(3),
    )


def expected_local_numerators() -> tuple[Poly, Poly, Poly, Poly]:
    fa = {
        (0, 1, 1, 2): Fraction(-4),
        (0, 1, 1, 1): Fraction(-5),
        (0, 1, 1, 0): Fraction(9),
        (0, 1, 0, 2): Fraction(4),
        (0, 1, 0, 1): Fraction(2),
        (0, 1, 0, 0): Fraction(-6),
        (0, 0, 1, 2): Fraction(4),
        (0, 0, 1, 1): Fraction(-6),
        (0, 0, 1, 0): Fraction(2),
        (0, 0, 0, 2): Fraction(-4),
        (0, 0, 0, 1): Fraction(2),
    }
    fd = {
        (2, 1, 1, 0): Fraction(4),
        (2, 1, 0, 0): Fraction(-4),
        (2, 0, 1, 0): Fraction(-4),
        (2, 0, 0, 0): Fraction(4),
        (1, 1, 1, 0): Fraction(-7),
        (1, 1, 0, 0): Fraction(2),
        (1, 0, 1, 0): Fraction(10),
        (1, 0, 0, 0): Fraction(2),
        (0, 1, 1, 0): Fraction(3),
        (0, 1, 0, 0): Fraction(2),
        (0, 0, 1, 0): Fraction(-6),
    }
    l_poly = sum_polys(
        [
            scale(2, mul(mul(a, c), d)),
            scale(-2, mul(a, c)),
            scale(3, mul(a, d)),
            scale(-6, a),
            scale(-2, mul(c, d)),
            scale(2, c),
            scale(2, d),
        ]
    )
    fb = neg(mul(sub(c, const(1)), l_poly))
    fc = {
        (1, 2, 0, 1): Fraction(4),
        (1, 2, 0, 0): Fraction(-4),
        (1, 1, 0, 1): Fraction(-5),
        (1, 1, 0, 0): Fraction(2),
        (1, 0, 0, 1): Fraction(1),
        (1, 0, 0, 0): Fraction(2),
        (0, 2, 0, 1): Fraction(-4),
        (0, 2, 0, 0): Fraction(4),
        (0, 1, 0, 1): Fraction(10),
        (0, 1, 0, 0): Fraction(2),
        (0, 0, 0, 1): Fraction(-6),
    }
    return fa, fb, fc, fd


def set_zero(poly: Poly, *variables: int) -> Poly:
    mask = (1 << N) - 1
    for variable in variables:
        mask &= ~(1 << variable)
    return restrict_to_support(poly, mask)


def assert_boundary_subwords(
    fa: Poly, fb: Poly, fc: Poly, fd: Poly
) -> None:
    """Close every nonempty proper support by a strict-sign active/inactive D."""
    one = const(1)

    # Singletons: the displayed inactive player has D>0 on the open face.
    assert set_zero(fc, B_VAR, C_VAR, D_VAR) == scale(2, a)       # {a}
    assert set_zero(fc, A_VAR, C_VAR, D_VAR) == mul(
        scale(2, b), add(scale(2, b), one)
    )                                                           # {b}
    assert set_zero(fa, A_VAR, B_VAR, D_VAR) == scale(2, c)       # {c}
    assert set_zero(fb, A_VAR, B_VAR, C_VAR) == scale(2, d)       # {d}

    # Pairs: the displayed active player's D has a strict sign.
    assert set_zero(fa, C_VAR, D_VAR) == scale(-6, b)             # {a,b}
    assert set_zero(fa, B_VAR, D_VAR) == scale(2, c)              # {a,c}
    assert set_zero(fd, B_VAR, C_VAR) == mul(
        scale(2, a), add(scale(2, a), one)
    )                                                            # {a,d}
    assert set_zero(fb, A_VAR, D_VAR) == mul(
        scale(-2, c), sub(c, one)
    )                                                            # {b,c}
    assert set_zero(fb, A_VAR, C_VAR) == scale(2, d)              # {b,d}
    assert set_zero(fc, A_VAR, B_VAR) == scale(-6, d)             # {c,d}

    # Three-variable faces.  For a,b in (0,1), ab-a-b<0.
    ab_minus_a_minus_b = sub(sub(mul(a, b), a), b)
    assert set_zero(fc, D_VAR) == mul(
        scale(-2, add(scale(2, b), one)), ab_minus_a_minus_b
    )                                                            # {a,b,c}
    assert set_zero(fd, C_VAR) == mul(
        scale(-2, add(scale(2, a), one)), ab_minus_a_minus_b
    )                                                            # {a,b,d}

    # On {a,c,d}, F_a=0 forces d=1/2 because cd-c-d<0.  Then
    # F_c=0 forces a=6/5, outside the unit cube.
    cd_minus_c_minus_d = sub(sub(mul(c, d), c), d)
    assert set_zero(fa, B_VAR) == mul(
        scale(2, add(scale(2, d), const(-1))), cd_minus_c_minus_d
    )
    acd_fc_at_half = set_zero(fc, B_VAR)
    acd_fc_at_half = substitute_constant(acd_fc_at_half, D_VAR, Fraction(1, 2))
    assert acd_fc_at_half == add(scale(Fraction(5, 2), a), const(-3))
    assert Fraction(6, 5) > 1

    # On {b,c,d}, both c-1 and cd-c-d are negative, so active F_b>0.
    assert set_zero(fb, A_VAR) == mul(
        scale(2, sub(c, one)), cd_minus_c_minus_d
    )


def substitute_constant(poly: Poly, variable: int, value: Fraction) -> Poly:
    result: Poly = {}
    for exponent, coefficient in poly.items():
        new_exponent = list(exponent)
        coefficient *= value ** new_exponent[variable]
        new_exponent[variable] = 0
        result = add(result, {tuple(new_exponent): coefficient})
    return result


def substitute_fractions(
    poly: Poly, replacements: dict[int, tuple[Poly, Poly]]
) -> tuple[Poly, Poly]:
    """Substitute polynomial fractions, returning one common numerator/denominator."""
    degrees = {
        variable: max((exponent[variable] for exponent in poly), default=0)
        for variable in replacements
    }
    denominator = const(1)
    for variable, (_, replacement_denominator) in replacements.items():
        denominator = mul(denominator, power(replacement_denominator, degrees[variable]))

    numerator: Poly = {}
    for exponent, coefficient in poly.items():
        term = const(coefficient)
        residual_exponent = list(exponent)
        for variable, (replacement_numerator, replacement_denominator) in replacements.items():
            variable_degree = exponent[variable]
            term = mul(term, power(replacement_numerator, variable_degree))
            term = mul(
                term,
                power(replacement_denominator, degrees[variable] - variable_degree),
            )
            residual_exponent[variable] = 0
        term = mul(term, {tuple(residual_exponent): Fraction(1)})
        numerator = add(numerator, term)
    return numerator, denominator


def coefficient_in(poly: Poly, variable: int, degree: int) -> Poly:
    result: Poly = {}
    for exponent, coefficient in poly.items():
        if exponent[variable] != degree:
            continue
        new_exponent = list(exponent)
        new_exponent[variable] = 0
        result[tuple(new_exponent)] = coefficient
    return result


def determinant(matrix: list[list[Poly]]) -> Poly:
    size = len(matrix)
    assert all(len(row) == size for row in matrix)
    result: Poly = {}
    for permutation in permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size)
            for j in range(i + 1, size)
        )
        term = const(-1 if inversions % 2 else 1)
        for row, column in enumerate(permutation):
            term = mul(term, matrix[row][column])
        result = add(result, term)
    return result


def sylvester_resultant_c(left: Poly, right: Poly) -> Poly:
    left_degree = max(exponent[C_VAR] for exponent in left)
    right_degree = max(exponent[C_VAR] for exponent in right)
    assert left_degree == right_degree == 3
    left_coefficients = [
        coefficient_in(left, C_VAR, degree) for degree in range(3, -1, -1)
    ]
    right_coefficients = [
        coefficient_in(right, C_VAR, degree) for degree in range(3, -1, -1)
    ]
    zero: Poly = {}
    rows: list[list[Poly]] = []
    for shift in range(3):
        rows.append(
            [zero] * shift + left_coefficients + [zero] * (2 - shift)
        )
    for shift in range(3):
        rows.append(
            [zero] * shift + right_coefficients + [zero] * (2 - shift)
        )
    return determinant(rows)


UPoly = tuple[Fraction, ...]


def trim_univariate(poly: UPoly) -> UPoly:
    values = list(poly)
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def to_univariate_d(poly: Poly) -> UPoly:
    assert all(
        exponent[A_VAR] == exponent[B_VAR] == exponent[C_VAR] == 0
        for exponent in poly
    )
    degree = max((exponent[D_VAR] for exponent in poly), default=-1)
    return trim_univariate(
        tuple(poly.get((0, 0, 0, power_), Fraction(0)) for power_ in range(degree + 1))
    )


def univariate_derivative(poly: UPoly) -> UPoly:
    return trim_univariate(tuple(i * poly[i] for i in range(1, len(poly))))


def univariate_divrem(dividend: UPoly, divisor: UPoly) -> tuple[UPoly, UPoly]:
    dividend_values = list(trim_univariate(dividend))
    divisor = trim_univariate(divisor)
    assert divisor
    if len(dividend_values) < len(divisor):
        return (), tuple(dividend_values)
    quotient = [Fraction(0)] * (len(dividend_values) - len(divisor) + 1)
    while len(dividend_values) >= len(divisor):
        shift = len(dividend_values) - len(divisor)
        leading = dividend_values[-1] / divisor[-1]
        quotient[shift] = leading
        for index, coefficient in enumerate(divisor):
            dividend_values[index + shift] -= leading * coefficient
        while dividend_values and dividend_values[-1] == 0:
            dividend_values.pop()
    return trim_univariate(tuple(quotient)), trim_univariate(tuple(dividend_values))


def univariate_evaluate(poly: UPoly, point: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(poly):
        result = result * point + coefficient
    return result


def sturm_chain(poly: UPoly) -> list[UPoly]:
    chain = [trim_univariate(poly), univariate_derivative(poly)]
    while chain[-1]:
        _, remainder = univariate_divrem(chain[-2], chain[-1])
        if not remainder:
            break
        chain.append(tuple(-coefficient for coefficient in remainder))
    return chain


def sign_variations(values: list[Fraction]) -> int:
    signs = [1 if value > 0 else -1 for value in values if value != 0]
    return sum(signs[index] != signs[index - 1] for index in range(1, len(signs)))


def roots_between(chain: list[UPoly], left: Fraction, right: Fraction) -> int:
    assert all(univariate_evaluate(poly, left) != 0 for poly in chain)
    assert all(univariate_evaluate(poly, right) != 0 for poly in chain)
    left_variations = sign_variations(
        [univariate_evaluate(poly, left) for poly in chain]
    )
    right_variations = sign_variations(
        [univariate_evaluate(poly, right) for poly in chain]
    )
    return left_variations - right_variations


def interval_bernstein_coefficients(
    poly: UPoly, left: Fraction, right: Fraction
) -> tuple[Fraction, ...]:
    """Bernstein coefficients after d=left+(right-left)t, t in [0,1]."""
    degree = len(poly) - 1
    width = right - left
    power_coefficients = []
    for j in range(degree + 1):
        power_coefficients.append(
            sum(
                poly[k] * comb(k, j) * left ** (k - j) * width ** j
                for k in range(j, degree + 1)
            )
        )
    return tuple(
        sum(
            power_coefficients[j]
            * Fraction(comb(i, j), comb(degree, j))
            for j in range(i + 1)
        )
        for i in range(degree + 1)
    )


def assert_full_support(fa: Poly, fb: Poly, fc: Poly, fd: Poly) -> None:
    one = const(1)
    l_poly = sum_polys(
        [
            scale(2, mul(mul(a, c), d)),
            scale(-2, mul(a, c)),
            scale(3, mul(a, d)),
            scale(-6, a),
            scale(-2, mul(c, d)),
            scale(2, c),
            scale(2, d),
        ]
    )
    da = sum_polys(
        [const(6), scale(-3, d), scale(2, c), scale(-2, mul(c, d))]
    )
    na = sum_polys([scale(2, c), scale(-2, mul(c, d)), scale(2, d)])
    assert l_poly == sub(na, mul(da, a))
    assert fb == neg(mul(sub(c, one), l_poly))
    # In the open cube c<1 and da=6-3d+2c(1-d)>0, hence F_b=0
    # is equivalent to a=na/da.

    e_poly = sum_polys(
        [scale(4, mul(c, d)), scale(9, c), scale(-4, d), const(-6)]
    )
    bc = mul(sub(one, d), e_poly)
    h_poly = sub(sub(mul(c, d), c), d)
    kc = mul(scale(2, add(scale(2, d), const(-1))), h_poly)
    assert fa == add(mul(bc, b), kc)

    # Exceptional branch bc=0.  Since d<1, e=0; since
    # h=-(c(1-d)+d)<0, K=0 forces d=1/2.  Then e=0 gives c=8/11
    # and L=0 gives a=38/115.  F_d fixes b, but that b misses F_c.
    half = Fraction(1, 2)
    e_at_half = substitute_constant(e_poly, D_VAR, half)
    assert e_at_half == add(scale(11, c), const(-8))
    exceptional_c = Fraction(8, 11)
    exceptional_a = Fraction(38, 115)
    assert substitute_constant(
        substitute_constant(l_poly, C_VAR, exceptional_c), D_VAR, half
    ) == add(const(Fraction(19, 11)), scale(Fraction(-115, 22), a))
    exceptional_fd = fd
    exceptional_fc = fc
    for variable, value in (
        (A_VAR, exceptional_a),
        (C_VAR, exceptional_c),
        (D_VAR, half),
    ):
        exceptional_fd = substitute_constant(exceptional_fd, variable, value)
        exceptional_fc = substitute_constant(exceptional_fc, variable, value)
    assert exceptional_fd == scale(
        Fraction(2, 13225), add(scale(20111, b), const(-7806))
    )
    assert exceptional_fc == scale(
        Fraction(2, 115),
        sum_polys([scale(77, mul(b, b)), scale(393, b), const(-125)]),
    )
    exceptional_b = Fraction(7806, 20111)
    assert substitute_constant(exceptional_fd, B_VAR, exceptional_b) == {}
    assert substitute_constant(exceptional_fc, B_VAR, exceptional_b) == const(
        Fraction(2, 115) * Fraction(323082265, 8254129)
    )

    # Regular branch bc != 0: substitute a=na/da and b=-kc/bc.
    fd_numerator, fd_denominator = substitute_fractions(
        fd, {A_VAR: (na, da), B_VAR: (neg(kc), bc)}
    )
    fc_numerator, fc_denominator = substitute_fractions(
        fc, {A_VAR: (na, da), B_VAR: (neg(kc), bc)}
    )
    assert fd_denominator == mul(power(da, 2), bc)
    assert fc_denominator == mul(da, power(bc, 2))

    u_poly = poly_from_cd(
        {
            (3, 4): 12, (3, 3): -76, (3, 2): 128, (3, 1): -76,
            (3, 0): 12, (2, 4): 14, (2, 3): 848, (2, 2): -2716,
            (2, 1): 2898, (2, 0): -1044, (1, 4): -14,
            (1, 3): -263, (1, 2): 794, (1, 1): -1020,
            (1, 0): 504, (0, 4): -12, (0, 3): -34, (0, 2): 204,
            (0, 1): -144,
        }
    )
    v_poly = poly_from_cd(
        {
            (3, 4): 124, (3, 3): -9, (3, 2): -444, (3, 1): 419,
            (3, 0): -90, (2, 4): -252, (2, 3): 1880,
            (2, 2): -3166, (2, 1): 1310, (2, 0): 228,
            (1, 4): 272, (1, 3): -1676, (1, 2): 2874,
            (1, 1): -1716, (1, 0): -144, (0, 4): -144,
            (0, 3): 400, (0, 2): -468, (0, 1): 504,
        }
    )
    assert fd_numerator == scale(2, u_poly)
    assert fc_numerator == mul(scale(-2, sub(one, d)), v_poly)

    p10 = poly_from_cd(
        {
            (0, 10): 38400, (0, 9): 1181040, (0, 8): 15234052,
            (0, 7): -79989972, (0, 6): -23552123,
            (0, 5): 820219890, (0, 4): -2194879076,
            (0, 3): 2781602736, (0, 2): -1865688336,
            (0, 1): 630681120, (0, 0): -82296000,
        }
    )
    resultant = sylvester_resultant_c(u_poly, v_poly)
    resultant_factorization = scale(
        -24,
        mul(
            d,
            mul(
                power(sub(d, one), 4),
                mul(
                    power(add(scale(2, d), const(-1)), 2),
                    mul(
                        power(add(scale(5, d), const(-6)), 3),
                        mul(
                            power(add(scale(7, d), const(6)), 2),
                            mul(add(scale(41, d), const(-78)), p10),
                        ),
                    ),
                ),
            ),
        ),
    )
    assert resultant == resultant_factorization

    # The only rational resultant root in (0,1) is d=1/2.  At d=1/2,
    # U and V have the following factorizations, whose sole common root in
    # c in (0,1) is c=8/11; that is exactly the already-separated bc=0 branch.
    u_at_half = substitute_constant(u_poly, D_VAR, half)
    v_at_half = substitute_constant(v_poly, D_VAR, half)
    assert u_at_half == scale(
        Fraction(-1, 8),
        mul(
            add(scale(11, c), const(-8)),
            sum_polys([scale(2, mul(c, c)), scale(123, c), const(-26)]),
        ),
    )
    assert v_at_half == scale(
        Fraction(1, 8),
        mul(add(c, const(22)), power(add(scale(11, c), const(-8)), 2)),
    )

    # For the remaining p10 branch, a compact Bezout identity forces a
    # linear relation A(d)c+B(d)=0 whenever U=V=0.
    n_alpha = poly_from_cd(
        {
            (1, 8): 590240, (1, 7): 10169056, (1, 6): 17401022,
            (1, 5): -76298000, (1, 4): -23336548,
            (1, 3): 205174258, (1, 2): -193570404,
            (1, 1): 68080536, (1, 0): -8210160,
            (0, 8): -579520, (0, 7): -10398360,
            (0, 6): 109465014, (0, 5): 120945587,
            (0, 4): -1071015674, (0, 3): 1530236044,
            (0, 2): -769961304, (0, 1): 74574432,
            (0, 0): 16872192,
        }
    )
    n_beta = poly_from_cd(
        {
            (1, 8): 14280, (1, 7): 156622, (1, 6): -922350,
            (1, 5): -1532762, (1, 4): 10140210,
            (1, 3): -15092378, (1, 2): 9691218,
            (1, 1): -2728512, (1, 0): 273672,
            (0, 8): 31660, (0, 7): 1237465, (0, 6): 15055749,
            (0, 5): -20946214, (0, 4): -115984669,
            (0, 3): 331784331, (0, 2): -338892930,
            (0, 1): 151435764, (0, 0): -23678568,
        }
    )
    a_coefficient = poly_from_cd(
        {
            (0, 11): 5038080, (0, 10): 188216304,
            (0, 9): 2005023796, (0, 8): -12541500544,
            (0, 7): 2385272761, (0, 6): 122855634554,
            (0, 5): -359448670940, (0, 4): 469464341888,
            (0, 3): -316137148944, (0, 2): 101908857888,
            (0, 1): -9762610752, (0, 0): -855878400,
        }
    )
    b_constant = poly_from_cd(
        {
            (0, 11): -5038080, (0, 10): -167367264,
            (0, 9): -1335476104, (0, 8): 6619925040,
            (0, 7): 2950975934, (0, 6): -63275064996,
            (0, 5): 159998890424, (0, 4): -203213181408,
            (0, 3): 144021171744, (0, 2): -53193706560,
            (0, 1): 7551066240,
        }
    )
    linear_relation = add(mul(a_coefficient, c), b_constant)
    bezout_left = add(
        mul(neg(n_alpha), u_poly), scale(4, mul(n_beta, v_poly))
    )
    bezout_right = mul(add(scale(5, d), const(-6)), linear_relation)
    assert bezout_left == bezout_right

    p10_univariate = to_univariate_d(p10)
    p10_sturm = sturm_chain(p10_univariate)
    assert roots_between(p10_sturm, Fraction(0), Fraction(1)) == 1
    isolate_left = Fraction(3369125955, 10_000_000_000)
    isolate_right = Fraction(3369125956, 10_000_000_000)
    assert univariate_evaluate(p10_univariate, isolate_left) < 0
    assert univariate_evaluate(p10_univariate, isolate_right) > 0

    b_univariate = to_univariate_d(b_constant)
    a_plus_b_univariate = to_univariate_d(add(a_coefficient, b_constant))
    b_bernstein = interval_bernstein_coefficients(
        b_univariate, isolate_left, isolate_right
    )
    a_plus_b_bernstein = interval_bernstein_coefficients(
        a_plus_b_univariate, isolate_left, isolate_right
    )
    assert min(b_bernstein) > 0
    assert min(a_plus_b_bernstein) > 0
    # For c in [0,1], A*c+B=(1-c)B+c(A+B)>0 throughout the isolating
    # interval, contradicting the Bezout relation at the unique p10 root.
    assert linear_relation == add(
        mul(sub(one, c), b_constant), mul(c, add(a_coefficient, b_constant))
    )


def main() -> None:
    numerators = local_two_phase_numerators()
    assert numerators == expected_local_numerators()
    assert_boundary_subwords(*numerators)
    assert_full_support(*numerators)
    print(
        "exact [9,6] certificate passed: no nonzero local-complementarity "
        "root with 0 <= a,b,c,d < 1 (all boundary subwords included)"
    )


if __name__ == "__main__":
    main()
