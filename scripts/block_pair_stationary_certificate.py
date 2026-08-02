#!/usr/bin/env python3
"""Exact stationary-support certificate for a four-player quitting table.

This regression uses only integer/Fraction arithmetic.  It proves that the
table below has no stationary complementarity root with

    0 <= x_i < 1 for every player i, and x != 0.

It does *not* audit faces on which some x_i = 1, and it does not claim to
exclude nonstationary absorption paths.

The proof reconstructs the stationary gain numerators G_i.  Singleton and
pair supports have explicit sign witnesses; three of the four triple supports
have direct sign witnesses; the remaining triple support and the full support
have exact positive Bernstein-polynomial certificates.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb


N = 4
Exp = tuple[int, int, int, int]
Poly = dict[Exp, Fraction]


# Rows are indexed by nonempty quitter masks 1,...,15.
TERMINAL: dict[int, tuple[int, int, int, int]] = {
    1: (-2, 8, 0, 0),
    2: (4, 2, 0, 0),
    3: (-5, -1, -1, 2),
    4: (-4, 0, 2, 8),
    5: (0, 4, 0, -4),
    6: (-7, 0, 6, 3),
    7: (-6, 1, -1, -3),
    8: (-4, 0, 8, 2),
    9: (-6, 3, 5, 6),
    10: (-2, 6, 1, 2),
    11: (-8, 3, 1, 4),
    12: (1, 0, 3, 2),
    13: (-7, -3, 0, 0),
    14: (-2, 0, 6, 0),
    15: (-10, -6, 1, -1),
}


ZERO_EXP: Exp = (0, 0, 0, 0)


def const(value: int | Fraction) -> Poly:
    value = Fraction(value)
    return {} if value == 0 else {ZERO_EXP: value}


def var(index: int) -> Poly:
    exponent = [0] * N
    exponent[index] = 1
    return {tuple(exponent): Fraction(1)}


X = tuple(var(i) for i in range(N))


def add(left: Poly, right: Poly) -> Poly:
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, Fraction(0)) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def neg(poly: Poly) -> Poly:
    return {exponent: -coefficient for exponent, coefficient in poly.items()}


def sub(left: Poly, right: Poly) -> Poly:
    return add(left, neg(right))


def scale(value: int | Fraction, poly: Poly) -> Poly:
    value = Fraction(value)
    return {
        exponent: value * coefficient
        for exponent, coefficient in poly.items()
        if value * coefficient != 0
    }


def mul(left: Poly, right: Poly) -> Poly:
    result: Poly = {}
    for left_exp, left_coefficient in left.items():
        for right_exp, right_coefficient in right.items():
            exponent = tuple(left_exp[i] + right_exp[i] for i in range(N))
            result[exponent] = (
                result.get(exponent, Fraction(0))
                + left_coefficient * right_coefficient
            )
    return {exponent: coefficient for exponent, coefficient in result.items()
            if coefficient != 0}


def prod_poly(factors: list[Poly] | tuple[Poly, ...]) -> Poly:
    result = const(1)
    for factor in factors:
        result = mul(result, factor)
    return result


def monomial(exponents: Exp) -> Poly:
    return {exponents: Fraction(1)}


def restrict_to_support(poly: Poly, mask: int) -> Poly:
    """Set every x_j outside ``mask`` to zero."""
    return {
        exponent: coefficient
        for exponent, coefficient in poly.items()
        if all(exponent[j] == 0 or (mask & (1 << j)) for j in range(N))
    }


def terminal(mask: int, player: int) -> int:
    if mask == 0:
        return 0
    return TERMINAL[mask][player]


def product_probability(mask: int, omitted: int | None = None) -> Poly:
    factors = []
    for player in range(N):
        if player == omitted:
            continue
        factors.append(
            X[player] if mask & (1 << player) else sub(const(1), X[player])
        )
    return prod_poly(factors)


def stationary_gain_numerators() -> tuple[Poly, Poly, Poly, Poly]:
    """Return p_abs times each stationary quit-minus-continue difference."""
    probabilities = tuple(product_probability(mask) for mask in range(1 << N))
    p_absorb = sub(const(1), probabilities[0])
    expected = []
    for player in range(N):
        value: Poly = {}
        for mask in range(1, 1 << N):
            value = add(value, scale(terminal(mask, player), probabilities[mask]))
        expected.append(value)

    gains = []
    for player in range(N):
        quit_value: Poly = {}
        continue_absorb: Poly = {}
        for opponent_mask in range(1 << N):
            if opponent_mask & (1 << player):
                continue
            probability = product_probability(opponent_mask, omitted=player)
            quit_value = add(
                quit_value,
                scale(terminal(opponent_mask | (1 << player), player), probability),
            )
            if opponent_mask != 0:
                continue_absorb = add(
                    continue_absorb,
                    scale(terminal(opponent_mask, player), probability),
                )
        no_opponent = prod_poly(
            [sub(const(1), X[j]) for j in range(N) if j != player]
        )
        gains.append(
            sub(
                mul(p_absorb, sub(quit_value, continue_absorb)),
                mul(no_opponent, expected[player]),
            )
        )
    return tuple(gains)  # type: ignore[return-value]


def bernstein_coefficients(
    poly: Poly, variables: tuple[int, ...], degrees: tuple[int, ...]
) -> dict[tuple[int, ...], Fraction]:
    """Convert a power polynomial to tensor Bernstein coefficients on [0,1]."""
    assert len(variables) == len(degrees)
    result: dict[tuple[int, ...], Fraction] = {}
    for bernstein_index in product(*(range(degree + 1) for degree in degrees)):
        coefficient = Fraction(0)
        for exponent, power_coefficient in poly.items():
            local_exp = tuple(exponent[variable] for variable in variables)
            if any(exponent[j] != 0 for j in range(N) if j not in variables):
                raise AssertionError("polynomial uses a variable outside the chart")
            if all(local_exp[k] <= bernstein_index[k]
                   for k in range(len(variables))):
                weight = Fraction(1)
                for k, degree in enumerate(degrees):
                    weight *= Fraction(
                        comb(bernstein_index[k], local_exp[k]),
                        comb(degree, local_exp[k]),
                    )
                coefficient += power_coefficient * weight
        result[bernstein_index] = coefficient
    return result


def determinant(matrix: list[list[int]]) -> int:
    size = len(matrix)
    answer = 0
    for perm in permutations(range(size)):
        inversions = sum(
            perm[i] > perm[j]
            for i in range(size)
            for j in range(i + 1, size)
        )
        term = -1 if inversions % 2 else 1
        for i in range(size):
            term *= matrix[i][perm[i]]
        answer += term
    return answer


def assert_residual_certificate() -> None:
    solo = [terminal(1 << i, i) for i in range(N)]
    residual = [
        [0 if i == j else terminal(1 << j, i) - solo[i] for j in range(N)]
        for i in range(N)
    ]
    assert solo == [-2, 2, 2, 2]
    assert residual == [
        [0, 6, -2, -2],
        [6, 0, -2, -2],
        [-2, -2, 0, 6],
        [-2, -2, 6, 0],
    ]
    normalized = [[entry // 2 for entry in row] for row in residual]
    expected_determinants = {
        2: [-9, -1, -1, -1, -1, -9],
        3: [6, 6, 6, 6],
        4: [45],
    }
    for size in (2, 3, 4):
        actual = []
        for support in combinations(range(N), size):
            principal = [[normalized[i][j] for j in support] for i in support]
            actual.append(determinant(principal))
        assert actual == expected_determinants[size]


def assert_support_certificates(gain: tuple[Poly, Poly, Poly, Poly]) -> None:
    x0, x1, x2, x3 = X

    # Singleton supports: an inactive player has a strict incentive to quit.
    singleton_witnesses = {
        1: (3, mul(scale(2, x0), add(scale(2, x0), const(1)))),
        2: (2, mul(scale(2, x1), add(scale(2, x1), const(1)))),
        4: (0, mul(scale(2, x2), add(x2, const(1)))),
        8: (1, mul(scale(2, x3), add(scale(2, x3), const(1)))),
    }
    for mask, (player, expected) in singleton_witnesses.items():
        assert restrict_to_support(gain[player], mask) == expected

    # Pair supports: an active player's gain is strictly nonzero in (0,1)^2.
    pair_witnesses = {
        3: (0, neg(mul(scale(3, x1), add(x1, const(2))))),
        5: (0, mul(scale(2, x2), add(x2, const(1)))),
        6: (1, mul(scale(2, x2), sub(const(1), x2))),
        9: (3, mul(scale(2, x0), add(scale(2, x0), const(1)))),
        10: (1, mul(scale(2, x3), add(scale(2, x3), const(1)))),
        12: (3, scale(-6, x2)),
    }
    for mask, (player, expected) in pair_witnesses.items():
        assert restrict_to_support(gain[player], mask) == expected

    # Support {0,1,2}: G_2 is strictly positive.  Both displayed factors are
    # strictly negative for x_0,x_1 in (0,1).
    bracket_7 = sub(
        mul(x0, add(add(scale(5, mul(x1, x1)), scale(-3, x1)), const(-2))),
        add(scale(4, mul(x1, x1)), scale(2, x1)),
    )
    expected_7 = mul(sub(x0, const(1)), bracket_7)
    assert restrict_to_support(gain[2], 7) == expected_7

    # Support {0,1,3}: G_3/2 is a sum of three strictly positive terms.
    positive_11 = add(
        add(
            mul(mul(x0, x0), mul(sub(const(1), x1), sub(const(2), x1))),
            mul(x0, sub(const(1), mul(x1, x1))),
        ),
        x1,
    )
    assert restrict_to_support(gain[3], 11) == scale(2, positive_11)

    # Support {1,2,3}: G_1 is strictly positive (negative * positive * negative).
    expected_14 = scale(
        2,
        mul(
            mul(sub(x2, const(1)), add(scale(2, x3), const(1))),
            sub(sub(mul(x2, x3), x2), x3),
        ),
    )
    assert restrict_to_support(gain[1], 14) == expected_14

    # Support {0,2,3}: a positive Bernstein ideal certificate.
    mu0 = add(add(const(53490), scale(-2311, x3)), scale(-7574, x2))
    mu2 = add(add(const(10698), scale(-37052, x3)), scale(-62134, x2))
    mu3 = const(10698)
    certificate_13 = restrict_to_support(
        add(add(mul(mu0, gain[0]), mul(mu2, gain[2])), mul(mu3, gain[3])),
        13,
    )
    bernstein_13 = bernstein_coefficients(
        certificate_13, variables=(0, 2, 3), degrees=(3, 3, 3)
    )
    assert bernstein_13[(0, 0, 0)] == 0
    assert min(
        coefficient
        for index, coefficient in bernstein_13.items()
        if index != (0, 0, 0)
    ) == 14264


def assert_full_support_certificate(gain: tuple[Poly, Poly, Poly, Poly]) -> None:
    x0, x1, x2, x3 = X
    lambdas = (
        add(
            add(add(const(-15553008), scale(-7528932, x3)), scale(3755590, x0)),
            scale(5098574, mul(x0, x2)),
        ),
        add(
            add(add(const(-15553008), scale(-15304880, x2)), scale(8520888, x1)),
            scale(4172497, mul(x1, x3)),
        ),
        add(add(const(-15553008), scale(13687356, x2)), scale(1804402, x1)),
        add(add(const(-15553008), scale(-5558092, x1)), scale(1700604, x0)),
    )
    certificate: Poly = {}
    for multiplier, player_gain in zip(lambdas, gain):
        certificate = add(certificate, mul(multiplier, player_gain))
    bernstein = bernstein_coefficients(
        certificate, variables=(0, 1, 2, 3), degrees=(3, 3, 3, 3)
    )
    assert bernstein[(0, 0, 0, 0)] == 0
    assert min(
        coefficient
        for index, coefficient in bernstein.items()
        if index != (0, 0, 0, 0)
    ) == 10368672


def main() -> None:
    gain = stationary_gain_numerators()
    assert_residual_certificate()
    assert_support_certificates(gain)
    assert_full_support_certificate(gain)
    print(
        "exact certificate passed: no stationary complementarity root "
        "with x != 0 and every x_i < 1"
    )


if __name__ == "__main__":
    main()
