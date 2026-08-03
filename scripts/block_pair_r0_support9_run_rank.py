#!/usr/bin/env python3
"""Exact hazard rank across an arbitrary finite strict support-9 run.

This strengthens ``block_pair_r0_alternating_6_9_rank.py`` without expanding
any period equations.  In the perturbed block-pair quitting game, consider

    support 6 -> support 9 -> ... -> support 9 -> support 6,

with a nonempty finite run of strict support-9 phases.  Let ``a`` and ``A``
be player 1's hazards at the two support-6 endpoints.  Then the Bellman
recurrences and the inactive Nash inequalities imply

    A > a.

Consequently there is no finite cyclic profile containing support 6 in which
every support-6 phase is separated by a nonempty finite support-9 run.  Run
lengths and hazards may vary around the cycle.  Combined with the separate
constant-support certificate (which excludes consecutive 6 phases and an
all-9 cycle), this excludes every finite strict cycle confined to supports 6
and 9.

The proof uses a relaxation, so it is not a bounded census.  At support-9
phase t put

    p_t = c_t+d_t-c_t*d_t,
    s_t = 1-p_t,
    h_t = 6*c_t-2*d_t-3*c_t*d_t,
    k_t = -c_t*d_t-2*c_t+6*d_t.

Active transport between consecutive support-9 phases is Möbius:

    c_{t+1} = 3*c_t/(2*(1-c_t)),
    d_{t+1} = 200*d_t/(411*(1-d_t)).

The first inactive player-1 inequality gives ``d_0<=3*c_0/4``.  The Möbius
maps preserve this inequality, while c increases.  If ``ell`` is the last c
hazard, every phase therefore satisfies

    h_t >= kappa(ell)*p_t,
    kappa(ell)=9*(2-ell)/(7-3*ell).

Weighted summation across the run gives ``H>=kappa*(1-S)`` and
``K<=mu*(1-S)``, where ``S=prod s_t`` and ``mu=4-kappa``.  These are the only
run data consumed below.  The aggregate Bellman equations then contradict
``A<=a``.  The final two-case inequality is replayed by exact polynomial
identities and Bernstein sign certificates.

The incoming coordinate ``a`` is consumed only through player 2's value
``2+6a/(1-a)`` and player 1's entry value 2.  It may therefore be an
effective hazard supplied by a preceding singleton-support block.

The support after the final 6 is unrestricted.  The only continuation bound
needed there is that player 3's value is at most its global terminal maximum
8; strictness of the support-6 hazards makes the current value strictly less
than 8 and forces the last support-9 player-0 hazard below 1/2.

Scope: this excludes finite strict cycles confined to supports 6 and 9 and
provides a local rank usable inside larger core cycles.  It does not cover
support-3 excursions, nonperiodic paths, or zero-hazard/product-flow hybrids.
Sure hazards are separately covered by the credible-First certificate.
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
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
Poly = algebra.Poly


def pow_poly(poly: Poly, exponent: int) -> Poly:
    result = algebra.const(1)
    for _ in range(exponent):
        result = algebra.mul(result, poly)
    return result


def bernstein_coefficients(
    poly: Poly, variables: tuple[int, ...], degrees: tuple[int, ...]
) -> dict[tuple[int, ...], Fraction]:
    """Tensor power-to-Bernstein conversion for the shared sparse algebra."""

    assert len(variables) == len(degrees)
    result: dict[tuple[int, ...], Fraction] = {}
    for index in product(*(range(degree + 1) for degree in degrees)):
        coefficient = Q(0)
        for exponent, power_coefficient in poly.items():
            if any(
                exponent[position] != 0
                for position in range(algebra.NVARS)
                if position not in variables
            ):
                raise AssertionError("polynomial uses a variable outside the chart")
            local = tuple(exponent[position] for position in variables)
            if all(local[k] <= index[k] for k in range(len(variables))):
                weight = Q(1)
                for k, degree in enumerate(degrees):
                    weight *= Q(
                        comb(index[k], local[k]), comb(degree, local[k])
                    )
                coefficient += power_coefficient * weight
        result[index] = coefficient
    return result


# Reuse two coordinates of the six-variable sparse algebra.
a = algebra.a
ell = algebra.A
u = algebra.b
one = algebra.const(1)


def scalar_polynomials() -> tuple[Poly, Poly, Poly]:
    """The separator C and the two case numerators P1,P2."""

    a2 = pow_poly(a, 2)
    a3 = pow_poly(a, 3)
    l2 = pow_poly(ell, 2)
    c_separator = algebra.sum_polys(
        [
            algebra.scale(12, algebra.mul(a2, l2)),
            algebra.scale(-40, algebra.mul(a2, ell)),
            algebra.scale(28, a2),
            algebra.scale(-15, algebra.mul(a, l2)),
            algebra.scale(32, algebra.mul(a, ell)),
            algebra.scale(14, a),
            algebra.scale(3, l2),
            algebra.scale(-10, ell),
        ]
    )
    p_clock = algebra.sum_polys(
        [
            algebra.scale(15, algebra.mul(a, l2)),
            algebra.scale(-14, algebra.mul(a, ell)),
            algebra.scale(-28, a),
            algebra.scale(-18, l2),
            algebra.scale(24, ell),
        ]
    )
    p_bellman = algebra.sum_polys(
        [
            algebra.scale(54, algebra.mul(a3, l2)),
            algebra.scale(-162, algebra.mul(a3, ell)),
            algebra.scale(108, a3),
            algebra.scale(-123, algebra.mul(a2, l2)),
            algebra.scale(389, algebra.mul(a2, ell)),
            algebra.scale(-266, a2),
            algebra.scale(78, algebra.mul(a, l2)),
            algebra.scale(-176, algebra.mul(a, ell)),
            algebra.scale(-88, a),
            algebra.scale(-18, l2),
            algebra.scale(60, ell),
        ]
    )
    return c_separator, p_clock, p_bellman


def assert_mobius_and_phase_bound() -> None:
    """Replay the run-independent per-phase ratio inequality."""

    c = algebra.a
    d = algebra.A
    last = algebra.b
    p = algebra.sum_polys([c, d, algebra.scale(-1, algebra.mul(c, d))])
    h = algebra.sum_polys(
        [algebra.scale(6, c), algebra.scale(-2, d), algebra.scale(-3, algebra.mul(c, d))]
    )
    left = algebra.sub(
        algebra.mul(algebra.sub(algebra.const(7), algebra.scale(3, last)), h),
        algebra.mul(algebra.scale(9, algebra.sub(algebra.const(2), last)), p),
    )
    right = algebra.add(
        algebra.mul(
            algebra.sub(algebra.scale(3, c), algebra.scale(4, d)),
            algebra.sum_polys(
                [
                    algebra.const(8),
                    algebra.scale(Q(3, 4), c),
                    algebra.scale(Q(-15, 4), last),
                ]
            ),
        ),
        algebra.scale(Q(9, 4), algebra.mul(c, algebra.sub(last, c))),
    )
    assert left == right
    k = algebra.sum_polys(
        [algebra.scale(-1, algebra.mul(c, d)), algebra.scale(-2, c), algebra.scale(6, d)]
    )
    assert algebra.add(h, k) == algebra.scale(4, p)

    # Consecutive support-9 active transport has
    # d'/c'=(400/1233)*(d/c)*((1-c)/(1-d)).  Thus d<=c implies the final
    # two factors are <=1, and d/c<=3/4 improves to d'/c'<=100/411<3/4.
    assert Q(400, 1233) * Q(3, 4) == Q(100, 411)
    assert Q(100, 411) < Q(3, 4)


def assert_last_hazard_lt_half() -> None:
    """Restrict ell to (0,1/2) without prescribing the outgoing support."""

    active_a = algebra.a
    active_b = algebra.A
    assert max(terminal(mask, 3) for mask in range(1, 16)) == 8

    # At support 6, player 3 gets 0 if player 1 quits alone, 8 if player 2
    # quits alone, 3 if both quit, and at most 8 after survival.  Replacing
    # the arbitrary successor value by 8 gives the displayed strict bound.
    value_with_successor_eight = algebra.sum_polys(
        [
            algebra.scale(
                8,
                algebra.mul(algebra.sub(one, active_a), active_b),
            ),
            algebra.scale(3, algebra.mul(active_a, active_b)),
            algebra.scale(
                8,
                algebra.mul(
                    algebra.sub(one, active_a), algebra.sub(one, active_b)
                ),
            ),
        ]
    )
    simplified = algebra.sub(
        algebra.const(8),
        algebra.mul(active_a, algebra.sub(algebra.const(8), algebra.scale(3, active_b))),
    )
    assert value_with_successor_eight == simplified
    assert algebra.sub(algebra.const(8), simplified) == algebra.mul(
        active_a, algebra.sub(algebra.const(8), algebra.scale(3, active_b))
    )

    # Active player 3 at the last support 9 fixes the final support-6 value
    # to 2+6*ell/(1-ell).  Its strict upper bound by 8 is equivalent to
    # ell<1/2.  The cleared difference is 6*(1-2ell).
    cleared_gap = algebra.sub(
        algebra.scale(8, algebra.sub(one, algebra.b)),
        algebra.add(
            algebra.scale(2, algebra.sub(one, algebra.b)),
            algebra.scale(6, algebra.b),
        ),
    )
    assert cleared_gap == algebra.scale(
        6, algebra.sub(one, algebra.scale(2, algebra.b))
    )


def assert_arbitrary_support9_run_rank() -> None:
    """Replay the local arbitrary-run rank and all of its sign packets."""

    assert_mobius_and_phase_bound()
    assert_last_hazard_lt_half()
    assert_boundary_polynomial_positive()
    assert_p2_strictly_decreasing()
    assert_two_case_identities()
    assert_credible_first_unchanged()


def substitute_l_half(poly: Poly) -> Poly:
    """Substitute ell=u/2, returning a polynomial in u only."""

    result: Poly = {}
    for exponent, coefficient in poly.items():
        assert all(exponent[index] == 0 for index in (0, 2, 3, 4, 5))
        power = exponent[1]
        target = [0] * algebra.NVARS
        target[2] = power
        result = algebra.add(
            result, {tuple(target): coefficient * Q(1, 2) ** power}
        )
    return result


def assert_boundary_polynomial_positive() -> None:
    """Bernstein-prove the polynomial controlling C at the P1 root."""

    l2 = pow_poly(ell, 2)
    l3 = pow_poly(ell, 3)
    l4 = pow_poly(ell, 4)
    l5 = pow_poly(ell, 5)
    boundary = algebra.sum_polys(
        [
            algebra.scale(513, l5),
            algebra.scale(-9018, l4),
            algebra.scale(39528, l3),
            algebra.scale(-62464, l2),
            algebra.scale(29792, ell),
            algebra.const(1568),
        ]
    )
    coefficients = bernstein_coefficients(substitute_l_half(boundary), (2,), (5,))
    assert tuple(coefficients[i,] for i in range(6)) == (
        Q(1568),
        Q(22736, 5),
        Q(29824, 5),
        Q(63149, 10),
        Q(47831, 8),
        Q(167725, 32),
    )
    assert all(value > 0 for value in coefficients.values())

    c_separator, p_clock, _ = scalar_polynomials()
    root_numerator = algebra.scale(6, algebra.mul(ell, algebra.sub(algebra.const(4), algebra.scale(3, ell))))
    root_denominator = algebra.sum_polys(
        [algebra.const(28), algebra.scale(14, ell), algebra.scale(-15, l2)]
    )
    # P1 = root_numerator-root_denominator*a.
    assert p_clock == algebra.sub(
        root_numerator, algebra.mul(root_denominator, a)
    )

    # Clear the positive square denominator in C(root_numerator/root_denominator).
    c_a2 = algebra.sum_polys(
        [algebra.scale(12, l2), algebra.scale(-40, ell), algebra.const(28)]
    )
    c_a1 = algebra.sum_polys(
        [algebra.scale(-15, l2), algebra.scale(32, ell), algebra.const(14)]
    )
    c_a0 = algebra.add(algebra.scale(3, l2), algebra.scale(-10, ell))
    cleared = algebra.sum_polys(
        [
            algebra.mul(c_a2, pow_poly(root_numerator, 2)),
            algebra.mul(c_a1, algebra.mul(root_numerator, root_denominator)),
            algebra.mul(c_a0, pow_poly(root_denominator, 2)),
        ]
    )
    assert cleared == algebra.mul(ell, boundary)
    # C is strictly increasing in a: c_a2>0 and c_a1>0 on ell<1/2.
    assert c_a2 == algebra.scale(
        4, algebra.mul(algebra.sub(algebra.scale(3, ell), algebra.const(7)), algebra.sub(ell, one))
    )
    c_a1_half = substitute_l_half(c_a1)
    c_a1_coefficients = bernstein_coefficients(c_a1_half, (2,), (2,))
    assert tuple(c_a1_coefficients[i,] for i in range(3)) == (
        Q(14), Q(22), Q(105, 4)
    )
    assert all(value > 0 for value in c_a1_coefficients.values())


def substitute_a_normalized(poly: Poly) -> Poly:
    """Substitute a=((10-3ell)/(52-21ell))*u and clear its square denominator."""

    numerator = algebra.sub(algebra.const(10), algebra.scale(3, ell))
    denominator = algebra.sub(algebra.const(52), algebra.scale(21, ell))
    result: Poly = {}
    for exponent, coefficient in poly.items():
        assert all(exponent[index] == 0 for index in (3, 4, 5))
        a_power = exponent[0]
        l_power = exponent[1]
        assert a_power <= 2 and exponent[2] == 0
        term = algebra.scale(coefficient, pow_poly(ell, l_power))
        term = algebra.mul(term, pow_poly(algebra.mul(numerator, u), a_power))
        term = algebra.mul(term, pow_poly(denominator, 2 - a_power))
        result = algebra.add(result, term)
    return result


def assert_p2_strictly_decreasing() -> None:
    """Bernstein-prove dP2/da<0 on 0<a<a_max(ell)."""

    l2 = pow_poly(ell, 2)
    derivative_half = algebra.sum_polys(
        [
            algebra.mul(
                pow_poly(a, 2),
                algebra.sum_polys(
                    [algebra.scale(81, l2), algebra.scale(-243, ell), algebra.const(162)]
                ),
            ),
            algebra.mul(
                a,
                algebra.sum_polys(
                    [algebra.scale(-123, l2), algebra.scale(389, ell), algebra.const(-266)]
                ),
            ),
            algebra.scale(39, l2),
            algebra.scale(-88, ell),
            algebra.const(-44),
        ]
    )
    cleared_derivative = algebra.scale(2, substitute_a_normalized(derivative_half))
    coefficients = bernstein_coefficients(cleared_derivative, (2, 1), (2, 4))
    expected = (
        (Q(-237952), Q(-308880), Q(-287060), Q(-234484), Q(-178746)),
        (Q(-376272), Q(-372291), Q(-312744), Q(-968967, 4), Q(-178746)),
        (Q(-482192), Q(-420312), Q(-332002), Q(-248015), Q(-178746)),
    )
    assert tuple(
        tuple(coefficients[i, j] for j in range(5)) for i in range(3)
    ) == expected
    assert all(value < 0 for value in coefficients.values())


def assert_two_case_identities() -> None:
    """Replay the aggregate q-bound split and both T upper bounds."""

    c_separator, p_clock, p_bellman = scalar_polynomials()
    kappa_den = algebra.sub(algebra.const(7), algebra.scale(3, ell))
    kappa_num = algebra.scale(9, algebra.sub(algebra.const(2), ell))
    mu_num = algebra.sub(algebra.const(10), algebra.scale(3, ell))
    mu_gap = algebra.sub(mu_num, algebra.scale(4, algebra.mul(a, kappa_den)))
    q_numerator = algebra.scale(
        2, algebra.mul(a, algebra.mul(algebra.add(algebra.scale(2, a), one), kappa_den))
    )
    q_denominator = algebra.mul(algebra.sub(one, a), mu_gap)

    # ell-q_a = -C / q_denominator.  Thus the two cases are exactly C<=0
    # and C>=0 once the positive denominator has been established.
    sub_poly = algebra.add(
        algebra.sub(algebra.mul(ell, q_denominator), q_numerator),
        c_separator,
    )
    assert sub_poly == {}

    payoff_denominator = algebra.sub(
        mu_num,
        algebra.mul(a, algebra.sub(algebra.const(52), algebra.scale(21, ell))),
    )
    assert algebra.sub(q_denominator, q_numerator) == payoff_denominator

    # Common numerator of the decreasing upper bound T(q).
    q = algebra.c
    t_numerator = algebra.sub(
        algebra.mul(
            algebra.scale(2, algebra.mul(algebra.sub(one, q), kappa_den)),
            algebra.add(algebra.scale(6, ell), algebra.scale(2, algebra.mul(a, algebra.sub(one, ell)))),
        ),
        algebra.mul(
            algebra.mul(algebra.sub(one, ell), algebra.sub(algebra.const(6), algebra.scale(3, a))),
            algebra.mul(kappa_num, q),
        ),
    )

    # At q=ell, T=-P1/(2*(7-3ell)).
    def substitute_q(poly: Poly, replacement: Poly) -> Poly:
        result: Poly = {}
        for exponent, coefficient in poly.items():
            q_power = exponent[3]
            reduced = list(exponent)
            reduced[3] = 0
            term: Poly = {tuple(reduced): coefficient}
            term = algebra.mul(term, pow_poly(replacement, q_power))
            result = algebra.add(result, term)
        return result

    assert substitute_q(t_numerator, ell) == algebra.scale(
        -1, algebra.mul(algebra.sub(one, ell), p_clock)
    )

    # At q=q_a, clearing q_denominator leaves exactly 2*kappa_den*P2.
    t_at_qa_cleared = algebra.sub(
        algebra.mul(
            algebra.scale(2, algebra.mul(payoff_denominator, kappa_den)),
            algebra.add(algebra.scale(6, ell), algebra.scale(2, algebra.mul(a, algebra.sub(one, ell)))),
        ),
        algebra.mul(
            algebra.mul(algebra.sub(one, ell), algebra.sub(algebra.const(6), algebra.scale(3, a))),
            algebra.mul(kappa_num, q_numerator),
        ),
    )
    assert t_at_qa_cleared == algebra.scale(2, algebra.mul(kappa_den, p_bellman))

    # On C=0 the two boundary signs agree through this exact identity.
    assert algebra.sub(
        algebra.scale(2, algebra.mul(algebra.sub(algebra.scale(3, ell), algebra.const(7)), p_bellman)),
        algebra.mul(payoff_denominator, p_clock),
    ) == algebra.scale(
        27,
        algebra.mul(
            algebra.sub(a, algebra.const(2)),
            algebra.mul(algebra.sub(ell, algebra.const(2)), c_separator),
        ),
    )


def main() -> None:
    assert_arbitrary_support9_run_rank()

    print("exact arbitrary support-9-run hazard rank passed")
    print("local invariant: next support-6 player-1 hazard A is strictly > a")
    print("outgoing support after the final 6 is unrestricted")
    print("rank excludes: every finite 6/9 cycle containing support 6")
    print("the separate constant-support certificate excludes the all-9 case")
    print("proof scope is run-length independent; no period equations enumerated")
    print("remaining: other-support excursions, nonperiodic paths, and hybrids")


if __name__ == "__main__":
    main()
