#!/usr/bin/env python3
"""Exact exclusion of the strict support-6/support-9 two-cycle.

The game is the block-pair quitting table with
``r_0({0})=-2+11/100``.  Consider a two-phase periodic product profile whose
supports are exactly

    6 = {1,2},  9 = {0,3},

and whose four active hazards ``a=x_1, b=x_2, c=x_0, d=x_3`` lie in
``(0,1)``.  Active indifference and the two Bellman recurrences for players
1, 2, and 3 give the exact polynomials ``E1=E2=E3=0`` below.  At support 9,
player 1's inactive Quit-minus-Continue gap is ``4d-3c`` modulo ``E1``, so
Nash requires ``4d <= 3c``.

The exclusion is a small conditional Bernstein certificate.

* ``E2`` is strictly increasing in ``d``.  Comparing its zero at ``d`` to
  ``d <= 3c/4`` gives ``P(a,c) <= 0``.
* Eliminating ``b`` from ``E1,E3`` and then ``d`` against ``E2`` gives
  ``R(a,c)=0``.
* Exactly ``R=M*P+S``.  The bilinear Bernstein coefficients of ``M`` are
  ``(3,1/4,7/48,3/8)``, hence ``M>0`` on the unit square.  Every degree-(3,3)
  Bernstein coefficient of ``S`` is nonpositive and several are negative;
  since all tensor Bernstein weights are positive in the open square,
  ``S<0`` there.  Therefore ``R<0``, a contradiction.

This proves only the strict two-phase orbit ``6 -> 9 -> 6``.  It does not yet
exclude several consecutive support-9 phases, excursions through another
support, a nonperiodic path, or a zero-hazard hybrid.  Zero and sure hazards
belong to the separately audited support and sure-quitter boundaries.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import (  # noqa: E402
    N,
    Poly,
    X,
    add,
    bernstein_coefficients,
    const,
    mul,
    scale,
    sub,
)
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
A, B, C, D = X


def sum_polys(terms: list[Poly]) -> Poly:
    result: Poly = {}
    for term in terms:
        result = add(result, term)
    return result


def monomial(coefficient: int | Fraction, powers: tuple[int, int, int, int]) -> Poly:
    coefficient = Q(coefficient)
    return {} if coefficient == 0 else {powers: coefficient}


def linear_parts(poly: Poly, variable: int) -> tuple[Poly, Poly]:
    """Return ``coefficient, constant`` for a polynomial linear in a variable."""

    coefficient: Poly = {}
    constant: Poly = {}
    for exponent, value in poly.items():
        assert exponent[variable] <= 1
        if exponent[variable] == 0:
            constant = add(constant, {exponent: value})
        else:
            reduced = list(exponent)
            reduced[variable] = 0
            coefficient = add(coefficient, {tuple(reduced): value})
    return coefficient, constant


def linear_resultant(left: Poly, right: Poly, variable: int) -> Poly:
    """Resultant ``left_coeff*right_const-right_coeff*left_const``."""

    left_coefficient, left_constant = linear_parts(left, variable)
    right_coefficient, right_constant = linear_parts(right, variable)
    return sub(
        mul(left_coefficient, right_constant),
        mul(right_coefficient, left_constant),
    )


def equations() -> tuple[Poly, Poly, Poly]:
    """The three denominator-cleared Bellman recurrences."""

    e1 = sum_polys(
        [
            monomial(-2, (0, 1, 1, 1)),
            monomial(2, (0, 1, 1, 0)),
            monomial(2, (0, 1, 0, 1)),
            monomial(-2, (0, 1, 0, 0)),
            monomial(-3, (0, 0, 1, 1)),
            monomial(6, (0, 0, 1, 0)),
            monomial(-2, (0, 0, 0, 1)),
        ]
    )
    e2 = sum_polys(
        [
            monomial(-4, (2, 0, 1, 1)),
            monomial(4, (2, 0, 1, 0)),
            monomial(4, (2, 0, 0, 1)),
            monomial(-4, (2, 0, 0, 0)),
            monomial(5, (1, 0, 1, 1)),
            monomial(-2, (1, 0, 1, 0)),
            monomial(-10, (1, 0, 0, 1)),
            monomial(-2, (1, 0, 0, 0)),
            monomial(-1, (0, 0, 1, 1)),
            monomial(-2, (0, 0, 1, 0)),
            monomial(6, (0, 0, 0, 1)),
        ]
    )
    e3 = sum_polys(
        [
            monomial(-4, (1, 1, 2, 0)),
            monomial(7, (1, 1, 1, 0)),
            monomial(-3, (1, 1, 0, 0)),
            monomial(4, (1, 0, 2, 0)),
            monomial(-2, (1, 0, 1, 0)),
            monomial(-2, (1, 0, 0, 0)),
            monomial(4, (0, 1, 2, 0)),
            monomial(-10, (0, 1, 1, 0)),
            monomial(6, (0, 1, 0, 0)),
            monomial(-4, (0, 0, 2, 0)),
            monomial(-2, (0, 0, 1, 0)),
        ]
    )
    return e1, e2, e3


def assert_payoff_origin() -> None:
    """Replay the terminal cells used to derive ``E1,E2,E3`` and the gap."""

    assert N == 4
    # Support 6={1,2}: active p1 has successor value 2; active p2 has
    # current 2+4a and successor (2+4a)/(1-a).
    assert (terminal(2, 1), terminal(4, 1), terminal(6, 1)) == (2, 0, 0)
    assert (terminal(4, 2), terminal(2, 2), terminal(6, 2)) == (2, 0, 6)
    # Support 9={0,3}: active p3 has current 2+4c and successor
    # (2+4c)/(1-c).
    assert (terminal(8, 3), terminal(1, 3), terminal(9, 3)) == (2, 0, 6)
    # The three inactive recurrence packets, in mask order 1,8,9.
    assert tuple(terminal(mask, 1) for mask in (1, 8, 9)) == (8, 0, 3)
    assert tuple(terminal(mask, 2) for mask in (1, 8, 9)) == (0, 8, 5)
    # Support-6 packet for player 3, in mask order 2,4,6.
    assert tuple(terminal(mask, 3) for mask in (2, 4, 6)) == (0, 8, 3)
    # If inactive player 1 quits at support 9, masks become 2,3,10,11.
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)


def assert_inactive_gap(e1: Poly) -> None:
    """Verify ``Quit-Continue = 4d-3c-E1`` for player 1 at support 9."""

    one_minus_c = sub(const(1), C)
    one_minus_d = sub(const(1), D)
    # Quit after adding player 1 to the opponent masks 0,1,8,9.
    quit_value = sum_polys(
        [
            scale(2, mul(one_minus_c, one_minus_d)),
            scale(-1, mul(C, one_minus_d)),
            scale(6, mul(one_minus_c, D)),
            scale(3, mul(C, D)),
        ]
    )
    # Continue, with successor value 2-2b on joint continuation.
    continue_value = sum_polys(
        [
            scale(8, mul(C, one_minus_d)),
            scale(3, mul(C, D)),
            mul(mul(one_minus_c, one_minus_d), sub(const(2), scale(2, B))),
        ]
    )
    gap = sub(quit_value, continue_value)
    assert gap == sub(sub(scale(4, D), scale(3, C)), e1)


def certificate_polynomials(e2: Poly, e1: Poly, e3: Poly) -> tuple[Poly, Poly, Poly, Poly]:
    """Construct ``P,R,M,S`` and replay both exact eliminations."""

    p = sum_polys(
        [
            monomial(12, (2, 0, 2, 0)),
            monomial(-28, (2, 0, 1, 0)),
            monomial(16, (2, 0, 0, 0)),
            monomial(-15, (1, 0, 2, 0)),
            monomial(38, (1, 0, 1, 0)),
            monomial(8, (1, 0, 0, 0)),
            monomial(3, (0, 0, 2, 0)),
            monomial(-10, (0, 0, 1, 0)),
        ]
    )

    # E2(3c/4)=-P/4.  Its d coefficient is
    # (1-a)(6-c-4a(1-c))>0 on the open square.
    d_coefficient, d_constant = linear_parts(e2, 3)
    assert add(d_constant, mul(d_coefficient, scale(Q(3, 4), C))) == scale(Q(-1, 4), p)
    expected_d_coefficient = mul(
        sub(const(1), A),
        sub(sub(const(6), C), scale(4, mul(A, sub(const(1), C)))),
    )
    assert d_coefficient == expected_d_coefficient

    # First eliminate b.  Its resultant is exactly (1-c)*N3.
    n3 = sum_polys(
        [
            monomial(20, (1, 0, 2, 1)),
            monomial(-32, (1, 0, 2, 0)),
            monomial(-5, (1, 0, 1, 1)),
            monomial(22, (1, 0, 1, 0)),
            monomial(-10, (1, 0, 0, 1)),
            monomial(4, (1, 0, 0, 0)),
            monomial(-20, (0, 0, 2, 1)),
            monomial(32, (0, 0, 2, 0)),
            monomial(6, (0, 0, 1, 1)),
            monomial(-32, (0, 0, 1, 0)),
            monomial(12, (0, 0, 0, 1)),
        ]
    )
    assert linear_resultant(e1, e3, 1) == mul(sub(const(1), C), n3)

    r = sum_polys(
        [
            monomial(24, (3, 0, 3, 0)),
            monomial(-58, (3, 0, 2, 0)),
            monomial(46, (3, 0, 1, 0)),
            monomial(-12, (3, 0, 0, 0)),
            monomial(-84, (2, 0, 3, 0)),
            monomial(306, (2, 0, 2, 0)),
            monomial(-191, (2, 0, 1, 0)),
            monomial(-6, (2, 0, 0, 0)),
            monomial(96, (1, 0, 3, 0)),
            monomial(-366, (1, 0, 2, 0)),
            monomial(232, (1, 0, 1, 0)),
            monomial(24, (1, 0, 0, 0)),
            monomial(-36, (0, 0, 3, 0)),
            monomial(118, (0, 0, 2, 0)),
            monomial(-84, (0, 0, 1, 0)),
        ]
    )
    assert linear_resultant(e2, n3, 3) == scale(2, r)

    # M is written directly in its positive bilinear Bernstein basis.
    one_minus_a = sub(const(1), A)
    one_minus_c = sub(const(1), C)
    m = sum_polys(
        [
            scale(3, mul(one_minus_a, one_minus_c)),
            scale(Q(1, 4), mul(A, one_minus_c)),
            scale(Q(7, 48), mul(one_minus_a, C)),
            scale(Q(3, 8), mul(A, C)),
        ]
    )
    s = sub(r, mul(m, p))
    return p, r, m, s


def assert_bernstein_signs(m: Poly, s: Poly) -> None:
    m_coefficients = bernstein_coefficients(m, (0, 2), (1, 1))
    assert m_coefficients == {
        (0, 0): Q(3),
        (0, 1): Q(7, 48),
        (1, 0): Q(1, 4),
        (1, 1): Q(3, 8),
    }
    assert all(value > 0 for value in m_coefficients.values())

    s_coefficients = bernstein_coefficients(s, (0, 2), (3, 3))
    expected_rows = (
        (Q(0), Q(-18), Q(-661, 72), Q(-47, 48)),
        (Q(0), Q(-146, 27), Q(-731, 216), Q(-953, 144)),
        (Q(-32, 3), Q(-4, 3), Q(0), Q(-151, 24)),
        (Q(0), Q(0), Q(0), Q(0)),
    )
    assert tuple(
        tuple(s_coefficients[i, j] for j in range(4)) for i in range(4)
    ) == expected_rows
    assert all(value <= 0 for value in s_coefficients.values())
    assert any(value < 0 for value in s_coefficients.values())


def main() -> None:
    assert_payoff_origin()
    e1, e2, e3 = equations()
    assert_inactive_gap(e1)
    p, r, m, s = certificate_polynomials(e2, e1, e3)
    assert r == add(mul(m, p), s)
    assert_bernstein_signs(m, s)

    # Replay the sure-hazard boundary rather than relying on divisions by
    # 1-a or 1-c there.
    assert_credible_first_unchanged()

    print("exact support-6/support-9 strict two-cycle exclusion passed")
    print("inactive support-9 player-1 constraint gives P(a,c) <= 0")
    print("Bellman elimination gives R(a,c) = 0")
    print("Bernstein certificate gives R = M*P+S < 0")
    print("scope: exactly one strict support-6 and one strict support-9 phase")


if __name__ == "__main__":
    main()
