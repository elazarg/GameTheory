#!/usr/bin/env python3
"""Endpoint-credible hazard rank across ``6 -> 9 -> 3 -> 6``.

In the perturbed block-pair quitting game, consider strict consecutive phases

    support 6 -> support 9 -> support 3 -> support 6.

At support 9 write c,d for the hazards of players 0,3; at support 3 write
e,f for players 0,1; and at the final support 6 write A,B for players 1,2.
The initial support-6 player-1 hazard is a.  If every displayed phase obeys
its active Bellman equalities, player 1 is inactive-Nash at support 9, and
player 0 is inactive-Nash at the endpoint support 6, then

    A > a.

The active coordinates eliminate four hazards exactly:

    d = 311*f/(200+311*f),
    c = 2*(300*e+311*f)/(3*(200*e+311*f+400)),
    B = 9*e/(2*(1-e)).

Endpoint strictness gives e<2/11.  The support-9 inactive inequality implies
that, on writing ``f=(100/311)*e*r``, one has r<1.  Player 0's endpoint
inequality gives a rational lower bound A>=Num/Den.  On the enlarged full
box ``e=(2/11)u``, 0<=u,r<=1, the transfer polynomial is increasing in A and
its value at Num/Den is strictly positive.  Both signs are replayed by exact
tensor Bernstein certificates below.

The theorem also applies after an arbitrary finite support-2 block between
the initial support 6 and support 9: the singleton bridge checker constructs
an effective incoming hazard x>=a, and the present proof gives A>x.

Scope: the support-9 and support-3 phases here are single phases.  Repeated
3/9 waits, 3<->9 backtracking, other masks, and nonperiodic/zero-hazard
boundary limits remain outside this certificate.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_singleton_bridge_ranks as singleton_bridge  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)
from block_pair_r0_support9_run_rank import bernstein_coefficients  # noqa: E402


Q = Fraction
Poly = algebra.Poly
one = algebra.one

# Original-variable chart used to replay the eliminations.
c, d, e, f, A, B = tuple(algebra.var(index) for index in range(6))


@dataclass(frozen=True)
class RationalPoly:
    numerator: Poly
    denominator: Poly


def rat(poly: Poly) -> RationalPoly:
    return RationalPoly(poly, one)


def rat_add(left: RationalPoly, right: RationalPoly) -> RationalPoly:
    return RationalPoly(
        algebra.add(
            algebra.mul(left.numerator, right.denominator),
            algebra.mul(right.numerator, left.denominator),
        ),
        algebra.mul(left.denominator, right.denominator),
    )


def rat_neg(value: RationalPoly) -> RationalPoly:
    return RationalPoly(algebra.neg(value.numerator), value.denominator)


def rat_sub(left: RationalPoly, right: RationalPoly) -> RationalPoly:
    return rat_add(left, rat_neg(right))


def rat_mul(left: RationalPoly, right: RationalPoly) -> RationalPoly:
    return RationalPoly(
        algebra.mul(left.numerator, right.numerator),
        algebra.mul(left.denominator, right.denominator),
    )


def rat_scale(coefficient: int | Fraction, value: RationalPoly) -> RationalPoly:
    return RationalPoly(algebra.scale(coefficient, value.numerator), value.denominator)


def rat_equal(value: RationalPoly, numerator: Poly, denominator: Poly) -> None:
    assert algebra.sub(
        algebra.mul(value.numerator, denominator),
        algebra.mul(numerator, value.denominator),
    ) == {}


def eliminated_coordinates() -> tuple[RationalPoly, RationalPoly]:
    d_numerator = algebra.scale(311, f)
    d_denominator = algebra.add(algebra.const(200), algebra.scale(311, f))
    c_numerator = algebra.scale(
        2, algebra.add(algebra.scale(300, e), algebra.scale(311, f))
    )
    c_denominator = algebra.scale(
        3,
        algebra.sum_polys(
            [algebra.scale(200, e), algebra.scale(311, f), algebra.const(400)]
        ),
    )
    c_value = RationalPoly(c_numerator, c_denominator)
    d_value = RationalPoly(d_numerator, d_denominator)

    # Shared active player 0 across 9->3:
    #   f=(200/311)*odds(d).
    shared_zero = rat_sub(
        rat_scale(311, rat_mul(rat(f), rat_sub(rat(one), d_value))),
        rat_scale(200, d_value),
    )
    assert shared_zero.numerator == {}

    # Player 1's current value at support 9 is exactly 2.  Its offset is
    # h(c,d)-3(1-c)(1-d)e and vanishes after the displayed substitutions.
    h = rat_add(
        rat_add(rat_scale(6, c_value), rat_scale(-2, d_value)),
        rat_scale(-3, rat_mul(c_value, d_value)),
    )
    clock = rat_mul(rat_sub(rat(one), c_value), rat_sub(rat(one), d_value))
    player_one_offset = rat_sub(h, rat_scale(3, rat_mul(clock, rat(e))))
    assert player_one_offset.numerator == {}

    return c_value, d_value


def transfer_numerator(endpoint: Poly, e_value: Poly, f_value: Poly) -> Poly:
    endpoint2 = algebra.mul(endpoint, endpoint)
    f2 = algebra.mul(f_value, f_value)
    return algebra.sum_polys(
        [
            algebra.scale(248800, algebra.mul(endpoint2, algebra.mul(e_value, f2))),
            algebra.scale(711200, algebra.mul(endpoint2, algebra.mul(e_value, f_value))),
            algebra.scale(-960000, algebra.mul(endpoint2, e_value)),
            algebra.scale(-248800, algebra.mul(endpoint2, f2)),
            algebra.scale(-711200, algebra.mul(endpoint2, f_value)),
            algebra.scale(960000, endpoint2),
            algebra.scale(-186600, algebra.mul(endpoint, algebra.mul(e_value, f2))),
            algebra.scale(1083800, algebra.mul(endpoint, algebra.mul(e_value, f_value))),
            algebra.scale(960000, algebra.mul(endpoint, e_value)),
            algebra.scale(3026030, algebra.mul(endpoint, f2)),
            algebra.scale(5580400, algebra.mul(endpoint, f_value)),
            algebra.scale(480000, endpoint),
            algebra.scale(-62200, algebra.mul(e_value, f2)),
            algebra.scale(-675400, algebra.mul(e_value, f_value)),
            algebra.scale(720000, e_value),
            algebra.scale(-1036252, f2),
            algebra.scale(-1510400, f_value),
        ]
    )


def assert_transfer_origin(c_value: RationalPoly, d_value: RationalPoly) -> None:
    # At support 3, inactive player 2 receives -1 on joint absorption and 0
    # on either singleton absorption.  The final support-6 current value is
    # 2+4A.  Transport this through support 9, whose player-2 packet is
    # (0,8,5), and compare it with the endpoint hazard value.
    assert tuple(terminal(mask, 2) for mask in (1, 2, 3)) == (0, 0, -1)
    assert tuple(terminal(mask, 2) for mask in (1, 8, 9)) == (0, 8, 5)

    one_minus_e = algebra.sub(one, e)
    one_minus_f = algebra.sub(one, f)
    support_three_value = algebra.add(
        algebra.scale(-1, algebra.mul(e, f)),
        algebra.mul(
            algebra.mul(one_minus_e, one_minus_f),
            algebra.add(algebra.const(2), algebra.scale(4, A)),
        ),
    )
    c_clock = rat_sub(rat(one), c_value)
    d_clock = rat_sub(rat(one), d_value)
    support_nine_value = rat_add(
        rat_add(
            rat_scale(8, rat_mul(d_value, c_clock)),
            rat_scale(5, rat_mul(c_value, d_value)),
        ),
        rat_mul(rat_mul(c_clock, d_clock), rat(support_three_value)),
    )
    endpoint_target = rat_add(
        rat(algebra.const(2)),
        RationalPoly(algebra.scale(6, A), algebra.sub(one, A)),
    )
    transfer = rat_mul(rat(algebra.sub(one, A)), rat_sub(endpoint_target, support_nine_value))

    expected_numerator = transfer_numerator(A, e, f)
    expected_denominator = algebra.scale(
        3,
        algebra.mul(
            algebra.add(algebra.scale(311, f), algebra.const(200)),
            algebra.sum_polys(
                [algebra.scale(200, e), algebra.scale(311, f), algebra.const(400)]
            ),
        ),
    )
    rat_equal(transfer, expected_numerator, expected_denominator)


def endpoint_threshold() -> tuple[Poly, Poly]:
    # Shared active player 1 across 3->6 gives B=(9/2)*odds(e).
    shared_one = algebra.sub(
        algebra.scale(2, algebra.mul(B, algebra.sub(one, e))),
        algebra.scale(9, e),
    )

    # Active player 0 at support 3 fixes its endpoint value to
    # q_0-9*odds(f).  Compare player 0's Quit value at support 6 with that
    # current value, clearing 100(1-f).
    q0 = algebra.const(Q(-189, 100))
    endpoint_quit = algebra.sum_polys(
        [
            algebra.mul(q0, algebra.mul(algebra.sub(one, A), algebra.sub(one, B))),
            algebra.scale(-5, algebra.mul(A, algebra.sub(one, B))),
            algebra.scale(-6, algebra.mul(A, B)),
        ]
    )
    d0_cleared = algebra.add(
        algebra.scale(
            100,
            algebra.mul(algebra.sub(one, f), algebra.sub(endpoint_quit, q0)),
        ),
        algebra.scale(900, f),
    )
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
    nash_numerator = algebra.sub(numerator, algebra.mul(A, denominator))
    assert algebra.sub(
        algebra.sub(
            algebra.scale(2, algebra.mul(algebra.sub(one, e), d0_cleared)),
            nash_numerator,
        ),
        algebra.mul(
            algebra.mul(
                algebra.sub(algebra.scale(289, A), algebra.const(189)),
                algebra.sub(f, one),
            ),
            shared_one,
        ),
    ) == {}
    return numerator, denominator


def assert_inactive_clock(c_value: RationalPoly, d_value: RationalPoly) -> None:
    inactive_difference = rat_add(rat_scale(-3, c_value), rat_scale(4, d_value))
    clock_numerator = algebra.sum_polys(
        [
            algebra.scale(31100, algebra.mul(e, f)),
            algebra.scale(-60000, e),
            algebra.scale(96721, algebra.mul(f, f)),
            algebra.scale(186600, f),
        ]
    )
    clock_denominator = algebra.mul(
        algebra.add(algebra.scale(311, f), algebra.const(200)),
        algebra.sum_polys(
            [algebra.scale(200, e), algebra.scale(311, f), algebra.const(400)]
        ),
    )
    rat_equal(inactive_difference, algebra.scale(2, clock_numerator), clock_denominator)

    # Put f=(100/311)e*r.  The inactive numerator becomes the displayed
    # positive factor times e*r^2+e*r+6r-6.  Since e,r>0, nonpositivity
    # forces r<1.
    r = B
    f_clock = algebra.scale(Q(100, 311), algebra.mul(e, r))

    def replace_f(poly: Poly) -> Poly:
        result: Poly = {}
        for exponent, coefficient in poly.items():
            power = exponent[3]
            base_exp = list(exponent)
            base_exp[3] = 0
            term = {tuple(base_exp): coefficient}
            for _ in range(power):
                term = algebra.mul(term, f_clock)
            result = algebra.add(result, term)
        return result

    substituted = replace_f(clock_numerator)
    expected = algebra.scale(
        10000,
        algebra.mul(
            e,
            algebra.sum_polys(
                [
                    algebra.mul(e, algebra.mul(r, r)),
                    algebra.mul(e, r),
                    algebra.scale(6, r),
                    algebra.const(-6),
                ]
            ),
        ),
    )
    assert substituted == expected


def derivative(poly: Poly, variable: int) -> Poly:
    result: Poly = {}
    for exponent, coefficient in poly.items():
        power = exponent[variable]
        if power == 0:
            continue
        target = list(exponent)
        target[variable] -= 1
        result[tuple(target)] = coefficient * power
    return result


def assert_scaled_box_certificate() -> None:
    # Fresh coordinates in the same sparse algebra: endpoint A, scaled
    # e-coordinate u, and inactive-clock ratio r.
    endpoint = algebra.var(0)
    u = algebra.var(1)
    r = algebra.var(2)
    e_scaled = algebra.scale(Q(2, 11), u)
    f_scaled = algebra.scale(Q(200, 3421), algebra.mul(u, r))
    transfer = transfer_numerator(endpoint, e_scaled, f_scaled)

    derivative_coefficients = bernstein_coefficients(
        derivative(transfer, 0), variables=(0, 1, 2), degrees=(1, 3, 2)
    )
    assert len(derivative_coefficients) == 24
    assert min(derivative_coefficients.values()) == Q(480000)
    assert all(value > 0 for value in derivative_coefficients.values())

    numerator = algebra.sum_polys(
        [
            algebra.scale(1701, e_scaled),
            algebra.scale(-3501, algebra.mul(e_scaled, f_scaled)),
            algebra.scale(1800, f_scaled),
        ]
    )
    denominator = algebra.mul(
        algebra.sub(one, f_scaled),
        algebra.add(algebra.scale(1979, e_scaled), algebra.const(622)),
    )
    assert Q(1701) - Q(3501) * Q(200, 3421) > 0

    # Extract the quadratic coefficients of the already-validated transfer
    # numerator by evaluating its explicit formula at a formal endpoint.
    f2 = algebra.mul(f_scaled, f_scaled)
    quadratic = algebra.sum_polys(
        [
            algebra.scale(248800, algebra.mul(e_scaled, f2)),
            algebra.scale(711200, algebra.mul(e_scaled, f_scaled)),
            algebra.scale(-960000, e_scaled),
            algebra.scale(-248800, f2),
            algebra.scale(-711200, f_scaled),
            algebra.const(960000),
        ]
    )
    linear = algebra.sum_polys(
        [
            algebra.scale(-186600, algebra.mul(e_scaled, f2)),
            algebra.scale(1083800, algebra.mul(e_scaled, f_scaled)),
            algebra.scale(960000, e_scaled),
            algebra.scale(3026030, f2),
            algebra.scale(5580400, f_scaled),
            algebra.const(480000),
        ]
    )
    constant = algebra.sum_polys(
        [
            algebra.scale(-62200, algebra.mul(e_scaled, f2)),
            algebra.scale(-675400, algebra.mul(e_scaled, f_scaled)),
            algebra.scale(720000, e_scaled),
            algebra.scale(-1036252, f2),
            algebra.scale(-1510400, f_scaled),
        ]
    )
    assert transfer == algebra.sum_polys(
        [
            algebra.mul(quadratic, algebra.mul(endpoint, endpoint)),
            algebra.mul(linear, endpoint),
            constant,
        ]
    )

    # Den^2*T_num(Num/Den), whose sign is the transfer sign at the endpoint
    # Nash threshold.  Every term contains u; remove that positive factor.
    threshold = algebra.sum_polys(
        [
            algebra.mul(quadratic, algebra.mul(numerator, numerator)),
            algebra.mul(linear, algebra.mul(numerator, denominator)),
            algebra.mul(constant, algebra.mul(denominator, denominator)),
        ]
    )
    reduced: Poly = {}
    for exponent, coefficient in threshold.items():
        assert exponent[1] >= 1
        target = list(exponent)
        target[1] -= 1
        reduced[tuple(target)] = coefficient
    threshold_coefficients = bernstein_coefficients(
        reduced, variables=(1, 2), degrees=(6, 4)
    )
    assert len(threshold_coefficients) == 35
    assert min(threshold_coefficients.values()) == Q(1542626560000, 11)
    assert all(value > 0 for value in threshold_coefficients.values())


def assert_transfer_sign_identity() -> None:
    # If V is the transported support-9 value and the incoming support-6
    # equality says V=2+6a/(1-a), then the transfer sign is exactly A-a.
    incoming = algebra.var(0)
    endpoint = algebra.var(1)
    value = algebra.var(2)
    bellman = algebra.sub(
        algebra.mul(algebra.sub(one, incoming), algebra.sub(value, algebra.const(2))),
        algebra.scale(6, incoming),
    )
    transfer = algebra.sub(
        algebra.add(algebra.const(2), algebra.scale(4, endpoint)),
        algebra.mul(algebra.sub(one, endpoint), value),
    )
    assert algebra.sub(
        algebra.sub(
            algebra.mul(algebra.sub(one, incoming), transfer),
            algebra.scale(6, algebra.sub(endpoint, incoming)),
        ),
        algebra.mul(algebra.sub(endpoint, one), bellman),
    ) == {}


def assert_payoff_origin() -> None:
    assert (terminal(1, 1), terminal(8, 1), terminal(9, 1)) == (8, 0, 3)
    assert (terminal(1, 0), terminal(8, 0), terminal(9, 0)) == (
        Q(-189, 100),
        -4,
        -6,
    )
    assert tuple(terminal(mask, 0) for mask in (1, 3, 5, 7)) == (
        Q(-189, 100),
        -5,
        0,
        -6,
    )


def main() -> None:
    assert_payoff_origin()
    c_value, d_value = eliminated_coordinates()
    assert_transfer_origin(c_value, d_value)
    endpoint_threshold()
    assert_inactive_clock(c_value, d_value)
    assert_scaled_box_certificate()
    assert_transfer_sign_identity()

    # Replay the exact effective-hazard bridge used for an arbitrary finite
    # support-2 block before support 9.
    singleton_bridge.assert_support_two_effective_hazard_rank()
    assert_credible_first_unchanged()

    print("exact endpoint-credible support 6->9->3->6 rank passed")
    print("local invariant: final player-1 support-6 hazard A is strictly > a")
    print("also covers a finite support-2 block before support 9")
    print("derivative Bernstein minimum = 480000")
    print("threshold Bernstein minimum = 1542626560000/11")
    print("scope: single support-9/support-3 phases; repeated backtracking remains")


if __name__ == "__main__":
    main()
