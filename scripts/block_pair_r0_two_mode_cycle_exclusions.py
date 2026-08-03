#!/usr/bin/env python3
"""Exact exclusions for three two-mode cycles in the perturbed block-pair game.

The payoff table is the block-pair quitting game with
``r_0({0}) = -2 + 11/100``.  All hazards below are assumed strictly between
zero and one.  This checker records three algebraic exclusions that are
independent of the unresolved support-6/support-9 kernel.

``1 <-> 6`` and ``2 <-> 9``
--------------------------------

For support 6={1,2}, write ``a`` for player 1's hazard.  Player 2's active
indifference makes the support-6 current value ``2+4a`` and its successor
value

    (2+4a)/(1-a) = 2+6a/(1-a).

At a preceding support-1={0} phase with hazard ``h``, player 2 receives zero
if player 0 quits.  Its current value is therefore
``(1-h)(2+4a)``.  Closing the two-cycle would equate these quantities, but
after multiplication by ``1-a`` their strict difference is

    2 (2a+1) (a+h-ah) > 0.

The support-2={1}/support-9={0,3} cycle is identical with player 3 in place
of player 2 and player 0's pair hazard in place of ``a``.

``3 <-> 9``
--------------------------------

Player 0 is active in both pair supports.  Put ``u=x_1`` at support 3 and
``v=x_3`` at support 9.  The exact active-coordinate transport coefficients
give

    odds(u) = (411/900) v,
    odds(v) = (311/200) u.

Their coefficient product is ``127821/180000 < 1``, while
``odds(u) odds(v) > uv`` for positive hazards, a contradiction.

The statements exclude the strict alternating two-phase cycles only.  Zero
hazards reduce support, sure hazards lie on the separately certified
sure-quitter boundary, and longer words or transitions through other modes
are deliberately not claimed here.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_r0_constant_pair_support import (  # noqa: E402
    COEFFICIENTS,
    N,
    SOLO,
    terminal,
)
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
ONE = Q(1)
Poly = dict[tuple[int, int], Fraction]


def poly_add(left: Poly, right: Poly) -> Poly:
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Q(0)) + coefficient
        if result[monomial] == 0:
            del result[monomial]
    return result


def poly_scale(coefficient: Fraction, polynomial: Poly) -> Poly:
    return {
        monomial: coefficient * value
        for monomial, value in polynomial.items()
        if coefficient * value != 0
    }


def poly_mul(left: Poly, right: Poly) -> Poly:
    result: Poly = {}
    for (a_degree, h_degree), left_coefficient in left.items():
        for (other_a_degree, other_h_degree), right_coefficient in right.items():
            monomial = (a_degree + other_a_degree, h_degree + other_h_degree)
            result[monomial] = (
                result.get(monomial, Q(0))
                + left_coefficient * right_coefficient
            )
    return {monomial: value for monomial, value in result.items() if value != 0}


def assert_singleton_pair_cycle_gap(
    singleton_owner: int,
    pair_owner: int,
    active_player: int,
) -> None:
    """Check the payoff packet yielding ``2(2a+1)(a+h-ah)``.

    ``pair_owner`` is the other active player at the pair support.  The
    displayed factorization proves strict positivity for ``0<a,h<1``:
    ``2a+1>0`` and ``a+h-ah = a+h(1-a)>0``.
    """

    singleton_mask = 1 << singleton_owner
    pair_mask = (1 << pair_owner) | (1 << active_player)

    solo = SOLO[active_player]
    collision = terminal(pair_mask, active_player)
    singleton_absorption = terminal(singleton_mask, active_player)

    # These three exact entries give
    #   Quit(a) = solo + (collision-solo)*a = 2+4a,
    #   successor(a) = Quit(a)/(1-a),
    # and the singleton predecessor (1-h)*Quit(a).
    assert solo == 2
    assert collision == 6
    assert singleton_absorption == 0

    # Verify the factorization as an exact bivariate polynomial identity.
    one: Poly = {(0, 0): ONE}
    a_var: Poly = {(1, 0): ONE}
    h_var: Poly = {(0, 1): ONE}
    one_minus_a = poly_add(one, poly_scale(-ONE, a_var))
    one_minus_h = poly_add(one, poly_scale(-ONE, h_var))
    quit_value = poly_add(
        {(0, 0): solo}, {(1, 0): collision - solo}
    )

    # Clearing the positive denominator 1-a gives
    #   (2+4a) - (1-a)(1-h)(2+4a)
    # = (2+4a)(a+h-ah)
    # = 2(2a+1)(a+h-ah).
    cleared_gap = poly_add(
        quit_value,
        poly_scale(
            -ONE,
            poly_mul(poly_mul(one_minus_a, one_minus_h), quit_value),
        ),
    )
    positive_clock = poly_add(
        poly_add(a_var, h_var), poly_scale(-ONE, poly_mul(a_var, h_var))
    )
    factored_gap = poly_mul(
        poly_scale(Q(2), poly_add(one, poly_scale(Q(2), a_var))),
        positive_clock,
    )
    assert cleared_gap == factored_gap


def assert_shared_player_pair_cycle_gap() -> None:
    """Check the exact multiplicative contradiction for supports 3 and 9."""

    # At support 3={0,1}: successor coefficient a_01 and current b_01.
    a01, b01 = COEFFICIENTS[0, 1]
    # At support 9={0,3}: successor coefficient a_03 and current b_03.
    a03, b03 = COEFFICIENTS[0, 3]
    assert (a01, b01) == (Q(-9, 2), Q(-311, 200))
    assert (a03, b03) == (Q(-1), Q(-411, 200))

    alpha = b03 / a01
    beta = b01 / a03
    assert alpha == Q(411, 900)
    assert beta == Q(311, 200)
    assert alpha > 0 and beta > 0
    assert alpha * beta == Q(127821, 180000)
    assert alpha * beta < ONE


def main() -> None:
    assert N == 4
    assert_singleton_pair_cycle_gap(
        singleton_owner=0, pair_owner=1, active_player=2
    )
    assert_singleton_pair_cycle_gap(
        singleton_owner=1, pair_owner=0, active_player=3
    )
    assert_shared_player_pair_cycle_gap()

    # Replay the exact hazard-one boundary packet rather than silently
    # dividing by a factor that may vanish there.
    assert_credible_first_unchanged()

    print("exact strict two-mode cycle exclusions passed")
    print("support cycles excluded = 1<->6, 2<->9, 3<->9")
    print("3<->9 coefficient product = 127821/180000 < 1")
    print("hazard-one boundary replayed from the credible-First certificate")
    print("scope: longer mixed-support words remain open")


if __name__ == "__main__":
    main()
