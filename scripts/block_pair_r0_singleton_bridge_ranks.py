#!/usr/bin/env python3
"""Exact singleton-bridge reductions for support-6 excursions.

This checker closes two unbounded finite-run families in the perturbed
block-pair quitting game.

First, consider

    support {2 or 6} -> (a nonempty finite support-1 block) -> support 2.

Player 1's active equality at either entering support requires successor
value 2.  Player 1 is active at the final support 2, so its value there is
also 2.  During the support-1 block, absorption gives player 1 payoff 8.  If
H is the block's aggregate absorption probability, its value at entry is
therefore ``8H+2(1-H)=2+6H>2``.  The support transition is impossible,
independently of inactive inequalities.  This removes both simple skeletons
beginning ``6,1,2``, every bare ``2,1+,2`` backtrack, and every version with
repeated support-1 phases.

Second, consider

    support 6 -> (a finite support-2 block) -> support 9 -> support 6,

where the final support-6 phase is endpoint-credible in the sense of
``block_pair_r0_support9_endpoint_rank.py``.  Player 2 receives zero when the
singleton player 1 quits.  If H is the block absorption probability and x is
the effective incoming hazard defined by the support-9 current value, the
Bellman equality is

    (1-H) * (2+6x/(1-x)) = 2+6a/(1-a).

Exact elimination gives

    x-a = H(1-a)(2a+1) / (3-2H(1-a)) >= 0.

The endpoint-credible support-9 lemma gives ``A>x`` even when H=0, hence
``A>a``.  This closes the simple skeleton ``6,2,9,6`` and arbitrary finite
same-support-2 repetitions without prescribing what follows the final 6.

There is also a complete singleton-word return rank.  In every nonempty
finite excursion

    support 6 -> word over {support 1, support 2} -> support 6,

player 2 receives zero at either possible singleton absorption.  Collapsing
the whole word to its survival S gives

    S*(2+4A) = 2+6a/(1-a),

and an exact positive factorization forces ``A>a``.  This includes arbitrary
owner changes and closes the simple skeleton ``6,2,1,6``.

Scope: these are finite strict-run reductions inside the five-mask core.
Changing singleton owners in another order, support-3 excursions,
nonperiodic boundary convergence, and zero-hazard flow are not claimed.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_support9_endpoint_rank as endpoint  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
one = algebra.one
# Reuse independent coordinates of the six-variable sparse algebra.
a = algebra.a
x = algebra.A
H = algebra.b


def assert_support_one_block_obstruction() -> None:
    # Player 1's exact packet: the required endpoint/current value is its
    # solo payoff 2, while singleton-player-0 absorption pays it 8.
    assert (terminal(2, 1), terminal(4, 1), terminal(6, 1)) == (2, 0, 0)
    assert terminal(1, 1) == 8

    entry_value = algebra.add(
        algebra.scale(8, H),
        algebra.scale(2, algebra.sub(one, H)),
    )
    assert algebra.sub(entry_value, algebra.const(2)) == algebra.scale(6, H)


def assert_support_two_effective_hazard_rank() -> None:
    # Player 2's exact packet across a support-2 singleton block.
    assert (terminal(4, 2), terminal(2, 2), terminal(6, 2)) == (2, 0, 6)

    one_minus_H = algebra.sub(one, H)
    one_minus_a = algebra.sub(one, a)
    one_minus_x = algebra.sub(one, x)
    value_numerator_a = algebra.add(algebra.const(2), algebra.scale(4, a))
    value_numerator_x = algebra.add(algebra.const(2), algebra.scale(4, x))

    # Clear the positive denominators in
    #   (1-H)*(2+4x)/(1-x) = (2+4a)/(1-a).
    bellman = algebra.sub(
        algebra.mul(
            one_minus_H,
            algebra.mul(one_minus_a, value_numerator_x),
        ),
        algebra.mul(one_minus_x, value_numerator_a),
    )
    denominator = algebra.sub(
        algebra.const(3),
        algebra.scale(2, algebra.mul(H, one_minus_a)),
    )
    positive_numerator = algebra.mul(
        H,
        algebra.mul(
            one_minus_a,
            algebra.add(algebra.scale(2, a), one),
        ),
    )
    assert denominator == algebra.sum_polys(
        [
            one,
            algebra.scale(2, algebra.sub(one, H)),
            algebra.scale(2, algebra.mul(H, a)),
        ]
    )

    # On Bellman=0 this says
    # denominator*(x-a)=positive_numerator.  The denominator is at least 1
    # on 0<=H,a<=1, and the numerator is nonnegative (strict for H>0).
    assert algebra.sub(
        algebra.sub(
            algebra.mul(denominator, algebra.sub(x, a)),
            positive_numerator,
        ),
        algebra.scale(Q(1, 2), bellman),
    ) == {}


def assert_arbitrary_singleton_word_return_rank() -> None:
    # Player 2 receives zero at either singleton support, while its current
    # value at the final support 6 is 2+4A.
    assert (terminal(1, 2), terminal(2, 2)) == (0, 0)
    assert (terminal(4, 2), terminal(6, 2)) == (2, 6)

    endpoint = x
    survival = H
    bellman = algebra.sub(
        algebra.mul(
            survival,
            algebra.mul(
                algebra.sub(one, a),
                algebra.add(algebra.const(2), algebra.scale(4, endpoint)),
            ),
        ),
        algebra.add(algebra.const(2), algebra.scale(4, a)),
    )
    cleared_increment = algebra.scale(
        2,
        algebra.mul(
            survival,
            algebra.mul(algebra.sub(one, a), algebra.sub(endpoint, a)),
        ),
    )
    positive_factor = algebra.mul(
        algebra.add(one, algebra.scale(2, a)),
        algebra.sub(one, algebra.mul(survival, algebra.sub(one, a))),
    )
    # On Bellman=0, the positive left multiplier times A-a equals the
    # positive_factor.  For strict a in (0,1) and 0<S<=1, the latter is
    # strictly positive (even if the singleton word has zero aggregate
    # hazard after compressing boundary stages).
    assert algebra.sub(
        algebra.sub(cleared_increment, positive_factor),
        algebra.scale(Q(1, 2), bellman),
    ) == {}


def replay_endpoint_rank() -> None:
    # The endpoint proof is uniform in its incoming hazard variable.  Replay
    # every algebraic component before instantiating that variable with x.
    endpoint.assert_payoff_origin()
    _, _, _, _, den, num, transfer = endpoint.local_polynomials()
    endpoint.assert_inactive_clock()
    endpoint.assert_clock_coefficients(den, num, transfer)


def main() -> None:
    assert_support_one_block_obstruction()
    assert_support_two_effective_hazard_rank()
    assert_arbitrary_singleton_word_return_rank()
    replay_endpoint_rank()
    assert_credible_first_unchanged()

    print("exact singleton-bridge support-6 reductions passed")
    print("excluded prefix: support 2 or 6 -> nonempty support-1 block -> 2")
    print("ranked family: 6 -> finite support-2 block -> 9 -> 6 has A>a")
    print("ranked family: every finite singleton-word 6-return has A>a")
    print("the endpoint rank leaves the outgoing support after the final 6 free")
    print("scope: finite strict core runs; nonperiodic boundaries remain")


if __name__ == "__main__":
    main()
