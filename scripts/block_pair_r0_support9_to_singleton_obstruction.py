#!/usr/bin/env python3
"""Exclude every finite ``{2,6} -> 9+ -> 2`` support prefix exactly.

Work in the perturbed block-pair quitting game.  Let a nonempty finite block
of strict support-9 phases lie between a phase of support 2 or 6 and a
support-2 phase.  For player 1 put ``y=V_1-2`` at a support-9 phase and ``y_plus`` at
its successor.  With c,d the hazards of players 0,3,

    y = h(c,d) + (1-c)(1-d)y_plus,
    h(c,d)=6c-2d-3cd.

Player 1's immediate-Quit offset at that phase is

    q(c,d)=-3c+4d,

and its inactive Nash inequality is ``q<=y``.  If q>0 then y>0 directly.  If
q<=0, then d<=3c/4 and the exact decomposition

    h = (9/4)c(2-c) + (2+3c)(3c/4-d)

shows h>0.  Therefore ``y_plus>=0`` implies ``y>0`` at every strict support-9
phase.  The following support-2 phase has value 2, hence terminal offset zero;
backward induction makes the entry offset of every nonempty support-9 block
strictly positive.  But active player 1 at either preceding support 2 or 6
requires its successor offset to be exactly zero.  Contradiction.

This excludes the final simple five-mask skeleton ``6,9,2,1,6`` before its
support-1 suffix is reached, every bare ``2,9+,2`` backtrack, and arbitrary
finite same-support-9 waiting.  It is a finite-run result: an infinite
support-9 tail converging to the zero-hazard boundary is not excluded here.
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
c = algebra.a
d = algebra.A
y_plus = algebra.b
one = algebra.one


def assert_payoff_origin() -> None:
    # Prescribed support-9 payoffs for player 1 and its Quit packet.
    assert tuple(terminal(mask, 1) for mask in (1, 8, 9)) == (8, 0, 3)
    assert tuple(terminal(mask, 1) for mask in (2, 3, 10, 11)) == (2, -1, 6, 3)

    # The support-2 endpoint has player-1 value 2.  At either possible
    # preceding support 2 or 6, active player 1 also demands successor value
    # 2 (the support-6 active successor coefficient is zero).
    assert (terminal(2, 1), terminal(4, 1), terminal(6, 1)) == (2, 0, 0)


def assert_one_step_positivity_packet() -> None:
    one_minus_c = algebra.sub(one, c)
    one_minus_d = algebra.sub(one, d)
    survival = algebra.mul(one_minus_c, one_minus_d)
    drift = algebra.sum_polys(
        [
            algebra.scale(6, c),
            algebra.scale(-2, d),
            algebra.scale(-3, algebra.mul(c, d)),
        ]
    )
    current_offset = algebra.add(drift, algebra.mul(survival, y_plus))

    quit_value = algebra.sum_polys(
        [
            algebra.scale(2, algebra.mul(one_minus_c, one_minus_d)),
            algebra.scale(-1, algebra.mul(c, one_minus_d)),
            algebra.scale(6, algebra.mul(one_minus_c, d)),
            algebra.scale(3, algebra.mul(c, d)),
        ]
    )
    quit_offset = algebra.sub(quit_value, algebra.const(2))
    assert quit_offset == algebra.add(algebra.scale(-3, c), algebra.scale(4, d))

    # When quit_offset<=0, gap=3c/4-d is nonnegative and this exact identity
    # makes drift strictly positive for 0<c<1.
    gap = algebra.sub(algebra.scale(Q(3, 4), c), d)
    positive_floor = algebra.scale(
        Q(9, 4), algebra.mul(c, algebra.sub(algebra.const(2), c))
    )
    assert drift == algebra.add(
        positive_floor,
        algebra.mul(algebra.add(algebra.const(2), algebra.scale(3, c)), gap),
    )

    # Keep the recurrence itself live: the only additional term beyond the
    # positive drift is nonnegative whenever y_plus>=0.
    assert algebra.sub(current_offset, drift) == algebra.mul(survival, y_plus)


def main() -> None:
    assert_payoff_origin()
    assert_one_step_positivity_packet()
    assert_credible_first_unchanged()

    print("exact finite support {2,6}->9+->2 prefix obstruction passed")
    print("one-step invariant: y_plus>=0 implies current y>0")
    print("excluded: every nonempty finite support-9 block from 2 or 6 to 2")
    print("therefore simple skeleton 6-9-2-1-6 is impossible")
    print("scope: infinite zero-hazard support-9 tails remain open")


if __name__ == "__main__":
    main()
