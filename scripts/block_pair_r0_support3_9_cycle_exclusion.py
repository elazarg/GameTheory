#!/usr/bin/env python3
"""Exclude every finite strict cycle confined to supports 3 and 9.

This is the perturbed block-pair quitting table, although the changed
player-0 singleton reward is not needed for this obstruction.  Compress a
finite cyclic word over supports

    3 = {0,1},       9 = {0,3}

into a nonempty support-9 block followed by a nonempty support-3 block.  Let
``c_first`` and ``c_last`` be player 0's hazards at the first and last
support-9 phases.

Player 3 is active at support 9.  Its Quit value against player 0's hazard
``c`` is ``2+4c``; its Continue value is ``(1-c)V_next``.  Indifference at
two consecutive support-9 phases therefore gives

    c_next = (3/2)c/(1-c) > c.

Consequently ``c_last >= c_first``.  Indifference at the last support-9
phase requires the value entering the support-3 block to be

    2 + 6c_last/(1-c_last).

Player 3 is inactive throughout support 3.  Every absorbing support-3 cell
pays player 3 at most 2, while the successor value at the first support-9
phase is player 3's current Quit value ``2+4c_first``.  Collapsing the whole
finite support-3 block to survival ``S`` therefore bounds its entry value by

    2(1-S) + S(2+4c_first) <= 2+4c_first.

But

    2 + 6c_last/(1-c_last)
      >= 2 + 6c_first/(1-c_first)
      > 2 + 4c_first

for every strict ``c_first>0``.  This contradiction excludes all finite
strict 3/9 cycles at once, with arbitrary block lengths and hazards.

The theorem does not cover a one-sided nonperiodic path, hazards on the
support boundary, or a zero-hazard product-flow limit.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_constant_pair_support as constant_pair  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


one = algebra.one
c, c_next, c_first, c_last, survival, aggregate = tuple(
    algebra.var(index) for index in range(6)
)


def assert_support_nine_player_three_transport() -> None:
    """Replay player 3's current and successor values at support 9."""

    assert tuple(terminal(mask, 3) for mask in (1, 8, 9)) == (0, 2, 6)

    quit_value = algebra.add(algebra.const(2), algebra.scale(4, c))
    successor_value_numerator = algebra.add(
        algebra.const(2), algebra.scale(4, c)
    )
    # Continue gives zero if player 0 quits and V_next otherwise.
    assert quit_value == successor_value_numerator

    # At the next support-9 phase its current value is 2+4*c_next.  Clearing
    # the positive denominator in
    #   2+4*c_next = (2+4*c)/(1-c)
    # gives exactly c_next=(3/2)*c/(1-c).
    active_equality = algebra.sub(
        algebra.mul(
            algebra.sub(one, c),
            algebra.add(algebra.const(2), algebra.scale(4, c_next)),
        ),
        successor_value_numerator,
    )
    transport = algebra.sub(
        algebra.scale(2, algebra.mul(algebra.sub(one, c), c_next)),
        algebra.scale(3, c),
    )
    assert active_equality == algebra.scale(2, transport)

    # The transported hazard strictly increases on 0<c,c_next<1.
    cleared_increment = algebra.sub(
        algebra.scale(2, algebra.mul(algebra.sub(one, c), c_next)),
        algebra.scale(2, algebra.mul(algebra.sub(one, c), c)),
    )
    positive_increment = algebra.mul(
        c, algebra.add(one, algebra.scale(2, c))
    )
    # On transport=0, 2(1-c)(c_next-c)=c(1+2c).
    assert algebra.sub(
        algebra.sub(cleared_increment, positive_increment), transport
    ) == {}


def assert_support_three_player_three_bound() -> None:
    """Collapse an arbitrary finite support-3 block to its survival."""

    assert tuple(terminal(mask, 3) for mask in (1, 2, 3)) == (0, 0, 2)

    # Every absorbed payoff in the block is <=2.  If aggregate is the
    # absorption-weighted payoff and survival is S, then aggregate<=2(1-S).
    upper_entry = algebra.add(
        algebra.scale(2, algebra.sub(one, survival)),
        algebra.mul(
            survival,
            algebra.add(algebra.const(2), algebra.scale(4, c_first)),
        ),
    )
    assert upper_entry == algebra.add(
        algebra.const(2),
        algebra.scale(4, algebra.mul(survival, c_first)),
    )
    assert algebra.sub(
        algebra.add(algebra.const(2), algebra.scale(4, c_first)),
        upper_entry,
    ) == algebra.scale(
        4, algebra.mul(algebra.sub(one, survival), c_first)
    )

    # Keep the aggregate symbol explicit: the exact entry value is
    # aggregate + S*(2+4c_first), and the preceding bound is equivalent to
    # aggregate<=2(1-S).
    exact_entry = algebra.add(
        aggregate,
        algebra.mul(
            survival,
            algebra.add(algebra.const(2), algebra.scale(4, c_first)),
        ),
    )
    assert algebra.sub(upper_entry, exact_entry) == algebra.sub(
        algebra.scale(2, algebra.sub(one, survival)), aggregate
    )


def assert_cycle_gap() -> None:
    """Check the positive endpoint gap after c_last>=c_first."""

    # The gap between the last-9 required successor value and the largest
    # value the 3 block can return, with c_last relaxed down to c_first, is
    #   6*c_first/(1-c_first)-4*c_first
    # = 2*c_first*(1+2*c_first)/(1-c_first) > 0.
    cleared_gap = algebra.sub(
        algebra.scale(6, c_first),
        algebra.scale(
            4, algebra.mul(c_first, algebra.sub(one, c_first))
        ),
    )
    assert cleared_gap == algebra.scale(
        2,
        algebra.mul(c_first, algebra.add(one, algebra.scale(2, c_first))),
    )

    # Monotonicity in c_last needs no calculus after clearing denominators:
    # odds(c_last)-odds(c_first) has numerator c_last-c_first.
    odds_difference_numerator = algebra.sub(
        algebra.mul(c_last, algebra.sub(one, c_first)),
        algebra.mul(c_first, algebra.sub(one, c_last)),
    )
    assert odds_difference_numerator == algebra.sub(c_last, c_first)


def main() -> None:
    constant_pair.assert_constant_pair_support_exclusion()
    assert_support_nine_player_three_transport()
    assert_support_three_player_three_bound()
    assert_cycle_gap()
    assert_credible_first_unchanged()

    print("exact all-period support-3/9 cycle exclusion passed")
    print("support-9 self transport strictly raises player-0 hazards")
    print("a finite support-3 block cannot return player 3's required value")
    print("scope: finite strict 3/9 cycles; boundary/nonperiodic paths remain")


if __name__ == "__main__":
    main()
