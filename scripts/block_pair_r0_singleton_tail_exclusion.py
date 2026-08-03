#!/usr/bin/env python3
"""Exclude infinite strict singleton tails in the perturbed core.

Suppose the live spine eventually stays forever at singleton support 1
(only player 0 may quit) or singleton support 2 (only player 1 may quit).
The hazards may vary arbitrarily and may have either finite or infinite
total clock.

At support 1, player 3 receives zero whether player 0 eventually quits or
play never absorbs.  Quitting immediately gives player 3

    (1-x) r_3({3}) + x r_3({0,3}) = 2+4x >= 2.

At support 2, player 3 again receives zero on-path, while quitting
immediately gives exactly 2 whether or not player 1 also quits.  Thus either
tail has a deviation gain at least two, independently of its future hazards.

This is a terminal-payoff argument for an actually infinite singleton tail.
It does not exclude long finite singleton blocks that later leave, and it
does not assign an edgewise Q122 potential.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402


one = algebra.one


def assert_support_one_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(1, 3) == 0
    assert terminal(8, 3) == 2
    assert terminal(9, 3) == 6

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, owner_hazard)),
        algebra.scale(6, owner_hazard),
    )
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.add(
        algebra.const(2), algebra.scale(4, owner_hazard)
    )


def assert_support_two_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(2, 3) == 0
    assert terminal(8, 3) == 2
    assert terminal(10, 3) == 2

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, owner_hazard)),
        algebra.scale(2, owner_hazard),
    )
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.const(2)


def assert_no_infinite_singleton_tail() -> None:
    assert_support_one_tail_gap()
    assert_support_two_tail_gap()


def main() -> None:
    assert_no_infinite_singleton_tail()

    print("exact infinite singleton-tail exclusion passed")
    print("support-1 and support-2 tails have player-3 deviation gap >=2")
    print("scope: actually infinite tails; finite blocks/potential remain separate")


if __name__ == "__main__":
    main()
