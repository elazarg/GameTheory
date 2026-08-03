#!/usr/bin/env python3
"""Give every strict five-mask support-6 return one clock constant.

The run-compressed residual language has exactly six support-6 return
skeletons.  This checker composes their exact value certificates and proves
that every such finite strict excursion satisfies

    A - a >= (1/50) * (1-S),

where ``a,A`` are player 1's endpoint hazards and ``S`` is excursion
survival.  The three ingredients are:

* every singleton-word return has the stronger constant ``1/2``;
* both arbitrary support-9-run returns have constant ``1/50``; and
* both returns ending in an arbitrary support-3 block have constant ``1/12``.

This is a common charged rank for the six support-6-return families, not yet
a Q122 potential on the full lifted relation.  In particular, this checker
does not charge every 3/9-only edge, prove the five-mask atlas exhaustive, or
cover boundary/nonperiodic paths.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_core_residual_language as residual  # noqa: E402
import block_pair_r0_singleton_bridge_ranks as singleton  # noqa: E402
import block_pair_r0_support3_block_clock_charge as support_three  # noqa: E402
import block_pair_r0_support9_run_clock_charge as support_nine  # noqa: E402


Q = Fraction
one = algebra.one


SINGLETON_RETURNS = frozenset({(6, 1, 6), (6, 2, 1, 6)})
SUPPORT_NINE_RETURNS = frozenset({(6, 9, 6), (6, 2, 9, 6)})
SUPPORT_THREE_RETURNS = frozenset(
    {(6, 9, 3, 6), (6, 2, 9, 3, 6)}
)


def assert_singleton_word_clock_charge() -> None:
    """Strengthen the singleton-word identity to a 1/2 clock charge."""

    singleton.assert_arbitrary_singleton_word_return_rank()
    incoming = algebra.var(0)
    endpoint = algebra.var(1)
    survival = algebra.var(2)

    bellman = algebra.sub(
        algebra.mul(
            survival,
            algebra.mul(
                algebra.sub(one, incoming),
                algebra.add(algebra.const(2), algebra.scale(4, endpoint)),
            ),
        ),
        algebra.add(algebra.const(2), algebra.scale(4, incoming)),
    )
    cleared_increment = algebra.scale(
        2,
        algebra.mul(
            survival,
            algebra.mul(
                algebra.sub(one, incoming),
                algebra.sub(endpoint, incoming),
            ),
        ),
    )
    positive_factor = algebra.mul(
        algebra.add(one, algebra.scale(2, incoming)),
        algebra.sub(
            one,
            algebra.mul(survival, algebra.sub(one, incoming)),
        ),
    )
    assert algebra.sub(
        algebra.sub(cleared_increment, positive_factor),
        algebra.scale(Q(1, 2), bellman),
    ) == {}

    # The right side dominates 1-S by the exact positive remainder below,
    # while the multiplier 2*S*(1-a) is at most 2.  Division therefore gives
    # A-a >= (1/2)(1-S).
    assert algebra.sub(
        positive_factor, algebra.sub(one, survival)
    ) == algebra.mul(
        incoming,
        algebra.add(
            algebra.sub(algebra.const(2), survival),
            algebra.scale(2, algebra.mul(survival, incoming)),
        ),
    )
    assert algebra.sub(
        algebra.const(2),
        algebra.scale(
            2, algebra.mul(survival, algebra.sub(one, incoming))
        ),
    ) == algebra.scale(
        2,
        algebra.add(
            algebra.sub(one, survival),
            algebra.mul(survival, incoming),
        ),
    )
    assert Q(1, 2) >= Q(1, 50)


def assert_common_return_partition() -> None:
    returns, _ = residual.enumerate_returns()
    assert SINGLETON_RETURNS.isdisjoint(SUPPORT_NINE_RETURNS)
    assert SINGLETON_RETURNS.isdisjoint(SUPPORT_THREE_RETURNS)
    assert SUPPORT_NINE_RETURNS.isdisjoint(SUPPORT_THREE_RETURNS)
    assert (
        SINGLETON_RETURNS | SUPPORT_NINE_RETURNS | SUPPORT_THREE_RETURNS
        == returns
    )


def assert_common_support_six_return_clock_charge() -> None:
    residual.replay_local_ingredients()
    assert_common_return_partition()
    assert_singleton_word_clock_charge()
    support_nine.assert_arbitrary_support9_run_clock_charge()
    support_three.assert_arbitrary_support_three_block_charge()
    assert min(Q(1, 2), Q(1, 50), Q(1, 12)) == Q(1, 50)


def main() -> None:
    assert_common_support_six_return_clock_charge()

    print("exact common five-mask support-6 return charge passed")
    print("all six skeletons satisfy A-a >= (1/50)*(one minus survival)")
    print("scope: finite strict support-6 returns in the five-mask atlas")
    print("not claimed: full lifted Q122 potential or boundary exhaustiveness")


if __name__ == "__main__":
    main()
