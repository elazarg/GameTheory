#!/usr/bin/env python3
"""Exclude every one-sided infinite strict path in the five-mask core.

Three exact ingredients cover the possible tails.

* A path visiting support 6 only finitely often eventually either stays in a
  singleton block or lives on supports 3/9.  The companion tail theorems
  exclude both strict cases.
* If support 6 is visited infinitely often, let ``a_n`` be player 1's hazard
  at its nth visit and ``P_n`` the absorption probability of the finite
  intervening block.  The common return theorem gives

      a_(n+1)-a_n >= P_n/50.

  Hence ``a_n`` increases to a limit ``L>=a_0>0`` and ``P_n->0``.
* Player 2's active equality at the nth support 6 fixes the value just after
  that phase to ``2+6a_n/(1-a_n)``.  Its current value at the next support 6
  is ``2+4a_(n+1)``.  Player 2's terminal rewards lie in ``[-1,8]``, so
  transport across a block with absorption probability ``P_n`` changes a
  continuation value by at most ``9P_n``.  Taking limits would give

      2+6L/(1-L) = 2+4L,

  whose cleared positive gap is ``2L(1+2L)``.  This contradicts ``L>0``.

Thus no exact one-sided path can remain forever in the strict interiors of
the five charts ``{1,2,3,6,9}``.  This is not atlas exhaustiveness and does
not exclude sequences of approximate paths escaping to zero/sure walls,
outside masks 4/8, or chattering directional limits.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_core_return_clock_charge as returns  # noqa: E402
import block_pair_r0_singleton_tail_exclusion as singleton_tails  # noqa: E402
import block_pair_r0_support3_9_one_sided_exclusion as pair_tails  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402


Q = Fraction
one = algebra.one


def assert_return_clock_limit_packet() -> None:
    """Record the exact telescoping implication of the common charge."""

    incoming = algebra.var(0)
    following = algebra.var(1)
    block_absorption = algebra.var(2)
    charged_slack = algebra.sub(
        algebra.sub(following, incoming),
        algebra.scale(Q(1, 50), block_absorption),
    )
    # Summing charged_slack>=0 over N returns gives
    #   sum P_n <= 50*(a_N-a_0) <= 50.
    telescoped_bound = algebra.sub(
        algebra.scale(50, algebra.sub(following, incoming)),
        block_absorption,
    )
    assert telescoped_bound == algebra.scale(50, charged_slack)
    # In particular P_n->0, while strictness and monotonicity give
    # a_n->L with L>=a_0>0.


def assert_player_two_block_transport_bound() -> None:
    """Replay the payoff diameter controlling a vanishing-clock block."""

    player_two_rewards = tuple(terminal(mask, 2) for mask in range(1, 16))
    assert min(player_two_rewards) == -1
    assert max(player_two_rewards) == 8
    assert Q(8) - Q(-1) == 9

    absorption = algebra.var(0)
    absorbed_average = algebra.var(1)
    endpoint_value = algebra.var(2)
    entry_value = algebra.add(
        algebra.mul(absorption, absorbed_average),
        algebra.mul(algebra.sub(one, absorption), endpoint_value),
    )
    assert algebra.sub(entry_value, endpoint_value) == algebra.mul(
        absorption, algebra.sub(absorbed_average, endpoint_value)
    )
    # Both the conditional absorbed average and endpoint continuation value
    # lie in [-1,8], so the displayed difference has modulus at most 9P.


def assert_support_six_limit_gap() -> None:
    """Derive the incompatible player-2 values at consecutive resets."""

    assert (terminal(2, 2), terminal(4, 2), terminal(6, 2)) == (0, 2, 6)
    incoming_hazard = algebra.var(0)
    following_hazard = algebra.var(1)

    # If player 2 continues at support 6, player 1 quits alone with payoff
    # zero or play reaches the successor value W.  Quitting gives 2 or 6.
    # Active equality therefore requires
    #   (1-a)W = 2(1-a)+6a = 2+4a.
    successor_numerator = algebra.add(
        algebra.const(2), algebra.scale(4, incoming_hazard)
    )
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, incoming_hazard)),
        algebra.scale(6, incoming_hazard),
    )
    assert successor_numerator == quit_payoff

    # At the following support 6, player 2's current value is its Quit
    # payoff 2+4A.  The numerator of W(a)-(2+4A) is recorded exactly.
    next_current = algebra.add(
        algebra.const(2), algebra.scale(4, following_hazard)
    )
    cleared_difference = algebra.sub(
        successor_numerator,
        algebra.mul(algebra.sub(one, incoming_hazard), next_current),
    )
    assert cleared_difference == algebra.sum_polys(
        [
            algebra.scale(6, incoming_hazard),
            algebra.scale(-4, following_hazard),
            algebra.scale(
                4, algebra.mul(incoming_hazard, following_hazard)
            ),
        ]
    )

    # At a common limit A,a->L this becomes 2L(1+2L)>0, whereas the
    # vanishing block-transport error requires it to tend to zero.
    limit = algebra.var(2)
    limit_gap = algebra.sum_polys(
        [
            algebra.scale(6, limit),
            algebra.scale(-4, limit),
            algebra.scale(4, algebra.mul(limit, limit)),
        ]
    )
    assert limit_gap == algebra.scale(
        2, algebra.mul(limit, algebra.add(one, algebra.scale(2, limit)))
    )


def assert_no_infinite_strict_core_path() -> None:
    returns.assert_common_support_six_return_clock_charge()
    singleton_tails.assert_no_infinite_singleton_tail()
    pair_tails.assert_no_one_sided_strict_support3_9_path()
    assert_return_clock_limit_packet()
    assert_player_two_block_transport_bound()
    assert_support_six_limit_gap()


def main() -> None:
    assert_no_infinite_strict_core_path()

    print("exact one-sided strict five-mask core exclusion passed")
    print("infinitely many support-6 resets contradict the player-2 limit gap")
    print("singleton and support-3/9 tails are excluded by companion theorems")
    print("scope: strict interiors only; walls/atlas exits/chattering remain")


if __name__ == "__main__":
    main()
