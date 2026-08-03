#!/usr/bin/env python3
"""Exact exclusion of constant pair-support periodic profiles.

The table is the block-pair quitting game with
``r_0({0})=-2+11/100``.  Fix a pair ``{j,k}`` and suppose that precisely j
and k use hazards strictly between zero and one at every phase of a finite
periodic profile.

Put ``z_i=(V_i-q_i)/2``, where ``q_i`` is player i's solo payoff.  Active
indifference at a pair-support phase gives

    z_j^+ = a_jk * odds(x_k),
    z_j   = b_jk * x_k,

where

    a_jk = (r_j({j,k})-r_j({k}))/2,
    b_jk = (r_j({j,k})-q_j)/2.

When ``a_jk`` is nonzero, eliminating ``x_k`` yields the scalar predecessor
map

    z_j = f_jk(z_j^+) = b_jk*z_j^+/(a_jk+z_j^+).

For supports 3={0,1} and 9={0,3}, both coordinate maps are strictly
increasing on their valid odds rays.  A monotone self-map of a line has no
nonconstant finite periodic orbit, so both active-coordinate sequences are
constant; the hazards are then constant too.  The imported exact stationary
pair-support fences exclude the resulting roots.

For supports 5, 6, 10, and 12, one displayed active coordinate is identically
zero on one side of every phase and has a strict sign on the other side.
Consecutive use of that support is therefore impossible before any inactive
inequality is considered.

Hazard-zero phases reduce to a smaller support.  Hazard-one phases belong to
the separately certified sure-quitter boundary.  This checker covers only a
constant two-player support; transitions between different supports remain
open.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_singleton_perturbation_fences as fences  # noqa: E402
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


Q = Fraction
THETA = Q(11, 100)
PAIR_MASKS = (3, 5, 6, 9, 10, 12)


def terminal(mask: int, player: int) -> Fraction:
    value = Q(TERMINAL[mask][player])
    if mask == 1 and player == 0:
        value += THETA
    return value


SOLO = tuple(terminal(1 << player, player) for player in range(N))


def coefficients(player: int, opponent: int) -> tuple[Fraction, Fraction]:
    pair = (1 << player) | (1 << opponent)
    active_slope = (
        terminal(pair, player) - terminal(1 << opponent, player)
    ) / 2
    current_slope = (terminal(pair, player) - SOLO[player]) / 2
    return active_slope, current_slope


COEFFICIENTS = {
    (player, opponent): coefficients(player, opponent)
    for player in range(N)
    for opponent in range(N)
    if player != opponent
}


EXPECTED_COEFFICIENTS = {
    (0, 1): (Q(-9, 2), Q(-311, 200)),
    (0, 2): (Q(2), Q(189, 200)),
    (0, 3): (Q(-1), Q(-411, 200)),
    (1, 0): (Q(-9, 2), Q(-3, 2)),
    (1, 2): (Q(0), Q(-1)),
    (1, 3): (Q(3), Q(2)),
    (2, 0): (Q(0), Q(-1)),
    (2, 1): (Q(3), Q(2)),
    (2, 3): (Q(-5, 2), Q(1, 2)),
    (3, 0): (Q(3), Q(2)),
    (3, 1): (Q(1), Q(0)),
    (3, 2): (Q(-3), Q(0)),
}


def players(mask: int) -> tuple[int, int]:
    result = tuple(player for player in range(N) if mask & (1 << player))
    assert len(result) == 2
    return result  # type: ignore[return-value]


def main() -> None:
    assert N == 4
    assert COEFFICIENTS == EXPECTED_COEFFICIENTS

    monotone_masks = (3, 9)
    for mask in monotone_masks:
        left, right = players(mask)
        for player, opponent in ((left, right), (right, left)):
            active_slope, current_slope = COEFFICIENTS[player, opponent]
            # f'(z)=a*b/(a+z)^2 on the valid odds ray.
            assert active_slope != 0
            assert active_slope * current_slope > 0

    # The exact perturbation checker reconstructs a nonzero stationary gain
    # witness on every singleton and pair support, including masks 3 and 9.
    fences.assert_direct_support_fences(fences.perturbed_gains())

    # Each remaining pair has an active coordinate that cannot be both the
    # current value and the preceding phase's successor value under constant
    # positive pair support.
    degeneracies = {
        # mask: (player, successor coefficient a, current coefficient b)
        5: (2, Q(0), Q(-1)),
        6: (1, Q(0), Q(-1)),
        10: (3, Q(1), Q(0)),
        12: (3, Q(-3), Q(0)),
    }
    for mask, (player, active_slope, current_slope) in degeneracies.items():
        left, right = players(mask)
        opponent = right if player == left else left
        assert COEFFICIENTS[player, opponent] == (
            active_slope,
            current_slope,
        )
        assert (active_slope == 0) != (current_slope == 0)
        assert active_slope != current_slope

    assert set(monotone_masks) | set(degeneracies) == set(PAIR_MASKS)
    print("exact constant pair-support periodic exclusion passed")
    print(f"theta = {THETA}")
    print("monotone-to-stationary masks = 3,9")
    print("zero-versus-strict coordinate masks = 5,6,10,12")
    print("all six constant positive pair supports are excluded")
    print("scope: transitions between different supports remain open")


if __name__ == "__main__":
    main()
