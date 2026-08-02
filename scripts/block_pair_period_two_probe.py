#!/usr/bin/env python3
"""Exact evaluation of a rational period-two block-pair probe.

This script does not certify optimality.  It records a reproducible rational
point for the public support word [14, 13] and evaluates its *full* periodic
stopping cap at both start phases.  Against periodic opponents, a pure best
response is one of:

* quit at the current phase;
* continue once and quit at the other phase; or
* never quit (while opponents may still absorb the game).

All three choices are evaluated with ``Fraction`` arithmetic.  The stored
terminal table is scaled by two relative to the normalized game.  At this
point the exact maximum regret is below 71/1000 in the stored scale.  The
script also computes prescribed-tail one-stage regret and checks that it is
strictly smaller, guarding against accidental identification of the two
criteria.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


Vector = tuple[Fraction, Fraction, Fraction, Fraction]
Profile = tuple[Vector, Vector]


ZERO_VECTOR: Vector = (Fraction(0),) * N  # type: ignore[assignment]


# A high-precision numerical minimizer was rounded to these exact decimals.
# Phase 0 has support mask 14; phase 1 has support mask 13.
PROBE: Profile = (
    (
        Fraction(0),
        Fraction("0.2045670440350683"),
        Fraction("0.29614132682840916"),
        Fraction("0.02710180329620997"),
    ),
    (
        Fraction("0.23339275153936467"),
        Fraction(0),
        Fraction("0.02852213099491344"),
        Fraction("0.24646088764746632"),
    ),
)


def bit(mask: int, player: int) -> int:
    return (mask >> player) & 1


def action_probability(mask: int, probabilities: Vector) -> Fraction:
    result = Fraction(1)
    for player, probability in enumerate(probabilities):
        result *= probability if bit(mask, player) else 1 - probability
    return result


def phase_data(probabilities: Vector) -> tuple[Vector, Fraction]:
    immediate = [Fraction(0)] * N
    for mask in range(1, 1 << N):
        probability = action_probability(mask, probabilities)
        for player in range(N):
            immediate[player] += probability * TERMINAL[mask][player]
    survival = action_probability(0, probabilities)
    return tuple(immediate), survival  # type: ignore[return-value]


def solve_periodic_affine(
    immediate0: Fraction,
    survival0: Fraction,
    immediate1: Fraction,
    survival1: Fraction,
) -> tuple[Fraction, Fraction]:
    """Solve v0=g0+s0*v1 and v1=g1+s1*v0 exactly."""
    denominator = 1 - survival0 * survival1
    assert denominator > 0
    value0 = (immediate0 + survival0 * immediate1) / denominator
    value1 = (immediate1 + survival1 * immediate0) / denominator
    return value0, value1


def profile_values(profile: Profile) -> Profile:
    phase0, survival0 = phase_data(profile[0])
    phase1, survival1 = phase_data(profile[1])
    values0 = []
    values1 = []
    for player in range(N):
        value0, value1 = solve_periodic_affine(
            phase0[player], survival0, phase1[player], survival1
        )
        values0.append(value0)
        values1.append(value1)
    return tuple(values0), tuple(values1)  # type: ignore[return-value]


def opponent_stage_values(
    probabilities: Vector, player: int
) -> tuple[Fraction, Fraction, Fraction]:
    """Return (quit payoff, opponent absorption payoff, opponent survival)."""
    quit_value = Fraction(0)
    opponent_absorption = Fraction(0)
    opponent_survival = Fraction(1)
    for opponent, probability in enumerate(probabilities):
        if opponent != player:
            opponent_survival *= 1 - probability

    for opponent_mask in range(1 << N):
        if bit(opponent_mask, player):
            continue
        probability = Fraction(1)
        for opponent, quit_probability in enumerate(probabilities):
            if opponent == player:
                continue
            probability *= (
                quit_probability
                if bit(opponent_mask, opponent)
                else 1 - quit_probability
            )
        quit_value += probability * TERMINAL[
            opponent_mask | (1 << player)
        ][player]
        if opponent_mask:
            opponent_absorption += (
                probability * TERMINAL[opponent_mask][player]
            )
    return quit_value, opponent_absorption, opponent_survival


def stopping_choices(
    profile: Profile, player: int, start: int
) -> dict[str, Fraction]:
    quit_values = []
    opponent_absorption = []
    opponent_survival = []
    for phase in range(2):
        quit_value, absorption, survival = opponent_stage_values(
            profile[phase], player
        )
        quit_values.append(quit_value)
        opponent_absorption.append(absorption)
        opponent_survival.append(survival)

    never0, never1 = solve_periodic_affine(
        opponent_absorption[0],
        opponent_survival[0],
        opponent_absorption[1],
        opponent_survival[1],
    )
    never = (never0, never1)
    successor = 1 - start
    return {
        "Quit": quit_values[start],
        "WaitThenQuit": (
            opponent_absorption[start]
            + opponent_survival[start] * quit_values[successor]
        ),
        "Never": never[start],
    }


def full_stopping_gains(
    profile: Profile,
) -> dict[tuple[int, int, str], Fraction]:
    values = profile_values(profile)
    result = {}
    for phase in range(2):
        for player in range(N):
            for choice, payoff in stopping_choices(profile, player, phase).items():
                result[(phase, player, choice)] = payoff - values[phase][player]
    return result


def prescribed_tail_one_stage_gains(profile: Profile) -> list[Fraction]:
    values = profile_values(profile)
    result = []
    for phase in range(2):
        successor = 1 - phase
        for player in range(N):
            quit_value, absorption, survival = opponent_stage_values(
                profile[phase], player
            )
            continue_value = absorption + survival * values[successor][player]
            result.append(max(quit_value, continue_value) - values[phase][player])
    return result


def main() -> None:
    assert tuple(
        sum((1 << player) for player, probability in enumerate(phase) if probability)
        for phase in PROBE
    ) == (14, 13)
    gains = full_stopping_gains(PROBE)
    maximum_key, maximum_gain = max(gains.items(), key=lambda item: item[1])
    one_stage_maximum = max(prescribed_tail_one_stage_gains(PROBE))

    # Exact positive witness: this particular period-two profile is a
    # 71/1000-terminal equilibrium in the stored (twice-normalized) scale.
    assert maximum_gain < Fraction(71, 1000)
    assert maximum_gain > Fraction(7, 100)
    assert one_stage_maximum < maximum_gain

    # The numerical optimum was guided by these seven nearly binding cap
    # constraints.  Keep the tolerance rational and much wider than rounding
    # error; this is a regression hint, not an optimality claim.
    expected_near_active = {
        (1, 0, "WaitThenQuit"),
        (1, 0, "Never"),
        (0, 1, "Never"),
        (1, 2, "WaitThenQuit"),
        (1, 2, "Never"),
        (0, 3, "WaitThenQuit"),
        (0, 3, "Never"),
    }
    near_active = {
        key
        for key, gain in gains.items()
        if maximum_gain - gain < Fraction(1, 10**12)
    }
    assert near_active == expected_near_active

    print("exact rational [14,13] probe passed")
    print(f"stored-scale full periodic cap = {maximum_gain}")
    print(f"stored-scale full periodic cap ~= {float(maximum_gain):.15f}")
    print(f"normalized full periodic cap ~= {float(maximum_gain / 2):.15f}")
    print(f"stored-scale prescribed-tail one-stage max ~= {float(one_stage_maximum):.15f}")
    print(f"maximizing branch = {maximum_key}")


if __name__ == "__main__":
    main()
