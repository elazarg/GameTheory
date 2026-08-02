#!/usr/bin/env python3
"""Exact evaluation of rational periodic block-pair probes.

This script does not certify optimality.  It records reproducible rational
points for two public support words and evaluates their *full* periodic
stopping caps at every start phase.  Against K-periodic opponents, a pure
best response quits at one of the next K phases or never quits (while the
opponents may still absorb the game).  Every such choice is evaluated with
``Fraction`` arithmetic.

The stored terminal table is scaled by two relative to the normalized game.
The certified upper bounds are

    period 2, support [14,13]: cap < 71/1000;
    period 3, support [14,15, 9]: cap < 27/500.

These are positive-regret witnesses, not exact equilibria or lower-bound
certificates.  The script also evaluates prescribed-tail one-stage regret,
guarding against accidental identification of that weaker quantity with the
full periodic stopping cap.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


Vector = tuple[Fraction, Fraction, Fraction, Fraction]
Profile = tuple[Vector, ...]


PROBE2: Profile = (
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


PROBE3: Profile = (
    (
        Fraction(0),
        Fraction("0.25211250978300337"),
        Fraction("0.3597769308022619"),
        Fraction("0.02438048260788807"),
    ),
    (
        Fraction("0.12732143086200806"),
        Fraction("0.043620943029017346"),
        Fraction("0.023451920489597874"),
        Fraction("0.21734406260488953"),
    ),
    (
        Fraction("0.21171786209189872"),
        Fraction(0),
        Fraction(0),
        Fraction("0.2437129392949335"),
    ),
)


PROBE4: Profile = (
    (Fraction(0), Fraction("0.21270937143995297"), Fraction("0.3677580056758998"), Fraction("0.010929049872543423")),
    (Fraction(0), Fraction("0.1447880461768622"), Fraction("0.019148593990112848"), Fraction("0.08520181633212268")),
    (Fraction("0.12817448143033464"), Fraction(0), Fraction(0), Fraction("0.2358367839526585")),
    (Fraction("0.22676759057078766"), Fraction(0), Fraction("0.01834429719375438"), Fraction("0.1607316926116511")),
)


PROBE5: Profile = (
    (Fraction(0), Fraction("0.1789955198842902"), Fraction("0.3650371702456783"), Fraction("0.00848224271611726")),
    (Fraction(0), Fraction("0.23524102181073978"), Fraction("0.06364736700455524"), Fraction("0.09914347022273425")),
    (Fraction("0.07919318635331213"), Fraction(0), Fraction(0), Fraction("0.22447689829620973")),
    (Fraction("0.12900619084205361"), Fraction(0), Fraction(0), Fraction("0.15550741683590857")),
    (Fraction("0.2289059528916575"), Fraction(0), Fraction("0.019615839278923516"), Fraction("0.054105586425012786")),
)


PROBE6: Profile = (
    (Fraction(0), Fraction("0.16557279787009302"), Fraction("0.35638705696149003"), Fraction("0.004356326280225217")),
    (Fraction(0), Fraction("0.2751507583083422"), Fraction("0.09667876252097149"), Fraction("0.09991369714220717")),
    (Fraction("0.05027724229709349"), Fraction("0.002072270726973805"), Fraction(0), Fraction("0.20421479360647357")),
    (Fraction("0.0805015461625366"), Fraction(0), Fraction(0), Fraction("0.1449189339382235")),
    (Fraction("0.1324231268581428"), Fraction(0), Fraction("0.005532837359838398"), Fraction("0.10147483113352697")),
    (Fraction("0.229034958748282"), Fraction(0), Fraction("0.02205708224644292"), Fraction("0.03198003136085553")),
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


def cyclic_affine_values(
    immediate: tuple[Fraction, ...], survival: tuple[Fraction, ...]
) -> tuple[Fraction, ...]:
    """Solve v_t=g_t+s_t*v_(t+1) on a finite cyclic spine."""
    period = len(immediate)
    assert period and len(survival) == period
    cycle_survival = Fraction(1)
    for probability in survival:
        cycle_survival *= probability
    denominator = 1 - cycle_survival
    assert denominator > 0

    result = []
    for start in range(period):
        numerator = Fraction(0)
        prefix_survival = Fraction(1)
        for delay in range(period):
            phase = (start + delay) % period
            numerator += prefix_survival * immediate[phase]
            prefix_survival *= survival[phase]
        assert prefix_survival == cycle_survival
        result.append(numerator / denominator)
    return tuple(result)


def profile_values(profile: Profile) -> tuple[Vector, ...]:
    data = tuple(phase_data(phase) for phase in profile)
    result = [[Fraction(0)] * N for _ in profile]
    for player in range(N):
        values = cyclic_affine_values(
            tuple(immediate[player] for immediate, _ in data),
            tuple(survival for _, survival in data),
        )
        for phase, value in enumerate(values):
            result[phase][player] = value
    return tuple(tuple(row) for row in result)  # type: ignore[return-value]


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
            opponent_absorption += probability * TERMINAL[opponent_mask][player]
    return quit_value, opponent_absorption, opponent_survival


def stopping_choices(
    profile: Profile, player: int, start: int
) -> dict[str, Fraction]:
    period = len(profile)
    stage = tuple(opponent_stage_values(phase, player) for phase in profile)
    quit_values = tuple(item[0] for item in stage)
    opponent_absorption = tuple(item[1] for item in stage)
    opponent_survival = tuple(item[2] for item in stage)
    never_values = cyclic_affine_values(opponent_absorption, opponent_survival)

    result = {}
    prefix_payoff = Fraction(0)
    prefix_survival = Fraction(1)
    for delay in range(period):
        phase = (start + delay) % period
        result[f"Quit+{delay}"] = (
            prefix_payoff + prefix_survival * quit_values[phase]
        )
        prefix_payoff += prefix_survival * opponent_absorption[phase]
        prefix_survival *= opponent_survival[phase]
    result["Never"] = never_values[start]
    return result


def full_stopping_gains(
    profile: Profile,
) -> dict[tuple[int, int, str], Fraction]:
    values = profile_values(profile)
    result = {}
    for phase in range(len(profile)):
        for player in range(N):
            for choice, payoff in stopping_choices(profile, player, phase).items():
                result[(phase, player, choice)] = payoff - values[phase][player]
    return result


def prescribed_tail_one_stage_gains(profile: Profile) -> list[Fraction]:
    values = profile_values(profile)
    result = []
    for phase in range(len(profile)):
        successor = (phase + 1) % len(profile)
        for player in range(N):
            quit_value, absorption, survival = opponent_stage_values(
                profile[phase], player
            )
            continue_value = absorption + survival * values[successor][player]
            result.append(max(quit_value, continue_value) - values[phase][player])
    return result


def support_word(profile: Profile) -> tuple[int, ...]:
    return tuple(
        sum(
            (1 << player)
            for player, probability in enumerate(phase)
            if probability
        )
        for phase in profile
    )


def evaluate_probe(
    name: str,
    profile: Profile,
    expected_support: tuple[int, ...],
    upper_bound: Fraction,
) -> tuple[Fraction, dict[tuple[int, int, str], Fraction]]:
    assert support_word(profile) == expected_support
    gains = full_stopping_gains(profile)
    maximum_key, maximum_gain = max(gains.items(), key=lambda item: item[1])
    one_stage_maximum = max(prescribed_tail_one_stage_gains(profile))
    assert maximum_gain < upper_bound
    assert one_stage_maximum < maximum_gain
    print(f"exact rational {name} probe passed")
    print(f"stored-scale full periodic cap ~= {float(maximum_gain):.15f}")
    print(f"normalized full periodic cap ~= {float(maximum_gain / 2):.15f}")
    print(
        "stored-scale prescribed-tail one-stage max ~= "
        f"{float(one_stage_maximum):.15f}"
    )
    print(f"maximizing branch = {maximum_key}")
    return maximum_gain, gains


def main() -> None:
    period2_maximum, period2_gains = evaluate_probe(
        "[14,13]", PROBE2, (14, 13), Fraction(71, 1000)
    )
    assert period2_maximum > Fraction(7, 100)
    period2_near_active = {
        key
        for key, gain in period2_gains.items()
        if period2_maximum - gain < Fraction(1, 10**12)
    }
    assert period2_near_active == {
        (1, 0, "Quit+1"),
        (1, 0, "Never"),
        (0, 1, "Never"),
        (1, 2, "Quit+1"),
        (1, 2, "Never"),
        (0, 3, "Quit+1"),
        (0, 3, "Never"),
    }

    period3_maximum, _ = evaluate_probe(
        "[14,15,9]", PROBE3, (14, 15, 9), Fraction(27, 500)
    )
    assert period3_maximum < period2_maximum

    period4_maximum, _ = evaluate_probe(
        "period 4", PROBE4, (14, 14, 9, 13), Fraction(37, 1000)
    )
    period5_maximum, _ = evaluate_probe(
        "period 5", PROBE5, (14, 14, 9, 9, 13), Fraction(1, 40)
    )
    period6_maximum, _ = evaluate_probe(
        "period 6", PROBE6, (14, 14, 11, 9, 13, 13), Fraction(17, 1000)
    )
    assert period4_maximum < period3_maximum
    assert period5_maximum < period4_maximum
    assert period6_maximum < period5_maximum


if __name__ == "__main__":
    main()
