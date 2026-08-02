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


def row(*entries: int | str) -> Vector:
    assert len(entries) == N
    return tuple(Fraction(entry) for entry in entries)  # type: ignore[return-value]


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


PROBE7: Profile = (
    row(0, "0.16522170356273985", "0.36004751101005517", "0.00309885440544373"),
    row(0, "0.2772557810817455", "0.10352598956106553", "0.0913847116020705"),
    row("0.0267315311803091", "0.020676793842569298", 0, "0.17091235181773734"),
    row("0.052045220316467175", 0, 0, "0.16926365617497965"),
    row("0.08273273308844842", 0, "0.003052178437271827", "0.09474701474858958"),
    row("0.13199085412333914", 0, "0.005125670044536747", "0.0645494642553428"),
    row("0.2269934754158264", 0, "0.01716868271968403", "0.017796223867593757"),
)


PROBE8: Profile = (
    row(0, "0.1644942037193029", "0.3629716549827152", "0.0021515385332348193"),
    row(0, "0.27810823459436834", "0.10657466013671703", "0.08337460126378005"),
    row("0.011277139199222767", "0.03430308090689961", 0, "0.1448951624514262"),
    row("0.035072011028573435", 0, 0, "0.18633524286502073"),
    row("0.0545201477666102", 0, 0, "0.10476552941131143"),
    row("0.08708012989608252", 0, "0.004472001868095843", "0.07334350335658137"),
    row("0.14063530881316397", 0, "0.01832340562025975", "0.023662895844810065"),
    row("0.22389072752676623", 0, "0.010001222344247837", 0),
)


PROBE9: Profile = (
    row("0.0677978954735063", "0.09711579815975396", "0.2014140906304075", 0),
    row(0, "0.16114842555455805", "0.3665118358293827", "0.0009259727185888749"),
    row(0, "0.2747133661374002", "0.10416855457054033", "0.06899157256024269"),
    row(0, "0.06881262351645262", 0, "0.11115619986915734"),
    row("0.03700086140812547", "0.0028108359533432882", 0, "0.21533624858737327"),
    row("0.0590973234998729", 0, 0, "0.1477158250204429"),
    row("0.09455174911633533", 0, "0.0023830506994692194", "0.09303570869475032"),
    row("0.16335312910606112", 0, "0.04101044126539314", "0.0583009474140889"),
    row("0.24179957470881341", 0, "0.013027863495011041", 0),
)


PROBE10: Profile = (
    row("0.07277745612319007", "0.058513776850084374", "0.17293999317612632", 0),
    row("0.012634049717432148", "0.10113993371302372", "0.3498037584782408", 0),
    row(0, "0.16641513119743642", "0.08859484315937345", "0.011349538933208168"),
    row(0, "0.27489002670801677", "0.09602960571601163", "0.07216447334075"),
    row(0, "0.07391399102643259", 0, "0.11666583882692774"),
    row("0.03990665570488256", 0, 0, "0.22804160789457437"),
    row("0.06234808720736541", 0, 0, "0.1454884316037016"),
    row("0.10009482851467484", 0, "0.002358103909160937", "0.08632891562846907"),
    row("0.1803372885735847", 0, "0.062023053682255705", "0.07110169086644653"),
    row("0.25816693324387385", "0.0002497631438837164", "0.03292262314792359", 0),
)


PROBE11: Profile = (
    row("0.07077316250825261", "0.06049895706248606", "0.17873702678622672", 0),
    row("0.00870554163481225", "0.10205549180212525", "0.360823707435671", 0),
    row(0, "0.1684647388296799", "0.06509810769329116", "0.00970305238135889"),
    row(0, "0.28149267717706933", "0.09754546812153103", "0.07033032463990774"),
    row("0.002056179806325357", "0.06082548529141743", 0, "0.11501844773867301"),
    row("0.03569988191346543", "0.00897017315075594", 0, "0.21708955986796796"),
    row("0.06022555064968521", 0, 0, "0.16277294054550848"),
    row("0.09612766769407326", 0, 0, "0.09720955546489693"),
    row("0.17272500809879754", 0, "0.0509426542216618", "0.07639103843052555"),
    row("0.2531712893453341", 0, "0.024484008004624004", "0.008640071805916994"),
    row("0.05344187650893504", "0.013002213795958862", "0.06130568065116255", 0),
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


def local_action_differences(profile: Profile) -> tuple[Vector, ...]:
    """Quit-minus-Continue values using the prescribed successor payoff."""
    values = profile_values(profile)
    result = []
    for phase in range(len(profile)):
        successor = (phase + 1) % len(profile)
        differences = []
        for player in range(N):
            quit_value, absorption, survival = opponent_stage_values(
                profile[phase], player
            )
            continue_value = absorption + survival * values[successor][player]
            differences.append(quit_value - continue_value)
        result.append(tuple(differences))
    return tuple(result)  # type: ignore[return-value]


def assert_profile_payoff_equations(profile: Profile) -> None:
    values = profile_values(profile)
    for phase, probabilities in enumerate(profile):
        immediate, survival = phase_data(probabilities)
        successor = (phase + 1) % len(profile)
        for player in range(N):
            assert values[phase][player] == (
                immediate[player] + survival * values[successor][player]
            )


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
    assert_profile_payoff_equations(profile)
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

    period7_maximum, _ = evaluate_probe(
        "period 7", PROBE7, (14, 14, 11, 9, 13, 13, 13), Fraction(3, 250)
    )
    period8_maximum, _ = evaluate_probe(
        "period 8", PROBE8, (14, 14, 11, 9, 9, 13, 13, 5), Fraction(1, 120)
    )
    period9_maximum, _ = evaluate_probe(
        "period 9", PROBE9, (7, 14, 14, 10, 11, 9, 13, 13, 5), Fraction(9, 2500)
    )
    period10_maximum, _ = evaluate_probe(
        "period 10",
        PROBE10,
        (7, 7, 14, 14, 10, 9, 9, 13, 13, 7),
        Fraction(17, 10000),
    )
    assert period7_maximum < period6_maximum
    assert period8_maximum < period7_maximum
    assert period9_maximum < period8_maximum
    assert period10_maximum < period9_maximum

    period11_maximum, period11_gains = evaluate_probe(
        "period 11",
        PROBE11,
        (7, 7, 14, 14, 11, 11, 9, 9, 13, 13, 7),
        Fraction(1, 10**10),
    )
    assert period11_maximum < Fraction(1, 10**12)
    assert period11_maximum < period10_maximum

    differences = local_action_differences(PROBE11)
    active_residuals = []
    inactive_differences = []
    for phase in range(len(PROBE11)):
        for player in range(N):
            if PROBE11[phase][player] == 0:
                inactive_differences.append(differences[phase][player])
            else:
                active_residuals.append(abs(differences[phase][player]))
    assert max(active_residuals) < Fraction(1, 10**12)
    assert max(inactive_differences) < 0
    assert max(period11_gains.values()) == period11_maximum
    print(f"period 11 exact signed maximum = {period11_maximum}")
    print(
        "period 11 inactive D range ~= "
        f"[{float(min(inactive_differences)):.15f}, "
        f"{float(max(inactive_differences)):.15f}]"
    )


if __name__ == "__main__":
    main()
