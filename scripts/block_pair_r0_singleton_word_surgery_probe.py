#!/usr/bin/env python3
"""Numerical chamber-wall probe for the block-pair singleton perturbation.

This is deliberately a witness-generation experiment, not a certificate.
It follows the three certified period-eleven complementarity branches after
replacing player 0's singleton payoff by ``-2 + theta``.  For each support
word it reports the first active-hazard or inactive-gain chamber wall.  It can
then seed the adjacent support word obtained by adding or deleting the player
whose constraint is tight.

All mathematical claims used elsewhere must be replayed by exact interval or
rational arithmetic.  In particular, failure of these selected branches does
not exclude another word, a longer lasso, or a nonperiodic path.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from collections import deque
from pathlib import Path
import sys

import numpy as np
from scipy.optimize import root


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_period_eleven_certificate import (  # noqa: E402
    NEARBY_ROOT_CENTER_TEXT,
    NEARBY_SUPPORT_WORD,
    ROOT_CENTER_TEXT,
    SUPPORT_TEN_ROOT_CENTER_TEXT,
    SUPPORT_TEN_WORD,
    SUPPORT_WORD,
)
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


PERIOD = 11


@dataclass(frozen=True)
class Constraint:
    kind: str
    phase: int
    player: int
    slack: float


def bit(mask: int, player: int) -> bool:
    return bool(mask & (1 << player))


def payoff_table(theta: float) -> np.ndarray:
    table = np.zeros((1 << N, N), dtype=float)
    for mask, row in TERMINAL.items():
        table[mask] = row
    table[1, 0] += theta
    return table


def action_probability(mask: int, probabilities: np.ndarray) -> float:
    result = 1.0
    for player, probability in enumerate(probabilities):
        result *= probability if bit(mask, player) else 1.0 - probability
    return result


def phase_data(
    probabilities: np.ndarray, table: np.ndarray
) -> tuple[np.ndarray, float]:
    immediate = np.zeros(N)
    for mask in range(1, 1 << N):
        immediate += action_probability(mask, probabilities) * table[mask]
    survival = action_probability(0, probabilities)
    return immediate, survival


def cyclic_values(profile: np.ndarray, table: np.ndarray) -> np.ndarray:
    period = len(profile)
    immediate = np.empty((period, N))
    survival = np.empty(period)
    for phase in range(period):
        immediate[phase], survival[phase] = phase_data(profile[phase], table)

    cycle_survival = float(np.prod(survival))
    if abs(1.0 - cycle_survival) < 1e-12:
        # Keep unconstrained root finding away from the singular no-absorption
        # hypersurface.  Valid reported profiles are checked separately.
        return np.full((period, N), 1e12)
    values = np.empty((period, N))
    for start in range(period):
        numerator = np.zeros(N)
        prefix = 1.0
        for delay in range(period):
            phase = (start + delay) % period
            numerator += prefix * immediate[phase]
            prefix *= survival[phase]
        values[start] = numerator / (1.0 - cycle_survival)
    return values


def opponent_difference(
    probabilities: np.ndarray,
    successor: np.ndarray,
    player: int,
    table: np.ndarray,
) -> float:
    quit_value = 0.0
    absorption = 0.0
    opponent_survival = 1.0
    for opponent, probability in enumerate(probabilities):
        if opponent != player:
            opponent_survival *= 1.0 - probability

    for mask in range(1 << N):
        if bit(mask, player):
            continue
        probability = 1.0
        for opponent, hazard in enumerate(probabilities):
            if opponent == player:
                continue
            probability *= hazard if bit(mask, opponent) else 1.0 - hazard
        quit_value += probability * table[mask | (1 << player), player]
        if mask:
            absorption += probability * table[mask, player]
    return quit_value - absorption - opponent_survival * successor[player]


class Branch:
    def __init__(
        self,
        word: tuple[int, ...],
        center_text: tuple[tuple[str, ...], ...],
    ) -> None:
        self.word = tuple(word)
        self.period = len(word)
        self.slots = tuple(
            (phase, player)
            for phase, mask in enumerate(word)
            for player in range(N)
            if bit(mask, player)
        )
        center = np.array(
            [[float(entry) for entry in row] for row in center_text]
        )
        self.seed = np.array([center[slot] for slot in self.slots])

    @classmethod
    def from_profile(cls, word: tuple[int, ...], profile: np.ndarray) -> "Branch":
        text = tuple(tuple(str(x) for x in row) for row in profile)
        return cls(word, text)

    def profile(self, active: np.ndarray) -> np.ndarray:
        result = np.zeros((self.period, N))
        for value, slot in zip(active, self.slots):
            result[slot] = value
        return result

    def residual(self, active: np.ndarray, theta: float) -> np.ndarray:
        table = payoff_table(theta)
        profile = self.profile(active)
        values = cyclic_values(profile, table)
        return np.array(
            [
                opponent_difference(
                    profile[phase],
                    values[(phase + 1) % self.period],
                    player,
                    table,
                )
                for phase, player in self.slots
            ]
        )

    def solve(self, theta: float, seed: np.ndarray) -> np.ndarray:
        solution = root(lambda active: self.residual(active, theta), seed)
        if not solution.success or np.max(np.abs(solution.fun)) > 1e-6:
            raise RuntimeError(
                f"root failed at theta={theta}: {solution.message}; "
                f"residual={np.max(np.abs(solution.fun)):.3e}"
            )
        return solution.x

    def constraints(self, active: np.ndarray, theta: float) -> list[Constraint]:
        profile = self.profile(active)
        table = payoff_table(theta)
        values = cyclic_values(profile, table)
        constraints: list[Constraint] = []
        for phase, mask in enumerate(self.word):
            for player in range(N):
                if bit(mask, player):
                    constraints.append(
                        Constraint("active-zero", phase, player, profile[phase, player])
                    )
                    constraints.append(
                        Constraint(
                            "active-one", phase, player, 1.0 - profile[phase, player]
                        )
                    )
                else:
                    difference = opponent_difference(
                        profile[phase],
                        values[(phase + 1) % self.period],
                        player,
                        table,
                    )
                    constraints.append(
                        Constraint("inactive", phase, player, -difference)
                    )
        return constraints


BRANCHES = {
    "W10": Branch(SUPPORT_TEN_WORD, SUPPORT_TEN_ROOT_CENTER_TEXT),
    "W11": Branch(SUPPORT_WORD, ROOT_CENTER_TEXT),
    "W14": Branch(NEARBY_SUPPORT_WORD, NEARBY_ROOT_CENTER_TEXT),
}


def follow(label: str, stop: float = 0.12, step: float = 0.001) -> None:
    branch = BRANCHES[label]
    active = branch.solve(0.0, branch.seed)
    previous: Constraint | None = None
    first_invalid: tuple[float, Constraint] | None = None
    theta = 0.0
    while theta < stop - step / 2:
        theta = min(stop, theta + step)
        active = branch.solve(theta, active)
        tightest = min(branch.constraints(active, theta), key=lambda item: item.slack)
        if tightest.slack <= 0 and first_invalid is None:
            first_invalid = theta, tightest
            break
        previous = tightest

    if first_invalid is None:
        tightest = min(branch.constraints(active, theta), key=lambda item: item.slack)
        print(f"{label}: valid through theta={theta:.6f}; tightest={tightest}")
        return
    invalid_theta, invalid = first_invalid
    assert previous is not None
    print(
        f"{label}: wall in ({invalid_theta-step:.6f},{invalid_theta:.6f}); "
        f"before={previous}; after={invalid}"
    )


def constraint_value(
    branch: Branch,
    active: np.ndarray,
    theta: float,
    key: tuple[str, int, int],
) -> float:
    for constraint in branch.constraints(active, theta):
        if (constraint.kind, constraint.phase, constraint.player) == key:
            return constraint.slack
    raise AssertionError(f"missing constraint {key}")


def locate_wall(
    branch: Branch,
    key: tuple[str, int, int],
    lower: float,
    upper: float,
) -> tuple[float, np.ndarray]:
    lower_active = branch.solve(lower, branch.seed)
    upper_active = branch.solve(upper, lower_active)
    assert constraint_value(branch, lower_active, lower, key) > 0
    assert constraint_value(branch, upper_active, upper, key) < 0
    for _ in range(32):
        middle = (lower + upper) / 2.0
        middle_active = branch.solve(middle, lower_active)
        if constraint_value(branch, middle_active, middle, key) > 0:
            lower, lower_active = middle, middle_active
        else:
            upper, upper_active = middle, middle_active
    theta = (lower + upper) / 2.0
    active = branch.solve(theta, lower_active)
    return theta, active


def surgery_probe() -> None:
    # W10 and W11 meet on the same phase-4/player-0 chamber wall.  Record
    # their agreement; neither orientation is automatically valid after the
    # exchange, because complementarity also fixes the side of the wall.
    theta10, active10 = locate_wall(
        BRANCHES["W10"], ("inactive", 4, 0), 0.058, 0.059
    )
    theta11, active11 = locate_wall(
        BRANCHES["W11"], ("active-zero", 4, 0), 0.058, 0.059
    )
    profile10 = BRANCHES["W10"].profile(active10)
    profile11 = BRANCHES["W11"].profile(active11)
    print(
        "W10/W11 wall: "
        f"theta10={theta10:.12f}; theta11={theta11:.12f}; "
        f"profile distance={np.max(np.abs(profile10-profile11)):.3e}"
    )

    # W14 reaches x_(phase 2, player 3)=0.  Drop player 3 from that phase,
    # changing mask 14 to mask 6, and continue the adjacent algebraic sheet.
    theta14, active14 = locate_wall(
        BRANCHES["W14"], ("active-zero", 2, 3), 0.102, 0.103
    )
    profile14 = BRANCHES["W14"].profile(active14)
    word6 = list(NEARBY_SUPPORT_WORD)
    assert word6[2] == 14
    word6[2] = 6
    branch6 = Branch.from_profile(tuple(word6), profile14)
    active6 = branch6.solve(theta14 + 1e-7, branch6.seed)
    tight = min(
        branch6.constraints(active6, theta14 + 1e-7),
        key=lambda item: item.slack,
    )
    print(
        f"W14/W6 wall: theta={theta14:.12f}; "
        f"adjacent-side tightest={tight}"
    )
    theta = theta14 + 1e-7
    while theta < 0.11 - 1e-12:
        theta = min(0.11, theta + 0.00025)
        active6 = branch6.solve(theta, active6)
        tight = min(
            branch6.constraints(active6, theta), key=lambda item: item.slack
        )
        if tight.slack <= 0:
            print(f"W6 invalid at theta={theta:.9f}: {tight}")
            return
    profile6 = branch6.profile(active6)
    values6 = cyclic_values(profile6, payoff_table(theta))
    opponent_products = []
    for player in range(N):
        product = 1.0
        for phase in range(len(profile6)):
            for opponent in range(N):
                if opponent != player:
                    product *= 1.0 - profile6[phase, opponent]
        opponent_products.append(product)
    print(
        "W6 survives to theta=0.11: "
        f"tightest={tight}; opponent max={max(opponent_products):.9f}; "
        f"phase-zero value={tuple(values6[0])}"
    )
    print("W6 profile at theta=0.11:")
    for row in profile6:
        print("  " + repr(tuple(float(value) for value in row)))


def phase_two_substitution_scan() -> None:
    """Try every nonempty support at the W14 phase-2 wall."""

    theta14, active14 = locate_wall(
        BRANCHES["W14"], ("active-zero", 2, 3), 0.102, 0.103
    )
    profile14 = BRANCHES["W14"].profile(active14)
    outcomes: list[tuple[int, str]] = []
    for mask in range(1, 1 << N):
        word = list(NEARBY_SUPPORT_WORD)
        word[2] = mask
        branch = Branch.from_profile(tuple(word), profile14)
        seed = branch.seed.copy()
        for index, slot in enumerate(branch.slots):
            if seed[index] == 0.0:
                seed[index] = 0.005
        try:
            active = branch.solve(0.11, seed)
        except RuntimeError as error:
            outcomes.append((mask, f"no-root ({error})"))
            continue
        tight = min(branch.constraints(active, 0.11), key=lambda item: item.slack)
        outcomes.append((mask, f"tightest={tight}"))
    print("phase-2 substitution scan at theta=0.11:")
    for mask, outcome in outcomes:
        print(f"  mask {mask}: {outcome}")


def active_set_pivot_scan(maximum_nodes: int = 120) -> None:
    """Explore adjacent support words by complementarity pivots at theta=.11."""

    queue: deque[tuple[tuple[int, ...], np.ndarray]] = deque()
    for source in BRANCHES.values():
        try:
            active = source.solve(0.11, source.seed)
        except RuntimeError:
            continue
        queue.append((source.word, source.profile(active)))

    seen: set[tuple[int, ...]] = set()
    best: tuple[float, tuple[int, ...], Constraint] | None = None
    solved = 0
    while queue and len(seen) < maximum_nodes:
        word, seed_profile = queue.popleft()
        if word in seen:
            continue
        seen.add(word)
        branch = Branch.from_profile(word, seed_profile)
        try:
            active = branch.solve(0.11, branch.seed)
        except RuntimeError:
            continue
        solved += 1
        profile = branch.profile(active)
        constraints = sorted(
            branch.constraints(active, 0.11), key=lambda item: item.slack
        )
        tight = constraints[0]
        if best is None or tight.slack > best[0]:
            best = tight.slack, word, tight
        if tight.slack >= -1e-7:
            opponent_products = []
            for player in range(N):
                product = 1.0
                for phase in range(len(profile)):
                    for opponent in range(N):
                        if opponent != player:
                            product *= 1.0 - profile[phase, opponent]
                opponent_products.append(product)
            print(
                "ACTIVE-SET RESCUE: "
                f"word={word}; tightest={tight}; "
                f"opponent max={max(opponent_products):.9f}"
            )
            for row in profile:
                print("  " + repr(tuple(float(value) for value in row)))
            return

        # Pivot the most violated zero-bound or inactive constraints.  An
        # active-one violation belongs to the sure-quitter boundary and needs
        # a different chart, so it is recorded but not toggled here.
        pivoted = 0
        for violation in constraints:
            if violation.slack >= 0 or pivoted >= 4:
                break
            if violation.kind == "active-one":
                continue
            neighbor = list(word)
            neighbor[violation.phase] ^= 1 << violation.player
            if neighbor[violation.phase] == 0:
                continue
            queue.append((tuple(neighbor), profile))
            pivoted += 1

    print(
        f"active-set scan found no rescue: visited={len(seen)}, solved={solved}, "
        f"best={best}"
    )


def length_surgery_scan() -> None:
    """Probe phase insertion/deletion near the dying W14 block."""

    source = BRANCHES["W14"]
    source_active = source.solve(0.11, source.seed)
    source_profile = source.profile(source_active)
    candidates: list[tuple[str, tuple[int, ...], np.ndarray]] = []

    for phase in range(source.period):
        deleted_word = source.word[:phase] + source.word[phase + 1 :]
        deleted_profile = np.delete(source_profile, phase, axis=0)
        candidates.append((f"delete-{phase}", deleted_word, deleted_profile))

    # The wall is at phase 2, inside the run of mask 14.  Probe insertions
    # throughout that run and immediately after it, with every nonempty mask.
    for insertion in (2, 3, 4, 5):
        template = source_profile[min(insertion, source.period - 1)]
        for mask in range(1, 1 << N):
            inserted_word = (
                source.word[:insertion] + (mask,) + source.word[insertion:]
            )
            inserted_profile = np.insert(
                source_profile, insertion, template, axis=0
            )
            candidates.append(
                (f"insert-{insertion}-mask-{mask}", inserted_word, inserted_profile)
            )

    results: list[
        tuple[float, str, tuple[int, ...], Constraint, np.ndarray]
    ] = []
    for label, word, seed_profile in candidates:
        branch = Branch.from_profile(word, seed_profile)
        seed = branch.seed.copy()
        for index, value in enumerate(seed):
            if value == 0.0:
                seed[index] = 0.002
        try:
            active = branch.solve(0.11, seed)
        except RuntimeError:
            continue
        profile = branch.profile(active)
        tight = min(branch.constraints(active, 0.11), key=lambda item: item.slack)
        results.append((tight.slack, label, word, tight, profile))

    results.sort(key=lambda item: item[0], reverse=True)
    print("length-surgery best candidates at theta=0.11:")
    for slack, label, word, tight, _ in results[:12]:
        print(f"  {label}: slack={slack:.9g}; tightest={tight}; word={word}")
    if results and results[0][0] >= -1e-7:
        slack, label, word, tight, profile = results[0]
        print(f"LENGTH-SURGERY RESCUE: {label}; word={word}; tightest={tight}")
        for row in profile:
            print("  " + repr(tuple(float(value) for value in row)))


def singleton_lasso_search(trials: int = 400) -> None:
    """Falsification search for a cap-safe singleton-support lasso."""

    rng = np.random.default_rng(20260803)
    table = payoff_table(0.11)
    solos = np.array([table[1 << player, player] for player in range(N)])
    columns = np.array([table[1 << player] for player in range(N)])

    def values(players: tuple[int, ...], hazards: np.ndarray) -> np.ndarray:
        period = len(players)
        survival = 1.0 - hazards
        cycle_survival = float(np.prod(survival))
        result = np.empty((period, N))
        numerator = np.zeros(N)
        prefix = 1.0
        for phase in range(period):
            numerator += prefix * hazards[phase] * columns[players[phase]]
            prefix *= survival[phase]
        denominator = 1.0 - cycle_survival
        if abs(denominator) < 1e-12 or np.any(np.abs(survival) < 1e-12):
            return np.full((period, N), 1e12)
        result[0] = numerator / denominator
        for phase in range(period - 1):
            result[phase + 1] = (
                result[phase] - hazards[phase] * columns[players[phase]]
            ) / survival[phase]
        return result

    def residual(players: tuple[int, ...], hazards: np.ndarray) -> np.ndarray:
        payoff = values(players, hazards)
        period = len(players)
        return np.array(
            [
                payoff[(phase + 1) % period, player] - solos[player]
                for phase, player in enumerate(players)
            ]
        )

    def minimum_slack(
        players: tuple[int, ...], hazards: np.ndarray
    ) -> tuple[float, str]:
        payoff = values(players, hazards)
        period = len(players)
        slacks: list[tuple[float, str]] = []
        for phase, quitter in enumerate(players):
            h = hazards[phase]
            slacks.append((h, f"hazard-zero phase={phase}"))
            slacks.append((1.0 - h, f"hazard-one phase={phase}"))
            successor = payoff[(phase + 1) % period]
            for player in range(N):
                if player == quitter:
                    continue
                pair = (1 << player) | (1 << quitter)
                difference = (
                    (1.0 - h) * solos[player]
                    + h * table[pair, player]
                    - h * columns[quitter, player]
                    - (1.0 - h) * successor[player]
                )
                slacks.append((-difference, f"inactive phase={phase} player={player}"))
        return min(slacks, key=lambda item: item[0])

    best: tuple[float, tuple[int, ...], str, np.ndarray] | None = None
    for _ in range(trials):
        period = int(rng.integers(2, 25))
        players = tuple(int(value) for value in rng.integers(0, N, period))
        if len(set(players)) < 2:
            continue
        seed = rng.uniform(0.002, 0.55, period)
        solution = root(lambda hazards: residual(players, hazards), seed)
        if not solution.success or np.max(np.abs(solution.fun)) > 1e-7:
            continue
        slack, label = minimum_slack(players, solution.x)
        word = tuple(1 << player for player in players)
        if best is None or slack > best[0]:
            best = slack, word, label, solution.x
        if slack >= -1e-7:
            print(
                f"SINGLETON-LASSO RESCUE: word={word}; "
                f"tightest={slack} ({label}); hazards={tuple(solution.x)}"
            )
            return
    print(f"singleton lasso search found no rescue in {trials} trials; best={best}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode",
        nargs="?",
        choices=("walls", "local", "length", "singleton", "all"),
        default="walls",
        help=(
            "walls follows the three known sheets and their immediate "
            "support exchanges; the other modes are broader numerical "
            "falsification searches"
        ),
    )
    parser.add_argument("--trials", type=int, default=500)
    args = parser.parse_args()

    if args.mode in ("walls", "all"):
        for label in BRANCHES:
            follow(label)
        surgery_probe()
    if args.mode in ("local", "all"):
        phase_two_substitution_scan()
        active_set_pivot_scan()
    if args.mode in ("length", "all"):
        length_surgery_scan()
    if args.mode in ("singleton", "all"):
        singleton_lasso_search(args.trials)


if __name__ == "__main__":
    main()
