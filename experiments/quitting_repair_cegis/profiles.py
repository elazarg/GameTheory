"""Exact evaluators for the repair ladder's stable certificate classes."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Iterable, Sequence

from .model import (
    Payoff,
    RationalQuittingGame,
    Root,
    absorbing_contribution,
    all_continue_mass,
    fixed_opponents_continue_mass,
    fixed_opponents_continue_reward,
    fixed_opponents_quit_value,
    fraction_text,
    fractions_json,
    max_regret,
    root_continue_value,
    root_nash_regrets,
    root_successor_payoff,
)


@dataclass(frozen=True)
class CutoffOneEvaluation:
    root: Root
    value: Payoff
    quit_values: Payoff
    positive_continue_values: Payoff
    root_regrets: Payoff
    behavioral_caps: Payoff
    regrets: Payoff

    @property
    def exact(self) -> bool:
        return max_regret(self.regrets) == 0 and max_regret(self.root_regrets) == 0

    def to_certificate_dict(self) -> dict[str, Any]:
        return {
            "kind": "cutoff_one",
            "hazards": fractions_json(self.root),
            "value": fractions_json(self.value),
            "quit_values": fractions_json(self.quit_values),
            "positive_continue_values": fractions_json(
                self.positive_continue_values
            ),
            "behavioral_caps": fractions_json(self.behavioral_caps),
            "regrets": fractions_json(self.regrets),
            "root_regrets": fractions_json(self.root_regrets),
        }


@dataclass(frozen=True)
class StationaryEvaluation:
    root: Root
    value: Payoff
    behavioral_caps: Payoff
    regrets: Payoff
    continue_mass: Fraction
    opponent_continue_masses: Payoff
    quit_values: Payoff
    never_values: Payoff

    @property
    def exact(self) -> bool:
        return max_regret(self.regrets) == 0

    def to_certificate_dict(self, *, kind: str = "stationary_full_rate") -> dict[str, Any]:
        return {
            "kind": kind,
            "hazards": fractions_json(self.root),
            "value": fractions_json(self.value),
            "behavioral_caps": fractions_json(self.behavioral_caps),
            "regrets": fractions_json(self.regrets),
            "continue_mass": fraction_text(self.continue_mass),
            "opponent_continue_masses": fractions_json(
                self.opponent_continue_masses
            ),
            "quit_values": fractions_json(self.quit_values),
            "never_values": fractions_json(self.never_values),
        }


@dataclass(frozen=True)
class CyclicEvaluation:
    word: tuple[Root, ...]
    values: tuple[Payoff, ...]
    root_regrets: tuple[Payoff, ...]
    behavioral_caps: tuple[Payoff, ...]
    behavioral_regrets: tuple[Payoff, ...]
    player_cycle_continue_products: Payoff
    total_cycle_continue_product: Fraction

    @property
    def period(self) -> int:
        return len(self.word)

    @property
    def contracts(self) -> bool:
        return all(product < 1 for product in self.player_cycle_continue_products)

    @property
    def exact(self) -> bool:
        return (
            self.contracts
            and all(max_regret(regrets) == 0 for regrets in self.root_regrets)
            and all(max_regret(regrets) == 0 for regrets in self.behavioral_regrets)
        )

    def initial_max_regret(self) -> Fraction:
        return max_regret(self.behavioral_regrets[0])

    def all_phase_max_regret(self) -> Fraction:
        return max(
            (max_regret(regrets) for regrets in self.behavioral_regrets),
            default=Fraction(0),
        )

    def to_certificate_dict(self) -> dict[str, Any]:
        return {
            "kind": "accepted_holonomy_word",
            "period": self.period,
            "word": [fractions_json(root) for root in self.word],
            "values": [fractions_json(value) for value in self.values],
            "root_regrets": [
                fractions_json(regrets) for regrets in self.root_regrets
            ],
            "behavioral_caps": [
                fractions_json(caps) for caps in self.behavioral_caps
            ],
            "behavioral_regrets": [
                fractions_json(regrets) for regrets in self.behavioral_regrets
            ],
            "player_cycle_continue_products": fractions_json(
                self.player_cycle_continue_products
            ),
            "total_cycle_continue_product": fraction_text(
                self.total_cycle_continue_product
            ),
        }


def evaluate_cutoff_one(
    game: RationalQuittingGame, root: Sequence[Fraction]
) -> CutoffOneEvaluation:
    checked_root = game.validate_root(root)
    zero = tuple(Fraction(0) for _ in range(game.players))
    value = root_successor_payoff(game, checked_root, zero)
    quit_values = tuple(
        fixed_opponents_quit_value(game, checked_root, who)
        for who in range(game.players)
    )
    root_regrets = root_nash_regrets(game, checked_root, zero)
    positive_continue_values = []
    caps = []
    regrets = []
    for who in range(game.players):
        positive_singleton_cap = max(
            Fraction(0), game.reward(1 << who, who)
        )
        continue_value = fixed_opponents_continue_reward(
            game, checked_root, who
        ) + fixed_opponents_continue_mass(
            checked_root, who
        ) * positive_singleton_cap
        cap = max(quit_values[who], continue_value)
        positive_continue_values.append(continue_value)
        caps.append(cap)
        regrets.append(max(Fraction(0), cap - value[who]))
    return CutoffOneEvaluation(
        root=checked_root,
        value=value,
        quit_values=quit_values,
        positive_continue_values=tuple(positive_continue_values),
        root_regrets=root_regrets,
        behavioral_caps=tuple(caps),
        regrets=tuple(regrets),
    )


def evaluate_stationary(
    game: RationalQuittingGame, root: Sequence[Fraction]
) -> StationaryEvaluation:
    checked_root = game.validate_root(root)
    contribution = absorbing_contribution(game, checked_root)
    continuation_mass = all_continue_mass(checked_root)
    if continuation_mass < 1:
        value = tuple(
            contribution[who] / (1 - continuation_mass)
            for who in range(game.players)
        )
    else:
        # The all-Continue profile never reaches a terminal state.
        value = tuple(Fraction(0) for _ in range(game.players))

    opponent_masses: list[Fraction] = []
    quit_values: list[Fraction] = []
    never_values: list[Fraction] = []
    caps: list[Fraction] = []
    regrets: list[Fraction] = []
    for who in range(game.players):
        opponent_mass = fixed_opponents_continue_mass(checked_root, who)
        quit_value = fixed_opponents_quit_value(game, checked_root, who)
        if opponent_mass < 1:
            never_value = fixed_opponents_continue_reward(
                game, checked_root, who
            ) / (1 - opponent_mass)
            cap = max(quit_value, never_value)
        else:
            never_value = Fraction(0)
            cap = max(Fraction(0), game.reward(1 << who, who))
        opponent_masses.append(opponent_mass)
        quit_values.append(quit_value)
        never_values.append(never_value)
        caps.append(cap)
        regrets.append(max(Fraction(0), cap - value[who]))

    return StationaryEvaluation(
        root=checked_root,
        value=value,
        behavioral_caps=tuple(caps),
        regrets=tuple(regrets),
        continue_mass=continuation_mass,
        opponent_continue_masses=tuple(opponent_masses),
        quit_values=tuple(quit_values),
        never_values=tuple(never_values),
    )


def _cyclic_affine_fixed_points(
    constants: Sequence[Fraction], coefficients: Sequence[Fraction]
) -> tuple[Fraction, ...]:
    """Solve ``x[k] = constants[k] + coefficients[k] * x[k+1]`` exactly."""

    period = len(constants)
    if period == 0 or len(coefficients) != period:
        raise ValueError("a cyclic affine system needs matching nonempty arrays")
    cycle_product = Fraction(1)
    for coefficient in coefficients:
        if coefficient < 0 or coefficient > 1:
            raise ValueError("cyclic continuation coefficients must lie in [0,1]")
        cycle_product *= coefficient
    if cycle_product == 1:
        if any(constant != 0 for constant in constants):
            raise ValueError("nonzero charge on a noncontracting cyclic system")
        return tuple(Fraction(0) for _ in range(period))

    values: list[Fraction] = []
    for start in range(period):
        accumulated = Fraction(0)
        prefix = Fraction(1)
        for offset in range(period):
            phase = (start + offset) % period
            accumulated += prefix * constants[phase]
            prefix *= coefficients[phase]
        values.append(accumulated / (1 - prefix))
    return tuple(values)


def cyclic_policy_values(
    game: RationalQuittingGame, word: Sequence[Sequence[Fraction]]
) -> tuple[Payoff, ...]:
    roots = tuple(game.validate_root(root) for root in word)
    if not roots:
        raise ValueError("cyclic word is empty")
    contributions = tuple(absorbing_contribution(game, root) for root in roots)
    coefficients = tuple(all_continue_mass(root) for root in roots)
    coordinate_values = [
        _cyclic_affine_fixed_points(
            [contribution[who] for contribution in contributions], coefficients
        )
        for who in range(game.players)
    ]
    return tuple(
        tuple(coordinate_values[who][phase] for who in range(game.players))
        for phase in range(len(roots))
    )


def _cyclic_player_cap(
    game: RationalQuittingGame,
    word: tuple[Root, ...],
    who: int,
    start: int,
) -> tuple[Fraction, Fraction]:
    """Return the exact pure-time/Never cap and opponent cycle product."""

    period = len(word)
    continue_rewards = tuple(
        fixed_opponents_continue_reward(game, root, who) for root in word
    )
    opponent_masses = tuple(
        fixed_opponents_continue_mass(root, who) for root in word
    )
    quit_values = tuple(
        fixed_opponents_quit_value(game, root, who) for root in word
    )
    cycle_product = Fraction(1)
    for mass in opponent_masses:
        cycle_product *= mass

    if cycle_product == 1:
        # Every opponent continues surely at every phase.  The deviator can
        # either Never (zero) or quit alone at any time; the singleton row is
        # independent of the calendar phase.
        return max(Fraction(0), game.reward(1 << who, who)), cycle_product

    never_values = _cyclic_affine_fixed_points(
        continue_rewards, opponent_masses
    )
    cap = never_values[start]
    prefix_reward = Fraction(0)
    prefix_mass = Fraction(1)
    for steps in range(period):
        phase = (start + steps) % period
        cap = max(cap, prefix_reward + prefix_mass * quit_values[phase])
        prefix_reward += prefix_mass * continue_rewards[phase]
        prefix_mass *= opponent_masses[phase]
    return cap, cycle_product


def evaluate_cyclic_word(
    game: RationalQuittingGame, word: Sequence[Sequence[Fraction]]
) -> CyclicEvaluation:
    roots = tuple(game.validate_root(root) for root in word)
    if not roots:
        raise ValueError("cyclic word is empty")
    values = cyclic_policy_values(game, roots)
    period = len(roots)
    root_regrets = tuple(
        root_nash_regrets(game, roots[phase], values[(phase + 1) % period])
        for phase in range(period)
    )

    caps_by_phase: list[Payoff] = []
    regrets_by_phase: list[Payoff] = []
    player_products: list[Fraction] = []
    for start in range(period):
        caps: list[Fraction] = []
        regrets: list[Fraction] = []
        products: list[Fraction] = []
        for who in range(game.players):
            cap, cycle_product = _cyclic_player_cap(game, roots, who, start)
            caps.append(cap)
            regrets.append(max(Fraction(0), cap - values[start][who]))
            products.append(cycle_product)
        caps_by_phase.append(tuple(caps))
        regrets_by_phase.append(tuple(regrets))
        if start == 0:
            player_products = products

    total_product = Fraction(1)
    for root in roots:
        total_product *= all_continue_mass(root)

    return CyclicEvaluation(
        word=roots,
        values=values,
        root_regrets=root_regrets,
        behavioral_caps=tuple(caps_by_phase),
        behavioral_regrets=tuple(regrets_by_phase),
        player_cycle_continue_products=tuple(player_products),
        total_cycle_continue_product=total_product,
    )
