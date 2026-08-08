"""Exact rational semantics for finite quitting-game search.

The experimental lane deliberately uses :class:`fractions.Fraction` throughout.
A reported equality or inequality is therefore an exact finite calculation,
not a floating-point tolerance test.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence
import json

Rational = Fraction
Root = tuple[Fraction, ...]
Payoff = tuple[Fraction, ...]


def parse_fraction(value: Any) -> Fraction:
    """Parse a JSON rational without accepting binary floats."""

    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        raise TypeError("booleans are not rationals")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"invalid rational literal {value!r}") from exc
    raise TypeError(
        f"expected an integer or rational string, got {type(value).__name__}"
    )


def fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def fractions_json(values: Iterable[Fraction]) -> list[str]:
    return [fraction_text(value) for value in values]


def coalition_mask(players: int, quitters: Iterable[int]) -> int:
    mask = 0
    for player in quitters:
        if not 0 <= player < players:
            raise ValueError(f"player {player} is outside Fin {players}")
        mask |= 1 << player
    return mask


def coalition_players(players: int, mask: int) -> tuple[int, ...]:
    if mask < 0 or mask >= 1 << players:
        raise ValueError(f"invalid coalition mask {mask} for {players} players")
    return tuple(player for player in range(players) if mask & (1 << player))


@dataclass(frozen=True)
class RationalQuittingGame:
    """A complete rational terminal reward table.

    ``rewards[mask]`` is the payoff vector for the nonempty quitter coalition
    encoded by ``mask``.  Index zero is a synthetic zero row used only to keep
    bit-mask lookup total; the quitting model never treats it as terminal.
    """

    name: str
    players: int
    rewards: tuple[Payoff, ...]
    hints: Mapping[str, Any]
    source: str | None = None

    def __post_init__(self) -> None:
        if self.players <= 0:
            raise ValueError("a quitting table needs at least one player")
        expected = 1 << self.players
        if len(self.rewards) != expected:
            raise ValueError(
                f"expected {expected} reward slots, got {len(self.rewards)}"
            )
        if any(len(row) != self.players for row in self.rewards):
            raise ValueError("every payoff row must have one coordinate per player")
        if any(value != 0 for value in self.rewards[0]):
            raise ValueError("the synthetic empty-coalition row must be zero")

    def reward(self, mask: int, player: int) -> Fraction:
        if mask == 0:
            raise ValueError("the empty coalition is not terminal")
        if not 0 <= player < self.players:
            raise ValueError(f"invalid player {player}")
        return self.rewards[mask][player]

    def payoff(self, mask: int) -> Payoff:
        if mask == 0:
            raise ValueError("the empty coalition is not terminal")
        return self.rewards[mask]

    def validate_root(self, root: Sequence[Fraction]) -> Root:
        if len(root) != self.players:
            raise ValueError(
                f"root has {len(root)} coordinates, expected {self.players}"
            )
        parsed = tuple(parse_fraction(value) for value in root)
        for player, probability in enumerate(parsed):
            if probability < 0 or probability > 1:
                raise ValueError(
                    f"player {player}'s quit probability {probability} is outside [0,1]"
                )
        return parsed

    @classmethod
    def from_dict(
        cls, data: Mapping[str, Any], *, source: str | None = None
    ) -> "RationalQuittingGame":
        schema = data.get("schema")
        if schema != "quitting-rational-table/v1":
            raise ValueError(f"unsupported table schema {schema!r}")
        players = int(data["players"])
        if players <= 0:
            raise ValueError("players must be positive")
        rewards: list[Payoff | None] = [None] * (1 << players)
        rewards[0] = tuple(Fraction(0) for _ in range(players))
        for entry in data["rewards"]:
            mask = coalition_mask(players, entry["quitters"])
            if mask == 0:
                raise ValueError("terminal reward rows must be nonempty")
            if rewards[mask] is not None:
                raise ValueError(f"duplicate reward row for coalition {mask}")
            payoff = tuple(parse_fraction(value) for value in entry["payoff"])
            if len(payoff) != players:
                raise ValueError(
                    f"coalition {entry['quitters']} has {len(payoff)} coordinates; "
                    f"expected {players}"
                )
            rewards[mask] = payoff
        missing = [
            coalition_players(players, mask)
            for mask in range(1, 1 << players)
            if rewards[mask] is None
        ]
        if missing:
            raise ValueError(f"missing terminal reward rows: {missing}")
        return cls(
            name=str(data["name"]),
            players=players,
            rewards=tuple(row for row in rewards if row is not None),
            hints=data.get("hints", {}),
            source=source,
        )

    @classmethod
    def from_path(cls, path: str | Path) -> "RationalQuittingGame":
        resolved = Path(path)
        with resolved.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
        return cls.from_dict(data, source=str(resolved))

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "quitting-rational-table/v1",
            "name": self.name,
            "players": self.players,
            "rewards": [
                {
                    "quitters": list(coalition_players(self.players, mask)),
                    "payoff": fractions_json(self.rewards[mask]),
                }
                for mask in range(1, 1 << self.players)
            ],
            **({"hints": self.hints} if self.hints else {}),
        }


def root_probability(root: Root, mask: int) -> Fraction:
    probability = Fraction(1)
    for player, quit_probability in enumerate(root):
        probability *= (
            quit_probability if mask & (1 << player) else 1 - quit_probability
        )
    return probability


def opponent_probability(root: Root, who: int, mask: int) -> Fraction:
    """Probability that exactly ``mask`` of ``who``'s opponents quit.

    ``mask`` must not contain ``who``.  The returned distribution is over all
    subsets of the opponents, including the empty set.
    """

    if mask & (1 << who):
        raise ValueError("opponent mask contains the selected player")
    probability = Fraction(1)
    for player, quit_probability in enumerate(root):
        if player == who:
            continue
        probability *= (
            quit_probability if mask & (1 << player) else 1 - quit_probability
        )
    return probability


def opponent_masks(players: int, who: int) -> Iterator[int]:
    who_bit = 1 << who
    for mask in range(1 << players):
        if mask & who_bit == 0:
            yield mask


def all_continue_mass(root: Root) -> Fraction:
    mass = Fraction(1)
    for probability in root:
        mass *= 1 - probability
    return mass


def fixed_opponents_continue_mass(root: Root, who: int) -> Fraction:
    mass = Fraction(1)
    for player, probability in enumerate(root):
        if player != who:
            mass *= 1 - probability
    return mass


def absorbing_contribution(game: RationalQuittingGame, root: Root) -> Payoff:
    values = [Fraction(0) for _ in range(game.players)]
    for mask in range(1, 1 << game.players):
        probability = root_probability(root, mask)
        if probability == 0:
            continue
        payoff = game.payoff(mask)
        for player in range(game.players):
            values[player] += probability * payoff[player]
    return tuple(values)


def root_successor_payoff(
    game: RationalQuittingGame, root: Root, continuation: Sequence[Fraction]
) -> Payoff:
    if len(continuation) != game.players:
        raise ValueError("continuation vector has the wrong dimension")
    contribution = absorbing_contribution(game, root)
    survival = all_continue_mass(root)
    return tuple(
        contribution[player] + survival * parse_fraction(continuation[player])
        for player in range(game.players)
    )


def fixed_opponents_quit_value(
    game: RationalQuittingGame, root: Root, who: int
) -> Fraction:
    total = Fraction(0)
    who_bit = 1 << who
    for mask in opponent_masks(game.players, who):
        total += opponent_probability(root, who, mask) * game.reward(
            mask | who_bit, who
        )
    return total


def fixed_opponents_continue_reward(
    game: RationalQuittingGame, root: Root, who: int
) -> Fraction:
    total = Fraction(0)
    for mask in opponent_masks(game.players, who):
        if mask == 0:
            continue
        total += opponent_probability(root, who, mask) * game.reward(mask, who)
    return total


def root_continue_value(
    game: RationalQuittingGame,
    root: Root,
    continuation: Sequence[Fraction],
    who: int,
) -> Fraction:
    return fixed_opponents_continue_reward(game, root, who) + (
        fixed_opponents_continue_mass(root, who)
        * parse_fraction(continuation[who])
    )


def root_nash_regrets(
    game: RationalQuittingGame,
    root: Root,
    continuation: Sequence[Fraction],
) -> Payoff:
    prescribed = root_successor_payoff(game, root, continuation)
    return tuple(
        max(
            Fraction(0),
            fixed_opponents_quit_value(game, root, who) - prescribed[who],
            root_continue_value(game, root, continuation, who) - prescribed[who],
        )
        for who in range(game.players)
    )


def max_regret(regrets: Sequence[Fraction]) -> Fraction:
    return max(regrets, default=Fraction(0))


def probability_grid(values: Sequence[Any]) -> tuple[Fraction, ...]:
    parsed = tuple(sorted({parse_fraction(value) for value in values}))
    if not parsed:
        raise ValueError("probability grid is empty")
    if parsed[0] < 0 or parsed[-1] > 1:
        raise ValueError("probability grid must lie in [0,1]")
    return parsed


def enumerate_roots(players: int, grid: Sequence[Fraction]) -> Iterator[Root]:
    yield from product(grid, repeat=players)
