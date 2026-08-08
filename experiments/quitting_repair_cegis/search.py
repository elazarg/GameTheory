"""Deterministic finite repair ladder.

Every accepted rung is checked by an exact evaluator whose hypotheses mirror a
Lean theorem.  Exhausting a rung has no semantic consequence beyond the finite
candidate grammar recorded in the trace.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from itertools import chain, islice, product
from typing import Any, Iterable, Iterator, Sequence

from .model import (
    RationalQuittingGame,
    Root,
    enumerate_roots,
    max_regret,
    parse_fraction,
    probability_grid,
)
from .profiles import (
    CutoffOneEvaluation,
    CyclicEvaluation,
    StationaryEvaluation,
    evaluate_cutoff_one,
    evaluate_cyclic_word,
    evaluate_stationary,
)


DEFAULT_GRID = ("0", "1/4", "1/3", "1/2", "2/3", "3/4", "1")


@dataclass(frozen=True)
class SearchConfig:
    probabilities: tuple[Fraction, ...] = field(
        default_factory=lambda: probability_grid(DEFAULT_GRID)
    )
    max_cutoff_roots: int = 50_000
    max_stationary_roots: int = 50_000
    max_pair_roots: int = 50_000
    max_period: int = 3
    max_word_roots: int = 12
    max_words: int = 50_000
    include_hints: bool = True

    @classmethod
    def from_dict(cls, data: dict[str, Any] | None) -> "SearchConfig":
        data = data or {}
        return cls(
            probabilities=probability_grid(data.get("probabilities", DEFAULT_GRID)),
            max_cutoff_roots=int(data.get("max_cutoff_roots", 50_000)),
            max_stationary_roots=int(data.get("max_stationary_roots", 50_000)),
            max_pair_roots=int(data.get("max_pair_roots", 50_000)),
            max_period=int(data.get("max_period", 3)),
            max_word_roots=int(data.get("max_word_roots", 12)),
            max_words=int(data.get("max_words", 50_000)),
            include_hints=bool(data.get("include_hints", True)),
        )

    def to_dict(self) -> dict[str, Any]:
        from .model import fractions_json

        return {
            "probabilities": fractions_json(self.probabilities),
            "max_cutoff_roots": self.max_cutoff_roots,
            "max_stationary_roots": self.max_stationary_roots,
            "max_pair_roots": self.max_pair_roots,
            "max_period": self.max_period,
            "max_word_roots": self.max_word_roots,
            "max_words": self.max_words,
            "include_hints": self.include_hints,
        }


@dataclass(frozen=True)
class RepairFinding:
    rung: str
    certificate: CutoffOneEvaluation | StationaryEvaluation | CyclicEvaluation
    tested: int
    source: str

    @property
    def exact(self) -> bool:
        return self.certificate.exact


@dataclass(frozen=True)
class RungTrace:
    rung: str
    tested: int
    exhausted: bool
    best_regret: Fraction | None
    note: str


@dataclass(frozen=True)
class LadderResult:
    finding: RepairFinding | None
    trace: tuple[RungTrace, ...]


def _parse_root(game: RationalQuittingGame, raw: Sequence[Any]) -> Root:
    return game.validate_root(tuple(parse_fraction(value) for value in raw))


def _hint_roots(game: RationalQuittingGame, key: str) -> Iterator[Root]:
    for raw in game.hints.get(key, []):
        yield _parse_root(game, raw)


def _dedupe(items: Iterable[Root]) -> Iterator[Root]:
    seen: set[Root] = set()
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        yield item


def _bounded(items: Iterable[Root], limit: int) -> Iterator[Root]:
    if limit < 0:
        raise ValueError("search limits must be nonnegative")
    for index, item in enumerate(items):
        if index >= limit:
            return
        yield item


def _best_update(current: Fraction | None, value: Fraction) -> Fraction:
    return value if current is None or value < current else current


def search_cutoff_one(
    game: RationalQuittingGame, config: SearchConfig
) -> tuple[RepairFinding | None, RungTrace]:
    candidates: Iterable[Root] = enumerate_roots(game.players, config.probabilities)
    if config.include_hints:
        candidates = chain(_hint_roots(game, "cutoff_one_roots"), candidates)
    tested = 0
    best: Fraction | None = None
    for root in _bounded(_dedupe(candidates), config.max_cutoff_roots):
        tested += 1
        evaluation = evaluate_cutoff_one(game, root)
        regret = max_regret(evaluation.regrets)
        best = _best_update(best, regret)
        if evaluation.exact:
            return (
                RepairFinding("cutoff_one", evaluation, tested, "exact grid/hint root"),
                RungTrace(
                    "cutoff_one",
                    tested,
                    False,
                    best,
                    "accepted by zero-tail root Nash plus cutoff-one safety",
                ),
            )
    return None, RungTrace(
        "cutoff_one",
        tested,
        True,
        best,
        "finite zero-tail root grid exhausted; this is only a filter",
    )


def _general_stationary_roots(
    players: int, grid: Sequence[Fraction]
) -> Iterator[Root]:
    """Grid roots outside the pure and one/two-mixer boundary rungs."""

    threshold = min(3, players)
    for root in enumerate_roots(players, grid):
        mixed = sum(1 for probability in root if 0 < probability < 1)
        if mixed >= threshold:
            yield root


def search_stationary(
    game: RationalQuittingGame, config: SearchConfig
) -> tuple[RepairFinding | None, RungTrace]:
    candidates: Iterable[Root] = _general_stationary_roots(
        game.players, config.probabilities
    )
    if config.include_hints:
        candidates = chain(_hint_roots(game, "stationary_roots"), candidates)
    tested = 0
    best: Fraction | None = None
    for root in _bounded(_dedupe(candidates), config.max_stationary_roots):
        tested += 1
        evaluation = evaluate_stationary(game, root)
        regret = max_regret(evaluation.regrets)
        best = _best_update(best, regret)
        if evaluation.exact:
            return (
                RepairFinding(
                    "stationary",
                    evaluation,
                    tested,
                    "exact full-rate stationary cap",
                ),
                RungTrace(
                    "stationary",
                    tested,
                    False,
                    best,
                    "accepted against arbitrary behavioral unilateral deviations",
                ),
            )
    return None, RungTrace(
        "stationary",
        tested,
        True,
        best,
        "general stationary grid stratum exhausted; this is only a filter",
    )


def subset_roots(players: int) -> Iterator[Root]:
    for mask in range(1 << players):
        yield tuple(
            Fraction(1) if mask & (1 << player) else Fraction(0)
            for player in range(players)
        )


def search_quitter_subsets(
    game: RationalQuittingGame, config: SearchConfig
) -> tuple[RepairFinding | None, RungTrace]:
    del config
    tested = 0
    best: Fraction | None = None
    for root in subset_roots(game.players):
        tested += 1
        evaluation = evaluate_stationary(game, root)
        regret = max_regret(evaluation.regrets)
        best = _best_update(best, regret)
        if evaluation.exact:
            return (
                RepairFinding(
                    "quitter_subset",
                    evaluation,
                    tested,
                    "exact pure quitter subset (including Never)",
                ),
                RungTrace(
                    "quitter_subset",
                    tested,
                    False,
                    best,
                    "accepted by the full-rate stationary verifier",
                ),
            )
    return None, RungTrace(
        "quitter_subset",
        tested,
        True,
        best,
        "all pure quitter subsets exhausted; this is only a filter",
    )


def pair_chart_roots(players: int, grid: Sequence[Fraction]) -> Iterator[Root]:
    """Boundary charts with one or two genuinely mixed coordinates.

    Every remaining coordinate is an endpoint.  This covers pure/mixed pairs,
    sure-quitter collision charts, and one-mixer subset repairs without
    pretending that the charts exhaust arbitrary stationary roots.
    """

    interior = tuple(value for value in grid if 0 < value < 1)
    if not interior:
        return
    endpoint = (Fraction(0), Fraction(1))
    for mixed_count in (1, 2):
        if mixed_count > players:
            continue
        # Small player sets make a direct bit-mask selection clearer and
        # deterministic than depending on itertools.combinations ordering.
        for mixed_mask in range(1 << players):
            if mixed_mask.bit_count() != mixed_count:
                continue
            mixed_players = [
                player for player in range(players) if mixed_mask & (1 << player)
            ]
            endpoint_players = [
                player for player in range(players) if not mixed_mask & (1 << player)
            ]
            for mixed_values in product(interior, repeat=mixed_count):
                for endpoint_values in product(endpoint, repeat=len(endpoint_players)):
                    root = [Fraction(0) for _ in range(players)]
                    for player, value in zip(mixed_players, mixed_values, strict=True):
                        root[player] = value
                    for player, value in zip(
                        endpoint_players, endpoint_values, strict=True
                    ):
                        root[player] = value
                    yield tuple(root)


def search_quitter_pairs(
    game: RationalQuittingGame, config: SearchConfig
) -> tuple[RepairFinding | None, RungTrace]:
    candidates: Iterable[Root] = pair_chart_roots(
        game.players, config.probabilities
    )
    if config.include_hints:
        candidates = chain(_hint_roots(game, "pair_roots"), candidates)
    tested = 0
    best: Fraction | None = None
    for root in _bounded(_dedupe(candidates), config.max_pair_roots):
        tested += 1
        evaluation = evaluate_stationary(game, root)
        regret = max_regret(evaluation.regrets)
        best = _best_update(best, regret)
        if evaluation.exact:
            return (
                RepairFinding(
                    "quitter_pair",
                    evaluation,
                    tested,
                    "exact one/two-mixer boundary chart",
                ),
                RungTrace(
                    "quitter_pair",
                    tested,
                    False,
                    best,
                    "accepted by the full-rate stationary verifier",
                ),
            )
    return None, RungTrace(
        "quitter_pair",
        tested,
        True,
        best,
        "finite one/two-mixer boundary charts exhausted; this is only a filter",
    )


def _word_key(word: Sequence[Root]) -> tuple[Root, ...]:
    return tuple(word)


def canonical_rotation(word: Sequence[Root]) -> tuple[Root, ...]:
    checked = tuple(word)
    if not checked:
        raise ValueError("empty cyclic word")
    rotations = tuple(
        checked[offset:] + checked[:offset] for offset in range(len(checked))
    )
    return min(rotations)


def _hint_words(game: RationalQuittingGame) -> Iterator[tuple[Root, ...]]:
    for raw_word in game.hints.get("holonomy_words", []):
        word = tuple(_parse_root(game, root) for root in raw_word)
        if not word:
            raise ValueError("hinted holonomy word is empty")
        yield word


def _word_alphabet(game: RationalQuittingGame, config: SearchConfig) -> tuple[Root, ...]:
    candidates: Iterable[Root] = chain(
        subset_roots(game.players),
        pair_chart_roots(game.players, config.probabilities),
    )
    if config.include_hints:
        candidates = chain(_hint_roots(game, "word_roots"), candidates)
    return tuple(islice(_dedupe(candidates), config.max_word_roots))


def search_holonomy_words(
    game: RationalQuittingGame, config: SearchConfig
) -> tuple[RepairFinding | None, RungTrace]:
    tested = 0
    best: Fraction | None = None
    seen: set[tuple[Root, ...]] = set()

    def inspect(word: tuple[Root, ...], source: str) -> RepairFinding | None:
        nonlocal tested, best
        canonical = canonical_rotation(word)
        if canonical in seen:
            return None
        seen.add(canonical)
        if tested >= config.max_words:
            return None
        tested += 1
        evaluation = evaluate_cyclic_word(game, canonical)
        regret = evaluation.all_phase_max_regret()
        best = _best_update(best, regret)
        if evaluation.exact:
            return RepairFinding("holonomy_word", evaluation, tested, source)
        return None

    if config.include_hints:
        for word in _hint_words(game):
            finding = inspect(word, "exact hinted cyclic word")
            if finding is not None:
                return finding, RungTrace(
                    "holonomy_word",
                    tested,
                    False,
                    best,
                    "accepted by policy recursion, phasewise root Nash, and "
                    "playerwise cycle contraction",
                )

    alphabet = _word_alphabet(game, config)
    for period in range(2, config.max_period + 1):
        for raw_word in product(alphabet, repeat=period):
            if tested >= config.max_words:
                return None, RungTrace(
                    "holonomy_word",
                    tested,
                    False,
                    best,
                    "word budget reached; failure is only a bounded filter",
                )
            if len(set(raw_word)) == 1:
                continue
            if tuple(raw_word) != canonical_rotation(raw_word):
                continue
            finding = inspect(tuple(raw_word), "exhaustive bounded cyclic word")
            if finding is not None:
                return finding, RungTrace(
                    "holonomy_word",
                    tested,
                    False,
                    best,
                    "accepted by policy recursion, phasewise root Nash, and "
                    "playerwise cycle contraction",
                )

    return None, RungTrace(
        "holonomy_word",
        tested,
        True,
        best,
        "bounded cyclic words exhausted; no nonexistence inference is licensed",
    )


RUNG_SEARCHERS = (
    search_cutoff_one,
    search_stationary,
    search_quitter_subsets,
    search_quitter_pairs,
    search_holonomy_words,
)


def run_repair_ladder(
    game: RationalQuittingGame, config: SearchConfig | None = None
) -> LadderResult:
    selected = config or SearchConfig()
    trace: list[RungTrace] = []
    for searcher in RUNG_SEARCHERS:
        finding, rung_trace = searcher(game, selected)
        trace.append(rung_trace)
        if finding is not None:
            if not finding.exact:
                raise AssertionError("a repair rung returned an unchecked certificate")
            return LadderResult(finding=finding, trace=tuple(trace))
    return LadderResult(finding=None, trace=tuple(trace))
