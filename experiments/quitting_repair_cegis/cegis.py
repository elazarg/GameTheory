"""Finite rational-table CEGIS with explicit semantic claim boundaries.

The loop searches a finite family of rational reward tables for a fixed
positive terminal exploitability gap.  A root or cyclic word with exact regret
below the proposed gap is a counterexample profile and is reused against later
tables.  A surviving table is reported only as a finite-grammar filter.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence
import copy
import json

from .model import (
    RationalQuittingGame,
    Root,
    coalition_mask,
    enumerate_roots,
    max_regret,
    parse_fraction,
)
from .profiles import (
    CutoffOneEvaluation,
    CyclicEvaluation,
    StationaryEvaluation,
    evaluate_cutoff_one,
    evaluate_cyclic_word,
    evaluate_stationary,
)
from .report import (
    make_filter_report,
    make_gap_counterexample_report,
    make_repair_report,
)
from .search import (
    LadderResult,
    RepairFinding,
    RungTrace,
    SearchConfig,
    canonical_rotation,
    run_repair_ladder,
    subset_roots,
)


@dataclass(frozen=True)
class ProfileWitness:
    kind: str
    data: tuple[Root, ...]
    source: str

    def key(self) -> tuple[str, tuple[Root, ...]]:
        return self.kind, self.data

    def evaluate(
        self, game: RationalQuittingGame
    ) -> tuple[
        Fraction,
        CutoffOneEvaluation | StationaryEvaluation | CyclicEvaluation,
        dict[str, Any],
    ]:
        if self.kind == "cutoff_one":
            evaluation = evaluate_cutoff_one(game, self.data[0])
            return (
                max_regret(evaluation.regrets),
                evaluation,
                evaluation.to_certificate_dict(),
            )
        if self.kind == "stationary_full_rate":
            evaluation = evaluate_stationary(game, self.data[0])
            return (
                max_regret(evaluation.regrets),
                evaluation,
                evaluation.to_certificate_dict(),
            )
        if self.kind == "accepted_holonomy_word":
            evaluation = evaluate_cyclic_word(game, self.data)
            return (
                evaluation.initial_max_regret(),
                evaluation,
                evaluation.to_certificate_dict(),
            )
        raise ValueError(f"unknown witness kind {self.kind!r}")


@dataclass(frozen=True)
class CegisConfig:
    gap: Fraction
    search: SearchConfig
    max_candidates: int = 10_000

    @classmethod
    def from_dict(cls, data: Mapping[str, Any]) -> "CegisConfig":
        gap = parse_fraction(data["gap"])
        if gap <= 0:
            raise ValueError("CEGIS gap must be positive")
        return cls(
            gap=gap,
            search=SearchConfig.from_dict(data.get("search")),
            max_candidates=int(data.get("max_candidates", 10_000)),
        )


@dataclass(frozen=True)
class CegisRun:
    reports: tuple[dict[str, Any], ...]
    witnesses: tuple[ProfileWitness, ...]
    candidates: int


def _template_games(
    manifest: Mapping[str, Any], manifest_path: Path
) -> Iterator[RationalQuittingGame]:
    if "tables" in manifest:
        for raw_path in manifest["tables"]:
            path = (manifest_path.parent / raw_path).resolve()
            yield RationalQuittingGame.from_path(path)
        return

    if "base_table" not in manifest:
        raise ValueError("CEGIS manifest needs either tables or base_table")
    raw_base = manifest["base_table"]
    if isinstance(raw_base, str):
        path = (manifest_path.parent / raw_base).resolve()
        with path.open("r", encoding="utf-8") as handle:
            base = json.load(handle)
    elif isinstance(raw_base, dict):
        base = copy.deepcopy(raw_base)
    else:
        raise TypeError("base_table must be a path or an inline table")

    variables = manifest.get("variables", [])
    choices: list[tuple[Fraction, ...]] = []
    locations: list[tuple[int, int]] = []
    players = int(base["players"])
    row_by_mask = {
        coalition_mask(players, row["quitters"]): row for row in base["rewards"]
    }
    for variable in variables:
        mask = coalition_mask(players, variable["quitters"])
        player = int(variable["player"])
        if mask == 0 or mask not in row_by_mask:
            raise ValueError(f"unknown variable coalition {variable['quitters']}")
        if not 0 <= player < players:
            raise ValueError(f"invalid variable player {player}")
        values = tuple(parse_fraction(value) for value in variable["values"])
        if not values:
            raise ValueError("template variables need a nonempty finite domain")
        locations.append((mask, player))
        choices.append(values)

    for candidate_index, assignment in enumerate(product(*choices) if choices else [()]):
        candidate = copy.deepcopy(base)
        suffix: list[str] = []
        candidate_rows = {
            coalition_mask(players, row["quitters"]): row
            for row in candidate["rewards"]
        }
        for (mask, player), value in zip(locations, assignment, strict=True):
            candidate_rows[mask]["payoff"][player] = str(value)
            suffix.append(f"m{mask}p{player}={value}")
        if suffix:
            candidate["name"] = f"{base['name']}[{','.join(suffix)}]"
        else:
            candidate["name"] = f"{base['name']}[{candidate_index}]"
        yield RationalQuittingGame.from_dict(
            candidate, source=f"{manifest_path}#candidate-{candidate_index}"
        )


def _witness_from_finding(finding: RepairFinding) -> ProfileWitness:
    if finding.rung == "cutoff_one":
        assert isinstance(finding.certificate, CutoffOneEvaluation)
        return ProfileWitness("cutoff_one", (finding.certificate.root,), finding.source)
    if finding.rung in {"stationary", "quitter_subset", "quitter_pair"}:
        assert isinstance(finding.certificate, StationaryEvaluation)
        return ProfileWitness(
            "stationary_full_rate", (finding.certificate.root,), finding.source
        )
    if finding.rung == "holonomy_word":
        assert isinstance(finding.certificate, CyclicEvaluation)
        return ProfileWitness(
            "accepted_holonomy_word", finding.certificate.word, finding.source
        )
    raise ValueError(f"unknown repair rung {finding.rung!r}")


def _direct_repair_result(
    evaluation: CutoffOneEvaluation | StationaryEvaluation | CyclicEvaluation,
    source: str,
) -> LadderResult:
    if isinstance(evaluation, CutoffOneEvaluation):
        rung = "cutoff_one"
        regret = max_regret(evaluation.regrets)
    elif isinstance(evaluation, StationaryEvaluation):
        rung = "stationary"
        regret = max_regret(evaluation.regrets)
    else:
        rung = "holonomy_word"
        regret = evaluation.all_phase_max_regret()
    finding = RepairFinding(rung, evaluation, 1, source)
    trace = RungTrace(
        rung=rung,
        tested=1,
        exhausted=False,
        best_regret=regret,
        note="reused exact CEGIS witness",
    )
    return LadderResult(finding=finding, trace=(trace,))


def _hint_witnesses(game: RationalQuittingGame) -> Iterator[ProfileWitness]:
    for raw in game.hints.get("cutoff_one_roots", []):
        yield ProfileWitness(
            "cutoff_one", (game.validate_root(raw),), "table cutoff-one hint"
        )
    for key in ("stationary_roots", "pair_roots"):
        for raw in game.hints.get(key, []):
            yield ProfileWitness(
                "stationary_full_rate",
                (game.validate_root(raw),),
                f"table {key} hint",
            )
    for raw_word in game.hints.get("holonomy_words", []):
        word = tuple(game.validate_root(root) for root in raw_word)
        yield ProfileWitness(
            "accepted_holonomy_word",
            canonical_rotation(word),
            "table cyclic-word hint",
        )


def _bounded_profile_witnesses(
    game: RationalQuittingGame, config: SearchConfig
) -> Iterator[ProfileWitness]:
    seen: set[tuple[str, tuple[Root, ...]]] = set()

    def emit(witness: ProfileWitness) -> Iterator[ProfileWitness]:
        key = witness.key()
        if key not in seen:
            seen.add(key)
            yield witness

    if config.include_hints:
        for witness in _hint_witnesses(game):
            yield from emit(witness)

    for index, root in enumerate(enumerate_roots(game.players, config.probabilities)):
        if index >= config.max_cutoff_roots:
            break
        yield from emit(ProfileWitness("cutoff_one", (root,), "bounded cutoff grid"))

    for index, root in enumerate(enumerate_roots(game.players, config.probabilities)):
        if index >= config.max_stationary_roots:
            break
        yield from emit(
            ProfileWitness("stationary_full_rate", (root,), "bounded stationary grid")
        )

    alphabet = tuple(subset_roots(game.players))[: config.max_word_roots]
    tested_words = 0
    for period in range(2, config.max_period + 1):
        for raw_word in product(alphabet, repeat=period):
            if tested_words >= config.max_words:
                return
            if len(set(raw_word)) == 1:
                continue
            canonical = canonical_rotation(raw_word)
            if tuple(raw_word) != canonical:
                continue
            tested_words += 1
            yield from emit(
                ProfileWitness(
                    "accepted_holonomy_word",
                    canonical,
                    "bounded pure-root cyclic grammar",
                )
            )


def _find_gap_counterexample(
    game: RationalQuittingGame,
    gap: Fraction,
    config: SearchConfig,
) -> tuple[ProfileWitness | None, Fraction | None, Any | None, dict[str, Any] | None, int]:
    best_regret: Fraction | None = None
    tested = 0
    for witness in _bounded_profile_witnesses(game, config):
        tested += 1
        regret, evaluation, certificate = witness.evaluate(game)
        if best_regret is None or regret < best_regret:
            best_regret = regret
        if regret < gap:
            return witness, regret, evaluation, certificate, tested
    return None, best_regret, None, None, tested


def run_cegis_manifest(path: str | Path) -> CegisRun:
    manifest_path = Path(path).resolve()
    with manifest_path.open("r", encoding="utf-8") as handle:
        manifest = json.load(handle)
    if manifest.get("schema") != "quitting-table-cegis/v1":
        raise ValueError(f"unsupported CEGIS schema {manifest.get('schema')!r}")
    config = CegisConfig.from_dict(manifest)

    reports: list[dict[str, Any]] = []
    witness_pool: list[ProfileWitness] = []
    witness_keys: set[tuple[str, tuple[Root, ...]]] = set()
    candidate_count = 0

    for game in _template_games(manifest, manifest_path):
        if candidate_count >= config.max_candidates:
            break
        candidate_count += 1

        reused = False
        for witness in witness_pool:
            if len(witness.data[0]) != game.players:
                continue
            regret, evaluation, certificate = witness.evaluate(game)
            if regret < config.gap:
                if regret == 0 and evaluation.exact:
                    reports.append(
                        make_repair_report(
                            game,
                            _direct_repair_result(
                                evaluation, "reused exact CEGIS profile witness"
                            ),
                            config.search,
                        )
                    )
                else:
                    reports.append(
                        make_gap_counterexample_report(
                            game,
                            fixed_gap=config.gap,
                            certificate=certificate,
                            regret=regret,
                            source="reused CEGIS profile witness",
                        )
                    )
                reused = True
                break
        if reused:
            continue

        ladder = run_repair_ladder(game, config.search)
        if ladder.finding is not None:
            reports.append(make_repair_report(game, ladder, config.search))
            witness = _witness_from_finding(ladder.finding)
            if witness.key() not in witness_keys:
                witness_keys.add(witness.key())
                witness_pool.append(witness)
            continue

        witness, regret, evaluation, certificate, tested = _find_gap_counterexample(
            game, config.gap, config.search
        )
        if witness is not None:
            assert regret is not None and evaluation is not None and certificate is not None
            if regret == 0 and evaluation.exact:
                reports.append(
                    make_repair_report(
                        game,
                        _direct_repair_result(
                            evaluation, "exact profile found by fixed-gap CEGIS"
                        ),
                        config.search,
                    )
                )
            else:
                reports.append(
                    make_gap_counterexample_report(
                        game,
                        fixed_gap=config.gap,
                        certificate=certificate,
                        regret=regret,
                        source=witness.source,
                    )
                )
            if witness.key() not in witness_keys:
                witness_keys.add(witness.key())
                witness_pool.append(witness)
            continue

        reports.append(
            make_filter_report(
                game,
                fixed_gap=config.gap,
                scope={
                    "repair_ladder": config.search.to_dict(),
                    "approximate_profile_grammar": {
                        "cutoff_one_grid": config.search.max_cutoff_roots,
                        "stationary_grid": config.search.max_stationary_roots,
                        "pure_root_cyclic_period": config.search.max_period,
                        "cyclic_word_budget": config.search.max_words,
                    },
                },
                tested=tested,
                minimum_regret=regret,
                reason=(
                    "No tested profile refuted the fixed gap.  This does not "
                    "quantify over arbitrary behavioral profiles and therefore "
                    "is not a HasTerminalExploitabilityGap certificate."
                ),
            )
        )

    return CegisRun(
        reports=tuple(reports),
        witnesses=tuple(witness_pool),
        candidates=candidate_count,
    )
