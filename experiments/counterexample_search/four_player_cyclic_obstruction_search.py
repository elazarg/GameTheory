"""Deterministic finite search for four-player cyclic obstruction packages.

This is a bounded candidate screen, not a counterexample verifier.  A table is
``C4``-equivariant: ``r_i(S)`` is determined by one integer row ``f`` after
rotating player ``i`` to slot zero.  The screen asks for:

* positive debt at every pure stationary root, including Never;
* a constant-total-debt unilateral better-response cycle;
* an off-mover debt after every step of that cycle;
* a pure semantic cap for which all-Continue is the only exact Nash root on
  the declared rational root grid; and
* positive total debt on the declared stationary-root grid.

The last two assertions are grid assertions only.  In particular, a positive
reported grid minimum is not a proof that the full terminal-semantic debt
minimum is positive, and grid uniqueness is not uniqueness in the continuous
root simplex.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
import random
from typing import Iterable, Optional


N = 4
NONEMPTY = tuple(range(1, 1 << N))
ROOT_GRID = tuple(F(k, 4) for k in range(5))
SEED = 0x4C59434C
TRIAL_LIMIT = 200_000


def rotate_to_player_zero(mask: int, player: int) -> int:
    answer = 0
    for who in range(N):
        if mask & (1 << who):
            answer |= 1 << ((who - player) % N)
    return answer


def table_from_row(row: tuple[int, ...]) -> tuple[tuple[F, ...], ...]:
    """Expand a 15-entry cyclic row to rewards indexed by coalition mask."""

    return tuple(
        tuple(F(row[rotate_to_player_zero(mask, who) - 1]) for who in range(N))
        if mask else tuple(F(0) for _ in range(N))
        for mask in range(1 << N)
    )


def pure_debt(table: tuple[tuple[F, ...], ...], mask: int) -> tuple[F, ...]:
    value = table[mask]
    return tuple(
        max(table[mask ^ (1 << who)][who] - value[who], F(0))
        for who in range(N)
    )


def find_constant_debt_cycle(
    table: tuple[tuple[F, ...], ...], debts: tuple[tuple[F, ...], ...]
) -> Optional[tuple[tuple[int, ...], tuple[int, ...]]]:
    totals = tuple(sum(debt, F(0)) for debt in debts)
    successors: dict[int, list[tuple[int, int]]] = {}
    for mask in range(1 << N):
        successors[mask] = []
        for who in range(N):
            target = mask ^ (1 << who)
            gain = table[target][who] - table[mask][who]
            off_mover = any(debts[target][other] > 0 for other in range(N) if other != who)
            if gain > 0 and debts[target][who] == 0 and off_mover and totals[target] == totals[mask]:
                successors[mask].append((target, who))

    def visit(start: int, current: int, path: list[int], movers: list[int]) -> Optional[tuple[tuple[int, ...], tuple[int, ...]]]:
        if len(path) > 12:
            return None
        for target, who in successors[current]:
            if target == start and len(path) >= 3:
                return tuple(path), tuple(movers + [who])
            if target in path:
                continue
            found = visit(start, target, path + [target], movers + [who])
            if found is not None:
                return found
        return None

    for start in range(1 << N):
        found = visit(start, start, [start], [])
        if found is not None:
            return found
    return None


def pure_cap(table: tuple[tuple[F, ...], ...], mask: int) -> tuple[F, ...]:
    return tuple(max(table[mask][who], table[mask ^ (1 << who)][who]) for who in range(N))


def action_probability(mask: int, root: tuple[F, ...]) -> F:
    probability = F(1)
    for who, quit_probability in enumerate(root):
        probability *= quit_probability if mask & (1 << who) else 1 - quit_probability
    return probability


def root_endpoint_difference(
    table: tuple[tuple[F, ...], ...], continuation: tuple[F, ...],
    root: tuple[F, ...], who: int,
) -> F:
    quit_value = F(0)
    continue_value = F(0)
    opponents = [other for other in range(N) if other != who]
    for bits in range(1 << (N - 1)):
        mask = 0
        probability = F(1)
        for index, other in enumerate(opponents):
            q = root[other]
            if bits & (1 << index):
                mask |= 1 << other
                probability *= q
            else:
                probability *= 1 - q
        quit_value += probability * table[mask | (1 << who)][who]
        continue_value += probability * (table[mask][who] if mask else continuation[who])
    return quit_value - continue_value


def is_exact_root_nash(
    table: tuple[tuple[F, ...], ...], continuation: tuple[F, ...], root: tuple[F, ...]
) -> bool:
    for who, q in enumerate(root):
        difference = root_endpoint_difference(table, continuation, root, who)
        if q == 0 and difference > 0:
            return False
        if q == 1 and difference < 0:
            return False
        if 0 < q < 1 and difference != 0:
            return False
    return True


def stationary_pair(
    table: tuple[tuple[F, ...], ...], root: tuple[F, ...]
) -> tuple[tuple[F, ...], tuple[F, ...]]:
    all_continue = action_probability(0, root)
    if all_continue == 1:
        prescribed = tuple(F(0) for _ in range(N))
    else:
        prescribed = tuple(
            sum((action_probability(mask, root) * table[mask][who] for mask in NONEMPTY), F(0))
            / (1 - all_continue)
            for who in range(N)
        )

    cap = []
    for who in range(N):
        opponents = [other for other in range(N) if other != who]
        quit_value = F(0)
        continue_reward = F(0)
        continue_mass = F(1)
        for other in opponents:
            continue_mass *= 1 - root[other]
        for bits in range(1 << (N - 1)):
            mask = 0
            probability = F(1)
            for index, other in enumerate(opponents):
                q = root[other]
                if bits & (1 << index):
                    mask |= 1 << other
                    probability *= q
                else:
                    probability *= 1 - q
            quit_value += probability * table[mask | (1 << who)][who]
            if mask:
                continue_reward += probability * table[mask][who]
        never_value = continue_reward / (1 - continue_mass) if continue_mass != 1 else F(0)
        cap.append(max(quit_value, never_value))
    return prescribed, tuple(cap)


@dataclass(frozen=True)
class Candidate:
    row: tuple[int, ...]
    cycle: tuple[int, ...]
    movers: tuple[int, ...]
    cap_source: int
    found_at_trial: int


def structural_search() -> Optional[Candidate]:
    rng = random.Random(SEED)
    for trial in range(1, TRIAL_LIMIT + 1):
        # A positive singleton self-payoff forces positive Never debt.
        row = [rng.choice((-2, -1, 0, 1, 2)) for _ in NONEMPTY]
        row[0] = rng.choice((1, 2))
        table = table_from_row(tuple(row))
        debts = tuple(pure_debt(table, mask) for mask in range(1 << N))
        if any(sum(debt, F(0)) == 0 for debt in debts):
            continue
        cycle = find_constant_debt_cycle(table, debts)
        if cycle is None:
            continue
        masks, movers = cycle
        for source in masks:
            cap = pure_cap(table, source)
            zero = tuple(F(0) for _ in range(N))
            if not is_exact_root_nash(table, cap, zero):
                continue
            grid_nash = [
                root for root in product(ROOT_GRID, repeat=N)
                if is_exact_root_nash(table, cap, root)
            ]
            if grid_nash == [zero]:
                return Candidate(tuple(row), masks, movers, source, trial)
    return None


def stationary_grid_minimum(table: tuple[tuple[F, ...], ...]) -> tuple[F, tuple[F, ...]]:
    best: Optional[tuple[F, tuple[F, ...]]] = None
    for root in product(ROOT_GRID, repeat=N):
        prescribed, cap = stationary_pair(table, root)
        debt = sum((cap[who] - prescribed[who] for who in range(N)), F(0))
        if best is None or debt < best[0]:
            best = debt, root
    assert best is not None
    return best


def stationary_quit_and_never_values(
    table: tuple[tuple[F, ...], ...], root: tuple[F, ...], who: int
) -> tuple[F, F]:
    """The two stationary Snell alternatives against fixed opponents."""

    opponents = [other for other in range(N) if other != who]
    quit_value = F(0)
    continue_reward = F(0)
    continue_mass = F(1)
    for other in opponents:
        continue_mass *= 1 - root[other]
    for bits in range(1 << (N - 1)):
        mask = 0
        probability = F(1)
        for index, other in enumerate(opponents):
            q = root[other]
            if bits & (1 << index):
                mask |= 1 << other
                probability *= q
            else:
                probability *= 1 - q
        quit_value += probability * table[mask | (1 << who)][who]
        if mask:
            continue_reward += probability * table[mask][who]
    assert continue_mass < 1
    return quit_value, continue_reward / (1 - continue_mass)


def frac(value: F) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def symmetric_quit_value(q: F) -> F:
    return 1 - q - q * q - q * q * q


def symmetric_never_value(q: F) -> F:
    return (2 * q - 4 * q * q + 2 * q * q * q) / (3 * q - 3 * q * q + q * q * q)


def symmetric_indifference_polynomial(q: F) -> F:
    return 1 - 2 * q - q**2 - q**3 + 2 * q**4 - q**5


def run() -> dict[str, object]:
    candidate = structural_search()
    if candidate is None:
        return {
            "status": "no_candidate",
            "seed": SEED,
            "trial_limit": TRIAL_LIMIT,
            "family": "C4-equivariant integer rewards in [-2,2], singleton self-payoff in {1,2}",
        }
    table = table_from_row(candidate.row)
    debts = tuple(pure_debt(table, mask) for mask in range(1 << N))
    grid_minimum, grid_root = stationary_grid_minimum(table)
    cap = pure_cap(table, candidate.cap_source)
    left = F(81, 200)
    right = F(203, 500)
    for q in (left, right):
        root = (q,) * N
        for who in range(N):
            quit_value, never_value = stationary_quit_and_never_values(table, root, who)
            assert quit_value == symmetric_quit_value(q)
            assert never_value == symmetric_never_value(q)
        assert (symmetric_quit_value(q) - symmetric_never_value(q)) * (
            3 - 3 * q + q * q
        ) == symmetric_indifference_polynomial(q)
    assert symmetric_indifference_polynomial(left) == F(786263999, 320000000000)
    assert symmetric_indifference_polynomial(right) == F(-14030950243, 31250000000000)
    cycle_gains = [
        table[target][who] - table[source][who]
        for source, target, who in zip(
            candidate.cycle,
            candidate.cycle[1:] + candidate.cycle[:1],
            candidate.movers,
        )
    ]
    return {
        "status": "finite_candidate_rejected_by_continuous_symmetric_root",
        "seed": SEED,
        "trial_limit": TRIAL_LIMIT,
        "found_at_trial": candidate.found_at_trial,
        "family": "C4-equivariant integer rewards in [-2,2]",
        "relative_row_by_mask_1_through_15": candidate.row,
        "cycle_masks": candidate.cycle,
        "cycle_movers": candidate.movers,
        "cycle_gains": tuple(frac(x) for x in cycle_gains),
        "cycle_debt": tuple(frac(sum(debts[mask], F(0))) for mask in candidate.cycle),
        "pure_minimum_debt": frac(min(sum(debt, F(0)) for debt in debts)),
        "cap_source_mask": candidate.cap_source,
        "cap": tuple(frac(x) for x in cap),
        "cap_grid_exact_nash_roots": [["0", "0", "0", "0"]],
        "stationary_grid": [frac(x) for x in ROOT_GRID],
        "stationary_grid_minimum_debt": frac(grid_minimum),
        "stationary_grid_argmin": tuple(frac(x) for x in grid_root),
        "fixed_law_stationary_ray": {
            "law": "Dirac at coalition mask 1",
            "roots": "(q,0,0,0), 0 < q <= 1",
            "debt_vector": ("0", "1", "0", "0"),
            "grid_premium_over_global_grid_minimum": frac(F(1) - grid_minimum),
            "scope": "stationary roots only; not the full fixed-law carrier",
        },
        "continuous_symmetric_rejection": {
            "roots": "(q,q,q,q)",
            "quit_value": "1 - q - q^2 - q^3",
            "never_value": "(2q - 4q^2 + 2q^3)/(3q - 3q^2 + q^3)",
            "indifference_polynomial_after_removing_q":
                "1 - 2q - q^2 - q^3 + 2q^4 - q^5",
            "positive_at": {"q": frac(left), "value": frac(symmetric_indifference_polynomial(left))},
            "negative_at": {"q": frac(right), "value": frac(symmetric_indifference_polynomial(right))},
            "conclusion": (
                "The intermediate value theorem gives q in (81/200,203/500) "
                "where Quit equals Never. C4 symmetry and stationary Bellman "
                "balance then give zero debt for all four players."
            ),
        },
        "warning": (
            "Pure and rational-grid certificates are exact but local. The explicit "
            "symmetric zero-debt root proves that their positive minima do not extend "
            "to the continuous stationary family, hence not to the full terminal-semantic carrier."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
