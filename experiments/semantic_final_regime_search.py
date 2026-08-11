"""Exact negative controls for the final minimum-semantic regimes.

This is a deliberately narrow ``Fraction`` search/replayer for Session XVIII.
It does not pretend to decide membership in the *minimum* semantic fibre: that
condition already quantifies over the whole executable carrier and, in a game
with an exact equilibrium, its minimum debt is zero.

What the script does certify is the complete finite/static passport surrounding
that condition:

* an executable terminal-semantic pair with one positive debtor;
* an exact atomic solo root at its singleton endpoint;
* the first affine support breakpoint and its collision orientation;
* the exact punishment sandwich, by matching lower and upper certificates;
* absence/presence of pure stationary equilibria and exact rational stationary
  equilibria on a stated grid;
* executable examples of all three marked plateau atoms (Never, collision,
  and waiting/opponent absorption).

The examples are negative controls.  Whenever a solved stationary row is
reported, its zero-debt semantic pair proves that the positive-debt witness was
not minimum.  Thus the computation isolates minimum-fibre provenance as a
load-bearing hypothesis rather than producing a counterexample.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from typing import Dict, FrozenSet, Iterable, Optional, Sequence, Tuple


N = 4
Player = int
Coalition = FrozenSet[Player]
Vector = Tuple[F, ...]
Reward = Dict[Coalition, Vector]


def coalitions(players: Iterable[int] = range(N)) -> Iterable[Coalition]:
    listed = tuple(players)
    for size in range(1, len(listed) + 1):
        for chosen in combinations(listed, size):
            yield frozenset(chosen)


def blank_table(default: F = F(0)) -> Reward:
    return {coalition: tuple(default for _ in range(N)) for coalition in coalitions()}


def set_coordinate(reward: Reward, coalition: Coalition, who: int, value: F) -> None:
    row = list(reward[coalition])
    row[who] = value
    reward[coalition] = tuple(row)


def r(reward: Reward, coalition: Iterable[int], who: int) -> F:
    return reward[frozenset(coalition)][who]


def expectation(reward: Reward, quit_rates: Sequence[F]) -> Tuple[F, Vector]:
    """One-row absorption probability and unconditional reward contribution."""

    absorb = F(0)
    value = [F(0) for _ in range(N)]
    for action in product((False, True), repeat=N):
        probability = F(1)
        quitting = set()
        for who, quits in enumerate(action):
            probability *= quit_rates[who] if quits else 1 - quit_rates[who]
            if quits:
                quitting.add(who)
        if not quitting:
            continue
        absorb += probability
        terminal = reward[frozenset(quitting)]
        for who in range(N):
            value[who] += probability * terminal[who]
    return absorb, tuple(value)


def stationary_value(reward: Reward, quit_rates: Sequence[F]) -> Optional[Vector]:
    absorb, contribution = expectation(reward, quit_rates)
    if absorb == 0:
        return None
    return tuple(value / absorb for value in contribution)


def root_gain(
    reward: Reward, tail: Vector, quit_rates: Sequence[F], who: int
) -> F:
    """Exact Quit-minus-Continue gain against the other coordinates."""

    quit_value = F(0)
    continue_value = F(0)
    opponents = [player for player in range(N) if player != who]
    for action in product((False, True), repeat=len(opponents)):
        probability = F(1)
        quitting = set()
        for player, quits in zip(opponents, action):
            probability *= quit_rates[player] if quits else 1 - quit_rates[player]
            if quits:
                quitting.add(player)
        quit_value += probability * r(reward, quitting | {who}, who)
        continue_value += probability * (
            r(reward, quitting, who) if quitting else tail[who]
        )
    return quit_value - continue_value


def complementary(rate: F, gain: F) -> bool:
    if rate == 0:
        return gain <= 0
    if rate == 1:
        return gain >= 0
    return gain == 0


def exact_stationary_root(reward: Reward, quit_rates: Sequence[F]) -> Optional[dict]:
    value = stationary_value(reward, quit_rates)
    if value is None:
        return None
    gains = tuple(root_gain(reward, value, quit_rates, who) for who in range(N))
    if not all(complementary(quit_rates[who], gains[who]) for who in range(N)):
        return None
    support = tuple(who for who, rate in enumerate(quit_rates) if rate > 0)
    # A period-one absorbing root is admissible if every negative-solo player
    # has an opponent in support, or has nonnegative solo reward.
    admissible = all(
        any(other != who for other in support) or r(reward, {who}, who) >= 0
        for who in range(N)
    )
    return {
        "rates": tuple(quit_rates),
        "value": value,
        "gains": gains,
        "support": support,
        "admissible": admissible,
    }


def pure_stationary_roots(reward: Reward) -> list[dict]:
    roots = []
    for support in coalitions():
        rates = tuple(F(int(who in support)) for who in range(N))
        certificate = exact_stationary_root(reward, rates)
        if certificate is not None:
            roots.append(certificate)
    return roots


def rational_stationary_roots(reward: Reward, grid: Sequence[F]) -> list[dict]:
    roots = []
    seen = set()
    for rates in product(grid, repeat=N):
        certificate = exact_stationary_root(reward, rates)
        if certificate is None:
            continue
        key = certificate["rates"]
        if key not in seen:
            seen.add(key)
            roots.append(certificate)
    return roots


@dataclass(frozen=True)
class AtomicCertificate:
    rate: F
    tail: Vector
    envelope: Vector
    debt: Vector
    entrant: int
    breakpoint: F
    entrant_gain: F
    other_gains: Tuple[F, ...]
    owner_collision: F
    reverse_entrant_collision: F
    punishment_value: F
    punishment_gap: F
    one_outsider_cap: F


def singleton_absorption_semantics(reward: Reward, owner: int) -> Tuple[Vector, Vector]:
    """Semantics of the profile where only ``owner`` quits immediately."""

    prescribed = reward[frozenset({owner})]
    envelope = []
    for who in range(N):
        if who == owner:
            envelope.append(max(r(reward, {owner}, owner), F(0)))
        else:
            envelope.append(max(r(reward, {owner}, who), r(reward, {owner, who}, who)))
    return prescribed, tuple(envelope)


def certify_owner_punishment_zero(reward: Reward, owner: int) -> F:
    """Exact certificate that the owner's punishment value is zero.

    Lower leg: every opponent-only terminal payoff to the owner is nonnegative,
    so the Continue branch of every stationary cap is nonnegative (Never gives
    zero when opponents never absorb).  Upper leg: choose any pure nonempty
    opponent set whose Continue payoff is zero and whose joined payoff is at
    most zero.  Stationary min-max equality then gives chi=0.
    """

    opponent_sets = list(coalitions(player for player in range(N) if player != owner))
    assert all(r(reward, terminal, owner) >= 0 for terminal in opponent_sets)
    witness = next(
        terminal
        for terminal in opponent_sets
        if r(reward, terminal, owner) == 0
        and r(reward, set(terminal) | {owner}, owner) <= 0
    )
    assert max(r(reward, witness, owner), r(reward, set(witness) | {owner}, owner)) == 0
    return F(0)


def atomic_certificate(
    reward: Reward, owner: int = 0, entrant: int = 1, rate: F = F(1, 2)
) -> AtomicCertificate:
    tail, envelope = singleton_absorption_semantics(reward, owner)
    debt = tuple(envelope[who] - tail[who] for who in range(N))
    rates = tuple(rate if who == owner else F(0) for who in range(N))
    gains = tuple(root_gain(reward, tail, rates, who) for who in range(N))
    assert 0 < rate <= 1
    assert debt[owner] > 0 and all(debt[who] == 0 for who in range(N) if who != owner)
    assert all(complementary(rates[who], gains[who]) for who in range(N))
    assert r(reward, {entrant}, entrant) > tail[entrant]

    attractive = r(reward, {entrant}, entrant) - tail[entrant]
    collision_loss = r(reward, {entrant}, entrant) - r(reward, {owner, entrant}, entrant)
    assert collision_loss > 0
    breakpoint = attractive / collision_loss
    assert breakpoint == rate and gains[entrant] == 0
    # At the first feasible rate every other inactive inequality must hold.
    for who in range(N):
        if who not in (owner, entrant):
            assert gains[who] < 0

    owner_collision = r(reward, {owner, entrant}, owner) - r(reward, {entrant}, owner)
    assert owner_collision != 0
    reverse_collision = (
        r(reward, {owner, entrant}, entrant) - r(reward, {owner}, entrant)
    )
    punishment = certify_owner_punishment_zero(reward, owner)
    assert r(reward, {owner}, owner) < punishment <= 0
    punishment_gap = punishment - r(reward, {owner}, owner)
    one_outsider_cap = max(
        r(reward, {owner, entrant}, owner), r(reward, {entrant}, owner)
    )
    assert r(reward, {owner}, owner) < one_outsider_cap
    assert punishment_gap <= one_outsider_cap - r(reward, {owner}, owner)
    if rate == 1:
        # Sharp one-sided boundary theorem from the completed §18 wave.
        assert owner_collision < 0
        assert reverse_collision == 0
        assert r(reward, {owner}, owner) < r(reward, {entrant}, owner)
        assert punishment_gap <= r(reward, {entrant}, owner) - r(reward, {owner}, owner)
    return AtomicCertificate(
        rate,
        tail,
        envelope,
        debt,
        entrant,
        breakpoint,
        gains[entrant],
        tuple(gains[who] for who in range(N) if who not in (owner, entrant)),
        owner_collision,
        reverse_collision,
        punishment,
        punishment_gap,
        one_outsider_cap,
    )


def atomic_no_pure_root_table() -> Reward:
    """A small integral atomic passport with no admissible pure root."""

    reward = blank_table()
    owner = 0
    # Owner: solo is negative, opponent-only outcomes are zero, and joining an
    # opponent coalition pays -1.  Hence chi_0=0 and every coalition containing
    # owner has an immediate owner exit deviation.
    set_coordinate(reward, frozenset({owner}), owner, F(-2))
    for terminal in coalitions(player for player in range(N) if player != owner):
        set_coordinate(reward, terminal, owner, F(0))
        set_coordinate(reward, frozenset(set(terminal) | {owner}), owner, F(-1))

    # Entrant 1 is attractive and exactly tight at owner rate 1/2.
    set_coordinate(reward, frozenset({1}), 1, F(1))
    set_coordinate(reward, frozenset({0}), 1, F(0))
    set_coordinate(reward, frozenset({0, 1}), 1, F(-1))

    # Other outsiders are strictly deterred at the same boundary.
    for who in (2, 3):
        set_coordinate(reward, frozenset({who}), who, F(0))
        set_coordinate(reward, frozenset({0}), who, F(0))
        set_coordinate(reward, frozenset({0, who}), who, F(-1))

    # Kill every opponent-only pure support by an explicit profitable move.
    # {1}: 2 joins; {2}: 3 joins; {3}: 1 joins.
    set_coordinate(reward, frozenset({1}), 2, F(0))
    set_coordinate(reward, frozenset({1, 2}), 2, F(1))
    set_coordinate(reward, frozenset({2}), 3, F(0))
    set_coordinate(reward, frozenset({2, 3}), 3, F(1))
    set_coordinate(reward, frozenset({3}), 1, F(0))
    set_coordinate(reward, frozenset({1, 3}), 1, F(1))
    # {1,2}: 1 leaves; {2,3}: 2 leaves; {1,3}: 3 leaves.
    set_coordinate(reward, frozenset({1, 2}), 1, F(-1))
    set_coordinate(reward, frozenset({2}), 1, F(0))
    set_coordinate(reward, frozenset({2, 3}), 2, F(-1))
    set_coordinate(reward, frozenset({3}), 2, F(0))
    set_coordinate(reward, frozenset({1, 3}), 3, F(-1))
    set_coordinate(reward, frozenset({1}), 3, F(0))
    # {1,2,3}: 1 leaves to {2,3}.
    set_coordinate(reward, frozenset({1, 2, 3}), 1, F(-1))
    set_coordinate(reward, frozenset({2, 3}), 1, F(0))
    return reward


def atomic_generic_grid_control() -> Reward:
    """Perturb only free zero entries to remove accidental rational ties.

    The denominator 101 is deliberately coprime to the quarter-grid.  All
    strict blocker inequalities in ``atomic_no_pure_root_table`` have unit
    margin, while the atomic endpoint entries are protected exactly.
    """

    reward = atomic_no_pure_root_table()
    protected = {
        (frozenset({0}), who) for who in (1, 2, 3)
    } | {
        (frozenset({who}), who) for who in (1, 2, 3)
    } | {
        (frozenset({0, who}), who) for who in (1, 2, 3)
    }
    for terminal in coalitions():
        mask = sum(1 << who for who in terminal)
        for who in (1, 2, 3):
            if (terminal, who) in protected or r(reward, terminal, who) != 0:
                continue
            numerator = ((7 * mask + 11 * who) % 17) - 8
            if numerator == 0:
                numerator = who + 1
            set_coordinate(reward, terminal, who, F(numerator, 101))
    # The unit-margin pure-support blockers remain strict.
    return reward


def atomic_rate_one_table() -> Reward:
    """The sharp sure-Quit boundary, including both collision orientations."""

    reward = atomic_no_pure_root_table()
    # Entrant 1's solo gain remains +1 at owner rate zero but its collision
    # gain becomes exactly zero.  Hence its affine first feasible rate is 1.
    # On the reverse side the owner's increment is still -1.
    set_coordinate(reward, frozenset({0, 1}), 1, F(0))
    return reward


@dataclass(frozen=True)
class PlateauCertificate:
    kind: str
    debtor: int
    prescribed: Vector
    envelope: Vector
    debt: Vector
    profitable_outcome: Optional[Coalition]
    profitable_gain: F


def plateau_collision_table() -> Tuple[Reward, PlateauCertificate]:
    reward = blank_table()
    # Actual profile: player 1 quits immediately.  Player 0 can join.
    set_coordinate(reward, frozenset({1}), 0, F(0))
    set_coordinate(reward, frozenset({0, 1}), 0, F(1))
    prescribed = reward[frozenset({1})]
    envelope = tuple(
        max(r(reward, {1}, who), r(reward, {1, who}, who)) if who != 1
        else max(r(reward, {1}, who), F(0))
        for who in range(N)
    )
    debt = tuple(envelope[who] - prescribed[who] for who in range(N))
    assert r(reward, {who := 0}, 0) <= prescribed[0]  # all-Continue gate
    assert debt[0] == 1 and all(debt[who] == 0 for who in range(1, N))
    return reward, PlateauCertificate(
        "collision", 0, prescribed, envelope, debt, frozenset({0, 1}), F(1)
    )


def plateau_waiting_table() -> Tuple[Reward, PlateauCertificate]:
    reward = blank_table()
    # Actual profile: players 0 and 1 quit immediately.  Player 0 profits by
    # waiting/continuing and letting {1} absorb without it.
    set_coordinate(reward, frozenset({0, 1}), 0, F(0))
    set_coordinate(reward, frozenset({1}), 0, F(1))
    prescribed = reward[frozenset({0, 1})]
    envelope = list(prescribed)
    envelope[0] = F(1)
    debt = tuple(envelope[who] - prescribed[who] for who in range(N))
    assert r(reward, {0}, 0) <= prescribed[0]
    assert debt[0] == 1 and all(debt[who] == 0 for who in range(1, N))
    return reward, PlateauCertificate(
        "waiting", 0, prescribed, tuple(envelope), debt, frozenset({1}), F(1)
    )


def plateau_never_table() -> Tuple[Reward, PlateauCertificate]:
    reward = blank_table()
    # Actual profile: player 0 quits immediately for -1 while everyone else
    # continues.  Never yields zero.
    set_coordinate(reward, frozenset({0}), 0, F(-1))
    prescribed = reward[frozenset({0})]
    envelope = list(prescribed)
    envelope[0] = F(0)
    debt = tuple(envelope[who] - prescribed[who] for who in range(N))
    assert all(r(reward, {who}, who) <= prescribed[who] for who in range(N))
    assert debt[0] == 1 and all(debt[who] == 0 for who in range(1, N))
    return reward, PlateauCertificate(
        "never", 0, prescribed, tuple(envelope), debt, None, F(1)
    )


def render_fraction(value: F) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def render_tuple(values: Sequence[F]) -> str:
    return "(" + ", ".join(render_fraction(value) for value in values) + ")"


def small_probability_grid(max_denominator: int) -> Tuple[F, ...]:
    return tuple(sorted({F(numerator, denominator)
        for denominator in range(1, max_denominator + 1)
        for numerator in range(denominator + 1)}))


def main() -> None:
    grid = small_probability_grid(5)
    for label, constructor, displayed_rate in (
        ("integral-interior", atomic_no_pure_root_table, F(1, 2)),
        ("generic-denominator-101-interior", atomic_generic_grid_control, F(1, 2)),
        ("integral-rate-one", atomic_rate_one_table, F(1)),
    ):
        atomic = constructor()
        certificate = atomic_certificate(atomic, rate=displayed_rate)
        pure = pure_stationary_roots(atomic)
        rational = rational_stationary_roots(atomic, grid)
        solved_pure = [root for root in pure if root["admissible"]]
        solved_grid = [root for root in rational if root["admissible"]]

        print(f"ATOMIC STATIC PASSPORT ({label})")
        print(f"  tail={render_tuple(certificate.tail)}")
        print(f"  envelope={render_tuple(certificate.envelope)}")
        print(f"  debt={render_tuple(certificate.debt)}")
        print(f"  first support breakpoint={render_fraction(certificate.breakpoint)}")
        print(f"  owner collision={render_fraction(certificate.owner_collision)}")
        print(f"  reverse entrant collision={render_fraction(certificate.reverse_entrant_collision)}")
        print(f"  punishment value={render_fraction(certificate.punishment_value)}")
        print(f"  punishment gap={render_fraction(certificate.punishment_gap)}")
        print(f"  one-outsider cap={render_fraction(certificate.one_outsider_cap)}")
        print(f"  pure local roots={len(pure)}; admissible/solved={len(solved_pure)}")
        print(
            f"  exact roots on reduced-denominator<=5 grid={len(rational)};"
            f" admissible/solved={len(solved_grid)}"
        )
        for root in rational[:8]:
            print(
                "    rates=" + render_tuple(root["rates"])
                + " value=" + render_tuple(root["value"])
                + f" support={root['support']} admissible={root['admissible']}"
            )
        assert not solved_pure

    print("PLATEAU MARKED-ATOM NEGATIVE CONTROLS")
    for constructor in (plateau_never_table, plateau_collision_table, plateau_waiting_table):
        reward, plateau = constructor()
        solved = pure_stationary_roots(reward)
        solved_admissible = [root for root in solved if root["admissible"]]
        print(
            f"  {plateau.kind}: debt={render_tuple(plateau.debt)}"
            + f" gain={render_fraction(plateau.profitable_gain)}"
            + f" pure local roots={len(solved)}"
            + f" admissible/solved={len(solved_admissible)}"
        )

if __name__ == "__main__":
    main()
