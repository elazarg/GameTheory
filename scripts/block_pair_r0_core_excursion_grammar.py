#!/usr/bin/env python3
"""Exact active-coordinate grammar for the five-mask perturbed core.

Work in the block-pair quitting game with ``r_0({0})=-189/100`` and restrict
attention to strict phases with support in

    1={0}, 2={1}, 3={0,1}, 6={1,2}, 9={0,3}.

This checker derives a *necessary* adjacent-support graph using only active
Bellman equalities.  It deliberately drops every inactive Nash inequality,
so every genuine strict path in this five-mask core is represented, while a
listed edge need not itself extend to a credible path.

For an active player i at a pair {i,j}, put

    z_i = (V_i-q_i)/2.

At the current phase and its successor, active indifference gives

    z_i       = b_ij*x_j,
    z_i^plus  = a_ij*odds(x_j).

At a singleton-i phase both quantities are zero.  Hence a player active on
both sides of an edge supplies an immediate sign/zero compatibility test.
Applying that test gives

    1 -> {1,2,6},       2 -> {1,2,9},
    3 -> {3,6,9},       6 -> {1,2,9},
    9 -> {2,3,6,9}.

After deleting self repetitions and cutting at visits to support 6, the
internal graph is exactly the bidirected path

    1 <-> 2 <-> 9 <-> 3.

Thus every finite 6-to-6 core excursion is a walk in a tree, beginning at
1, 2, or 9 and ending at 1, 9, or 3.  Its simple skeleton is one of the nine
paths asserted below; every additional complexity is repeated-mode waiting
or edge backtracking.  This isolates the remaining transfer grammar without
bounding the excursion length.

Scope is essential.  The graph is an active-coordinate over-approximation
inside these five supports.  It does not cover other support masks,
zero-hazard/product-flow limits, sure hazards, or nonperiodic boundary
convergence.  In particular, its cycles are not equilibrium witnesses.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_r0_constant_pair_support import (  # noqa: E402
    COEFFICIENTS,
    SOLO,
    terminal,
)


Q = Fraction
CORE = (1, 2, 3, 6, 9)


def active_players(mask: int) -> tuple[int, ...]:
    return tuple(player for player in range(4) if mask & (1 << player))


def current_coefficient(mask: int, player: int) -> Fraction:
    """Coefficient of the other active hazard in current ``z_player``."""

    active = active_players(mask)
    assert player in active and len(active) in (1, 2)
    if len(active) == 1:
        return Q(0)
    opponent = active[0] if active[1] == player else active[1]
    return COEFFICIENTS[player, opponent][1]


def successor_coefficient(mask: int, player: int) -> Fraction:
    """Coefficient of odds(other hazard) in successor ``z_player``."""

    active = active_players(mask)
    assert player in active and len(active) in (1, 2)
    if len(active) == 1:
        return Q(0)
    opponent = active[0] if active[1] == player else active[1]
    return COEFFICIENTS[player, opponent][0]


def same_open_ray(left: Fraction, right: Fraction) -> bool:
    """Whether ``left*odds(x)=right*y`` is soluble for x,y in (0,1)."""

    return (left == 0 and right == 0) or left * right > 0


def active_coordinate_compatible(current: int, following: int) -> bool:
    shared = set(active_players(current)) & set(active_players(following))
    return all(
        same_open_ray(
            successor_coefficient(current, player),
            current_coefficient(following, player),
        )
        for player in shared
    )


def core_edges() -> frozenset[tuple[int, int]]:
    return frozenset(
        (current, following)
        for current in CORE
        for following in CORE
        if active_coordinate_compatible(current, following)
    )


EXPECTED_EDGES = frozenset(
    {
        (1, 1),
        (1, 2),
        (1, 6),
        (2, 1),
        (2, 2),
        (2, 9),
        (3, 3),
        (3, 6),
        (3, 9),
        (6, 1),
        (6, 2),
        (6, 9),
        (9, 2),
        (9, 3),
        (9, 6),
        (9, 9),
    }
)

INTERNAL_LINE_EDGES = frozenset(
    {(1, 2), (2, 1), (2, 9), (9, 2), (9, 3), (3, 9)}
)

EXPECTED_SIMPLE_SIX_EXCURSIONS = frozenset(
    {
        (6, 1, 6),
        (6, 1, 2, 9, 6),
        (6, 1, 2, 9, 3, 6),
        (6, 2, 1, 6),
        (6, 2, 9, 6),
        (6, 2, 9, 3, 6),
        (6, 9, 6),
        (6, 9, 2, 1, 6),
        (6, 9, 3, 6),
    }
)


def simple_six_excursions(edges: frozenset[tuple[int, int]]) -> frozenset[tuple[int, ...]]:
    """Enumerate 6-return paths with no repeated internal support."""

    result: set[tuple[int, ...]] = set()

    def visit(path: tuple[int, ...]) -> None:
        current = path[-1]
        for source, target in edges:
            if source != current or target == current:
                continue
            if target == 6:
                if len(path) > 1:
                    result.add((*path, 6))
                continue
            if target in path:
                continue
            visit((*path, target))

    visit((6,))
    return frozenset(result)


def assert_pair_three_transport() -> None:
    """Replay the exact shared-player Möbius coefficients on 3/9 edges."""

    a01, b01 = COEFFICIENTS[0, 1]
    a03, b03 = COEFFICIENTS[0, 3]
    assert (a01, b01) == (Q(-9, 2), Q(-311, 200))
    assert (a03, b03) == (Q(-1), Q(-411, 200))
    # If x is the current hazard of player 0's opponent, the displayed
    # coefficient multiplies odds(x) to give that opponent's next hazard.
    assert a01 / b01 == Q(900, 311)  # 3 -> 3
    assert a01 / b03 == Q(300, 137)  # 3 -> 9
    assert a03 / b01 == Q(200, 311)  # 9 -> 3
    assert a03 / b03 == Q(200, 411)  # 9 -> 9


def assert_singleton_endpoint_packets() -> None:
    # These are the exact singleton endpoints used when maximal {1,6} and
    # {2,9} runs are collapsed by the companion rank checker.
    assert SOLO[0] == terminal(1, 0) == Q(-189, 100)
    assert SOLO[1] == terminal(2, 1) == 2
    assert (terminal(4, 2), terminal(6, 2), terminal(1, 2)) == (2, 6, 0)
    assert (terminal(8, 3), terminal(9, 3), terminal(2, 3)) == (2, 6, 0)


def main() -> None:
    edges = core_edges()
    assert edges == EXPECTED_EDGES

    internal_without_six_or_self = frozenset(
        (source, target)
        for source, target in edges
        if source != 6 and target != 6 and source != target
    )
    assert internal_without_six_or_self == INTERNAL_LINE_EDGES
    assert simple_six_excursions(edges) == EXPECTED_SIMPLE_SIX_EXCURSIONS

    families = {1: "A", 6: "A", 2: "B", 9: "B", 3: "C"}
    external_family_edges = frozenset(
        (families[source], families[target])
        for source, target in edges
        if families[source] != families[target]
    )
    assert external_family_edges == frozenset(
        {("A", "B"), ("B", "A"), ("B", "C"), ("C", "A"), ("C", "B")}
    )

    assert_pair_three_transport()
    assert_singleton_endpoint_packets()

    print("exact five-mask active-coordinate grammar passed")
    print("successors: 1->{1,2,6}; 2->{1,2,9}; 3->{3,6,9}")
    print("            6->{1,2,9}; 9->{2,3,6,9}")
    print("cutting at support 6 leaves the bidirected line 1<->2<->9<->3")
    print(f"simple 6-return skeletons = {len(EXPECTED_SIMPLE_SIX_EXCURSIONS)}")
    print("scope: necessary five-mask finite grammar; not a global path exclusion")


if __name__ == "__main__":
    main()
