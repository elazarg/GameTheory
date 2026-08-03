#!/usr/bin/env python3
"""Exact obstruction to one global affine clock rank for a perturbed table.

The payoff table is the block-pair table with

    r_0({0}) = -2 + 11/100.

This checker constructs five rational, nonterminal, singleton-support
Nash-predecessor edges.  If d_k = (w_k - v_k) / p_k is the normalized
value drift of edge k, strictly positive rational weights alpha_k satisfy

    sum_k alpha_k = 1,
    sum_k alpha_k * d_k = 0.

Consequently no affine potential Phi(z) = lambda dot z + constant and
c > 0 can satisfy

    Phi(w) - Phi(v) >= c * p

on the full local Nash-predecessor relation: multiplying the five normalized
inequalities by alpha_k and summing would give 0 >= c.

This does not obstruct a smaller cap-augmented relation, a mode-dependent
piecewise potential, or any equilibrium construction.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this assertion-based exact certificate must not run under python -O"
    )

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


Q = Fraction
THETA = Q(11, 100)
ZERO = Q(0)
ONE = Q(1)


def terminal(mask: int, player: int) -> Fraction:
    value = Q(TERMINAL[mask][player])
    if mask == 1 and player == 0:
        value += THETA
    return value


LOWER = tuple(
    min(ZERO, *(terminal(mask, player) for mask in range(1, 1 << N)))
    for player in range(N)
)
UPPER = tuple(
    max(ZERO, *(terminal(mask, player) for mask in range(1, 1 << N)))
    for player in range(N)
)


def probability(
    root: tuple[Fraction, ...],
    mask: int,
    omitted: int | None = None,
) -> Fraction:
    result = ONE
    for player in range(N):
        if player == omitted:
            continue
        result *= (
            root[player] if mask & (1 << player) else ONE - root[player]
        )
    return result


def action_differences(
    root: tuple[Fraction, ...],
    successor: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    result = []
    for player in range(N):
        quit_value = ZERO
        continue_absorption = ZERO
        opponent_survival = ZERO
        for mask in range(1 << N):
            if mask & (1 << player):
                continue
            mass = probability(root, mask, omitted=player)
            quit_value += mass * terminal(mask | (1 << player), player)
            if mask:
                continue_absorption += mass * terminal(mask, player)
            else:
                opponent_survival = mass
        result.append(
            quit_value
            - continue_absorption
            - opponent_survival * successor[player]
        )
    return tuple(result)


def predecessor(
    root: tuple[Fraction, ...],
    successor: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    immediate = [ZERO for _ in range(N)]
    for mask in range(1, 1 << N):
        mass = probability(root, mask)
        for player in range(N):
            immediate[player] += mass * terminal(mask, player)
    survival = probability(root, 0)
    return tuple(
        immediate[player] + survival * successor[player]
        for player in range(N)
    )


@dataclass(frozen=True)
class Edge:
    quitter: int
    hazard: Fraction
    successor: tuple[Fraction, ...]
    normalized_drift: tuple[Fraction, ...]

    @property
    def root(self) -> tuple[Fraction, ...]:
        return tuple(
            self.hazard if player == self.quitter else ZERO
            for player in range(N)
        )


EDGES = (
    Edge(
        0,
        Q(1, 1000),
        (Q(-189, 100), Q(221, 111), Q(2), Q(668, 333)),
        (Q(0), Q(667, 111), Q(-2), Q(-668, 333)),
    ),
    Edge(
        1,
        Q(1, 100),
        (Q(-2179, 1100), Q(2), Q(68, 33), Q(200, 99)),
        (Q(6579, 1100), Q(0), Q(-68, 33), Q(-200, 99)),
    ),
    Edge(
        2,
        Q(1, 10),
        (Q(-1301, 900), Q(2), Q(2), Q(4, 3)),
        (Q(-2299, 900), Q(-2), Q(0), Q(20, 3)),
    ),
    Edge(
        3,
        Q(1, 2),
        (Q(-389, 100), Q(8), Q(-1), Q(2)),
        (Q(-11, 100), Q(-8), Q(9), Q(0)),
    ),
    Edge(
        3,
        Q(1, 2),
        (Q(-389, 100), Q(8), Q(8), Q(2)),
        (Q(-11, 100), Q(-8), Q(0), Q(0)),
    ),
)


WEIGHTS = (
    Q(34385691, 74795036),
    Q(111162579, 1495900720),
    Q(120309669, 747950360),
    Q(401122481, 3365776620),
    Q(2503154923, 13463106480),
)


def certify_edge(edge: Edge) -> None:
    root = edge.root
    successor = edge.successor
    assert all(LOWER[i] <= successor[i] <= UPPER[i] for i in range(N))
    assert all(ZERO <= hazard < ONE for hazard in root)

    absorption = ONE - probability(root, 0)
    assert absorption == edge.hazard
    assert 0 < absorption < 1

    differences = action_differences(root, successor)
    for player in range(N):
        # Closed polynomial encoding of a binary mixed-action Nash profile.
        assert root[player] * differences[player] >= 0
        assert (ONE - root[player]) * differences[player] <= 0
    assert differences[edge.quitter] == 0

    current = predecessor(root, successor)
    assert all(LOWER[i] <= current[i] <= UPPER[i] for i in range(N))
    assert tuple(
        (current[i] - successor[i]) / absorption for i in range(N)
    ) == edge.normalized_drift


def main() -> None:
    assert N == 4
    assert len(EDGES) == len(WEIGHTS) == 5
    for edge in EDGES:
        certify_edge(edge)

    assert all(weight > 0 for weight in WEIGHTS)
    assert sum(WEIGHTS, ZERO) == 1
    barycenter = tuple(
        sum(
            WEIGHTS[index] * EDGES[index].normalized_drift[player]
            for index in range(len(EDGES))
        )
        for player in range(N)
    )
    assert barycenter == (ZERO, ZERO, ZERO, ZERO)

    print("exact affine absorption-clock barrier obstruction passed")
    print(f"theta = {THETA}")
    print(f"edges = {len(EDGES)}")
    print("all five edges are nonterminal local Nash-predecessor edges")
    print("positive convex combination of normalized drifts = (0,0,0,0)")
    print("scope: full local relation/global affine potential only")


if __name__ == "__main__":
    main()
