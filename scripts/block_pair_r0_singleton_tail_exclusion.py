#!/usr/bin/env python3
"""Exclude every one-sided infinite strict singleton-support path.

The hazards may vary arbitrarily and may have either finite or infinite
total clock.  The exact arbitrary-run transition overgraph from
``block_pair_r0_singleton_jump_graph.py`` is a finite DAG.  Thus an infinite
path cannot change its singleton owner infinitely often and must eventually
stay at one of the four singleton masks.

At support 1, player 3 receives zero whether player 0 eventually quits or
play never absorbs.  Quitting immediately gives player 3

    (1-x) r_3({3}) + x r_3({0,3}) = 2+4x >= 2.

The other three constant-owner tails have the same zero-payoff witness:

* owner 1: player 3 gets zero and can quit for exactly 2;
* owner 2: player 1 gets zero and can quit for ``2(1-x)>0``; and
* owner 3: player 1 gets zero and can quit for ``2+4x>=2``.

Thus no one-sided infinite path can remain in strict singleton interiors.

This is a terminal-payoff argument for an actually infinite singleton tail.
It does not exclude long finite singleton blocks that later leave, and it
does not assign an edgewise Q122 potential.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_singleton_jump_graph as jump_graph  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402


one = algebra.one


def assert_support_one_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(1, 3) == 0
    assert terminal(8, 3) == 2
    assert terminal(9, 3) == 6

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, owner_hazard)),
        algebra.scale(6, owner_hazard),
    )
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.add(
        algebra.const(2), algebra.scale(4, owner_hazard)
    )


def assert_support_two_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(2, 3) == 0
    assert terminal(8, 3) == 2
    assert terminal(10, 3) == 2

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, owner_hazard)),
        algebra.scale(2, owner_hazard),
    )
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.const(2)


def assert_support_four_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(4, 1) == 0
    assert terminal(2, 1) == 2
    assert terminal(6, 1) == 0

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.scale(2, algebra.sub(one, owner_hazard))
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.scale(
        2, algebra.sub(one, owner_hazard)
    )


def assert_support_eight_tail_gap() -> None:
    owner_hazard = algebra.var(0)
    assert terminal(8, 1) == 0
    assert terminal(2, 1) == 2
    assert terminal(10, 1) == 6

    prescribed_terminal_payoff = algebra.const(0)
    quit_payoff = algebra.add(
        algebra.scale(2, algebra.sub(one, owner_hazard)),
        algebra.scale(6, owner_hazard),
    )
    deviation_gap = algebra.sub(quit_payoff, prescribed_terminal_payoff)
    assert deviation_gap == algebra.add(
        algebra.const(2), algebra.scale(4, owner_hazard)
    )


def assert_arbitrary_run_graph_acyclic() -> None:
    """Replay the finite DAG containing every singleton owner change."""

    vertices = tuple(
        (left, right)
        for left in range(jump_graph.N)
        for right in range(jump_graph.N)
        if left != right
    )
    run_edges: set[
        tuple[tuple[int, int], tuple[int, int]]
    ] = set()
    run_triples: set[tuple[int, int, int]] = set()
    for previous in range(jump_graph.N):
        for current in range(jump_graph.N):
            for following in range(jump_graph.N):
                if previous == current or current == following:
                    continue
                interval = jump_graph.repeated_run_endpoint_interval(
                    previous, current, following
                )
                if interval is not None:
                    run_triples.add((previous, current, following))
                    run_edges.add(
                        ((current, following), (previous, current))
                    )
    assert frozenset(run_triples) == (
        jump_graph.EXPECTED_RUN_ENVELOPE_TRIPLES
    )
    components = jump_graph.strongly_connected_components(
        vertices, run_edges
    )
    assert all(len(component) == 1 for component in components)


def assert_no_infinite_singleton_tail() -> None:
    assert_arbitrary_run_graph_acyclic()
    assert_support_one_tail_gap()
    assert_support_two_tail_gap()
    assert_support_four_tail_gap()
    assert_support_eight_tail_gap()


def main() -> None:
    assert_no_infinite_singleton_tail()

    print("exact one-sided strict singleton-support exclusion passed")
    print("the arbitrary-run owner-change overgraph is acyclic")
    print("all four eventual constant-owner tails have an exact deviation")
    print("scope: strict singleton interiors; walls/potential remain separate")


if __name__ == "__main__":
    main()
