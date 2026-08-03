#!/usr/bin/env python3
"""Exact run-compressed residual language for the perturbed five-mask core.

Start from the active-coordinate overgraph on supports {1,2,3,6,9}, suppress
all self edges (so each letter denotes a nonempty maximal same-support block),
and stop a walk at its first return to support 6.  The exact local
obstructions proved in the companion checkers forbid the compressed motifs

    {2,6} -> 1 -> 2,
    {2,6} -> 9 -> 2,
    {2,6} -> 9 -> 3 -> 9.

This checker constructs the corresponding finite suffix automaton and proves
that its reachable nonterminal part is acyclic.  Exactly six 6-return
skeletons survive:

    6-1-6,       6-2-1-6,
    6-9-6,       6-2-9-6,
    6-9-3-6,     6-2-9-3-6.

Thus there is no remaining combinatorial period search inside this core.
The singleton-block cases and the two 6-return skeletons ending directly
after support 9 are already ranked for arbitrary finite blocks.  A companion
value argument excludes every finite strict cycle using only supports 3 and
9.  An exact inactive-value obstruction forces the support-9 block after
support 2 or 6 to have length one.  The two remaining 6-return skeletons pass
through support 3 and are ranked when that block also has length one.  To
obtain an all-finite-core-cycle theorem it remains to lift that endpoint rank
to arbitrary nonempty support-3 blocks.

This is a grammar theorem only.  It does not claim those block lifts, does not
cover supports outside the five-mask core, and says nothing about infinite
walks converging to the zero-hazard boundary.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from collections import deque
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_9_run_3_run_obstruction as pair_backtrack  # noqa: E402
import block_pair_r0_core_excursion_grammar as grammar  # noqa: E402
import block_pair_r0_singleton_bridge_ranks as singleton_bridge  # noqa: E402
import block_pair_r0_support3_9_cycle_exclusion as pair_cycles  # noqa: E402
import block_pair_r0_support9_double_obstruction as double_nine  # noqa: E402
import block_pair_r0_support9_run_rank as support_nine_run  # noqa: E402
import block_pair_r0_support9_to_singleton_obstruction as nine_exit  # noqa: E402


FORBIDDEN = frozenset(
    {
        (6, 1, 2),
        (2, 1, 2),
        (6, 9, 2),
        (2, 9, 2),
        (6, 9, 3, 9),
        (2, 9, 3, 9),
    }
)

EXPECTED_RETURNS = frozenset(
    {
        (6, 1, 6),
        (6, 2, 1, 6),
        (6, 9, 6),
        (6, 2, 9, 6),
        (6, 9, 3, 6),
        (6, 2, 9, 3, 6),
    }
)


def forbidden(path: tuple[int, ...]) -> bool:
    return any(
        len(path) >= len(pattern) and path[-len(pattern) :] == pattern
        for pattern in FORBIDDEN
    )


def suffix_state(path: tuple[int, ...]) -> tuple[int, ...]:
    # The longest forbidden word has length four, so its last three letters
    # contain all memory needed for the next transition.
    return path[-3:]


def enumerate_returns() -> tuple[
    frozenset[tuple[int, ...]],
    frozenset[tuple[tuple[int, ...], tuple[int, ...]]],
]:
    edges = frozenset(
        edge for edge in grammar.core_edges() if edge[0] != edge[1]
    )
    queue = deque([(6,)])
    representatives: dict[tuple[int, ...], tuple[int, ...]] = {(6,): (6,)}
    automaton_edges: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    returns: set[tuple[int, ...]] = set()

    while queue:
        path = queue.popleft()
        source_state = suffix_state(path)
        for source, target in edges:
            if source != path[-1]:
                continue
            candidate = (*path, target)
            if forbidden(candidate):
                continue
            if target == 6:
                returns.add(candidate)
                continue
            target_state = suffix_state(candidate)
            automaton_edges.add((source_state, target_state))
            if target_state not in representatives:
                representatives[target_state] = candidate
                queue.append(candidate)

    # Exact acyclicity of the reachable nonterminal suffix automaton.
    adjacency = {
        state: tuple(target for source, target in automaton_edges if source == state)
        for state in representatives
    }
    visiting: set[tuple[int, ...]] = set()
    visited: set[tuple[int, ...]] = set()

    def visit(state: tuple[int, ...]) -> None:
        assert state not in visiting
        if state in visited:
            return
        visiting.add(state)
        for target in adjacency[state]:
            visit(target)
        visiting.remove(state)
        visited.add(state)

    visit((6,))
    assert visited == set(representatives)

    # Now that the suffix automaton is known acyclic, enumerate every full
    # path rather than relying on one representative per suffix state.
    all_returns: set[tuple[int, ...]] = set()

    def explore(path: tuple[int, ...]) -> None:
        for source, target in edges:
            if source != path[-1]:
                continue
            candidate = (*path, target)
            if forbidden(candidate):
                continue
            if target == 6:
                all_returns.add(candidate)
            else:
                explore(candidate)

    explore((6,))
    assert returns <= all_returns
    return frozenset(all_returns), frozenset(automaton_edges)


def replay_local_ingredients() -> None:
    singleton_bridge.assert_support_one_block_obstruction()
    singleton_bridge.assert_arbitrary_singleton_word_return_rank()
    singleton_bridge.assert_support_two_effective_hazard_rank()
    support_nine_run.assert_arbitrary_support9_run_rank()
    double_nine.assert_entry_clock()
    double_nine.assert_second_inactive_difference()
    double_nine.assert_positive_numerator()
    nine_exit.assert_one_step_positivity_packet()

    pair_backtrack.assert_block_obstruction()
    pair_cycles.assert_support_nine_player_three_transport()
    pair_cycles.assert_support_three_player_three_bound()
    pair_cycles.assert_cycle_gap()


def main() -> None:
    returns, automaton_edges = enumerate_returns()
    assert returns == EXPECTED_RETURNS
    replay_local_ingredients()

    singleton_returns = frozenset({(6, 1, 6), (6, 2, 1, 6)})
    pair_returns = returns - singleton_returns
    assert len(singleton_returns) == 2
    assert len(pair_returns) == 4

    print("exact run-compressed five-mask residual language passed")
    print(f"reachable suffix-automaton edges = {len(automaton_edges)}")
    print(f"surviving 6-return skeletons = {len(returns)}")
    for path in sorted(returns):
        print("  " + "->".join(map(str, path)))
    print("singleton skeletons are ranked for arbitrary finite blocks")
    print("all finite strict 3/9-only cycles are excluded separately")
    print("arbitrary support-9 blocks in the two direct 6-returns are ranked")
    print("entered support-9 blocks have length one")
    print("remaining lift: arbitrary support-3 blocks in two 6-returns")
    print("scope: strict five-mask finite grammar; infinite/boundary paths remain")


if __name__ == "__main__":
    main()
