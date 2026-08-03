#!/usr/bin/env python3
"""Exclude every one-sided infinite strict path on supports 3 and 9.

The existing finite-cycle theorem left a one-sided nonperiodic 3/9 path
open.  Exact forward growth closes that interior case.

At a support-9 self transition, player 3's active equality transports player
0's hazard by

    c' = (3/2)c/(1-c) > (3/2)c.

At a support-3 self transition, the corresponding active transport is

    e' = 3e/(1-e) > 3e.

Finally, collapse any nonempty support-3 block between two support-9 blocks.
If ``c`` is player 0's hazard at the last entering support-9 phase, ``C`` is
its hazard at the first returning support-9 phase, and ``S`` is survival
through the support-3 block, player 3's value equations give

    2 + 6c/(1-c) <= 2 + 4SC,

so ``C >= (3/2)c/((1-c)S) > (3/2)c``.

Hence an infinite strict path that eventually stays in one support has a
positive hazard growing geometrically, and a path switching infinitely often
has its first support-9 hazards grow geometrically.  Either exceeds one after
finitely many steps, a contradiction.

This removes one-sided *strict interior* 3/9 paths.  It does not cover paths
whose finite approximants escape to the zero-hazard boundary, chattering
directional limits, or other support masks.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_support3_9_cycle_exclusion as finite_cycles  # noqa: E402
from block_pair_r0_constant_pair_support import terminal  # noqa: E402


Q = Fraction
one = algebra.one


def assert_support_nine_geometric_growth() -> None:
    finite_cycles.assert_support_nine_player_three_transport()
    current = algebra.var(0)
    following = algebra.var(1)
    transport = algebra.sub(
        algebra.scale(
            2, algebra.mul(algebra.sub(one, current), following)
        ),
        algebra.scale(3, current),
    )
    # On transport=0, clearing the positive denominator proves
    # following-(3/2)current = (3/2)current^2/(1-current)>0.
    cleared_gap = algebra.sub(
        algebra.scale(
            2,
            algebra.mul(
                algebra.sub(one, current),
                algebra.sub(
                    following, algebra.scale(Q(3, 2), current)
                ),
            ),
        ),
        transport,
    )
    assert cleared_gap == algebra.scale(3, algebra.mul(current, current))


def assert_support_three_geometric_growth() -> None:
    current = algebra.var(0)
    following = algebra.var(1)
    transport = algebra.sub(
        algebra.mul(algebra.sub(one, current), following),
        algebra.scale(3, current),
    )
    # following=3current/(1-current), hence following>3current.
    cleared_gap = algebra.sub(
        algebra.mul(
            algebra.sub(one, current),
            algebra.sub(following, algebra.scale(3, current)),
        ),
        transport,
    )
    assert cleared_gap == algebra.scale(3, algebra.mul(current, current))


def assert_support_three_block_growth() -> None:
    """Collapse an arbitrary finite strict 3 block between two 9 blocks."""

    assert tuple(terminal(mask, 3) for mask in (1, 2, 3)) == (0, 0, 2)
    entering = algebra.var(0)
    returning = algebra.var(1)
    survival = algebra.var(2)
    aggregate = algebra.var(3)

    # Exact block entry value and the terminal-payoff upper relaxation.
    exact_entry = algebra.add(
        aggregate,
        algebra.mul(
            survival,
            algebra.add(algebra.const(2), algebra.scale(4, returning)),
        ),
    )
    upper_entry = algebra.add(
        algebra.scale(2, algebra.sub(one, survival)),
        algebra.mul(
            survival,
            algebra.add(algebra.const(2), algebra.scale(4, returning)),
        ),
    )
    assert algebra.sub(upper_entry, exact_entry) == algebra.sub(
        algebra.scale(2, algebra.sub(one, survival)), aggregate
    )
    assert upper_entry == algebra.add(
        algebra.const(2),
        algebra.scale(4, algebra.mul(survival, returning)),
    )

    # Active player 3 at the entering support 9 requires successor value
    # 2+6*entering/(1-entering).  Comparing it with the upper entry value
    # and clearing denominators gives
    #   4S(1-c)C - 6c >= 0.
    required_numerator = algebra.add(
        algebra.scale(2, algebra.sub(one, entering)),
        algebra.scale(6, entering),
    )
    upper_cleared = algebra.mul(
        algebra.sub(one, entering), upper_entry
    )
    growth_numerator = algebra.sub(upper_cleared, required_numerator)
    assert growth_numerator == algebra.sub(
        algebra.scale(
            4,
            algebra.mul(
                survival,
                algebra.mul(algebra.sub(one, entering), returning),
            ),
        ),
        algebra.scale(6, entering),
    )

    # If growth_numerator>=0, then after subtracting the weaker target
    # C>=(3/2)c and clearing the same positive factors, the remaining slack
    # is 6c*((1-S)+S*c), nonnegative and strict for c>0.
    weaker_target = algebra.scale(
        6,
        algebra.mul(
            survival,
            algebra.mul(
                algebra.sub(one, entering), entering
            ),
        ),
    )
    assert algebra.sub(
        algebra.scale(6, entering), weaker_target
    ) == algebra.scale(
        6,
        algebra.mul(
            entering,
            algebra.add(
                algebra.sub(one, survival),
                algebra.mul(survival, entering),
            ),
        ),
    )


def assert_geometric_escape() -> None:
    # If x_{n+1}>(3/2)x_n from some x_0>0, then
    # x_n>(3/2)^n x_0.  The Archimedean property supplies a finite n with
    # the right side >1.  The exact factor is recorded here; no compactness
    # or periodicity assumption is used.
    assert Q(3, 2) > 1


def assert_no_one_sided_strict_support3_9_path() -> None:
    finite_cycles.assert_support_three_player_three_bound()
    assert_support_nine_geometric_growth()
    assert_support_three_geometric_growth()
    assert_support_three_block_growth()
    assert_geometric_escape()


def main() -> None:
    assert_no_one_sided_strict_support3_9_path()

    print("exact one-sided strict support-3/9 exclusion passed")
    print("self blocks and every 9->3+->9 return grow a hazard geometrically")
    print("scope: strict interior; zero-hazard/chattering/atlas exits remain")


if __name__ == "__main__":
    main()
