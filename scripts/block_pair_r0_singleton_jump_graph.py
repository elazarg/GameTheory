#!/usr/bin/env python3
"""Exact transition graph for singleton-support product jumps.

The payoff table is the block-pair table with ``r_0({0})=-2+11/100``.
Suppose a periodic quitting profile uses exactly one positive hazard at every
phase.  Conditional on eventual absorption, let ``mu`` be the distribution of
the identity of the solo quitter.  The continuation value is then the payoff
matrix times ``mu``.  If player ``j`` is active, both endpoints of its jump
lie on the rational hyperplane where player j's continuation payoff equals
its solo payoff.

A phase whose adjacent active identities are different is described by a
triple ``(a,j,k)``: the previous, current, and next active players.  Its future
distribution lies on ``H_j intersect H_k`` and its current distribution lies
on ``H_a intersect H_j``.  Both intersections are rational lines.  The jump
hazard and every inactive Nash inequality reduce to rational functions whose
sign changes only at explicitly enumerated rational points.  This checker
enumerates all such transition domains exactly and prints the resulting graph
on ordered player pairs.

The first graph is the exact finite reduction for singleton-support periodic
profiles with no equal adjacent active identities.  A second, larger graph
handles arbitrary finite same-player runs: after a reciprocal-coordinate
change, the first and last substage conditions are linear, and exact
Fourier--Motzkin projection gives a necessary endpoint envelope.  That
overgraph is also acyclic, so no compatibility claim for intermediate
substage choices is needed.  The checker imports the exact sure-quitter audit
for the hazard-one boundary and separately excludes one-identity cycles.
Zero-hazard phases may be compressed from a terminal-payoff profile; if every
hazard is zero the profile is Never.  Thus the checker excludes every exact
finite-period singleton-support terminal Nash profile.  It says nothing about
phases with several active quitters or nonperiodic paths.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402
from block_pair_r0_singleton_perturbation_fences import (  # noqa: E402
    assert_credible_first_unchanged,
)


Q = Fraction
ZERO = Q(0)
ONE = Q(1)
THETA = Q(11, 100)
Vector = tuple[Fraction, Fraction, Fraction, Fraction]
Affine = tuple[Fraction, Fraction]
Pair = tuple[int, int]


EXPECTED_STRATEGIC_TRIPLES = frozenset(
    {
        (0, 3, 2),
        (1, 0, 2),
        (1, 2, 3),
        (2, 0, 1),
        (3, 1, 0),
        (3, 2, 1),
    }
)
EXPECTED_RUN_ENVELOPE_TRIPLES = frozenset(
    {
        (0, 2, 3),
        (0, 3, 2),
        (1, 0, 2),
        (1, 2, 3),
        (1, 3, 2),
        (2, 0, 1),
        (2, 1, 0),
        (3, 0, 1),
        (3, 1, 0),
        (3, 2, 1),
    }
)


def terminal(mask: int, player: int) -> Fraction:
    value = Q(TERMINAL[mask][player])
    if mask == 1 and player == 0:
        value += THETA
    return value


SOLO: Vector = tuple(terminal(1 << player, player) for player in range(N))  # type: ignore[assignment]
COLUMNS: tuple[Vector, ...] = tuple(
    tuple(terminal(1 << quitter, player) for player in range(N))
    for quitter in range(N)
)  # type: ignore[assignment]
NORMALS: tuple[Vector, ...] = tuple(
    tuple(COLUMNS[quitter][player] - SOLO[player] for quitter in range(N))
    for player in range(N)
)  # type: ignore[assignment]


def dot(left: Vector, right: Vector) -> Fraction:
    return sum((left[index] * right[index] for index in range(N)), ZERO)


def affine_value(value: Affine, parameter: Fraction) -> Fraction:
    return value[0] + value[1] * parameter


def line_intersection(left: int, right: int) -> tuple[Affine, ...]:
    """Parametrize simplex intersect H_left intersect H_right."""

    assert left != right
    matrix = [
        [ONE, ONE, ONE, ONE, ONE],
        [*NORMALS[left], ZERO],
        [*NORMALS[right], ZERO],
    ]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(N):
        selected = next(
            (row for row in range(pivot_row, 3) if matrix[row][column] != 0),
            None,
        )
        if selected is None:
            continue
        matrix[pivot_row], matrix[selected] = matrix[selected], matrix[pivot_row]
        pivot = matrix[pivot_row][column]
        matrix[pivot_row] = [entry / pivot for entry in matrix[pivot_row]]
        for row in range(3):
            if row == pivot_row:
                continue
            coefficient = matrix[row][column]
            if coefficient:
                matrix[row] = [
                    matrix[row][index] - coefficient * matrix[pivot_row][index]
                    for index in range(N + 1)
                ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == 3:
            break
    assert pivot_row == 3
    free_columns = [column for column in range(N) if column not in pivot_columns]
    assert len(free_columns) == 1
    free = free_columns[0]
    result: list[Affine] = [(ZERO, ZERO) for _ in range(N)]
    result[free] = (ZERO, ONE)
    for row, column in enumerate(pivot_columns):
        result[column] = (matrix[row][N], -matrix[row][free])
    return tuple(result)


def probability_interval(line: tuple[Affine, ...]) -> tuple[Fraction, Fraction]:
    lower: Fraction | None = None
    upper: Fraction | None = None
    for constant, slope in line:
        if slope > 0:
            bound = -constant / slope
            lower = bound if lower is None else max(lower, bound)
        elif slope < 0:
            bound = -constant / slope
            upper = bound if upper is None else min(upper, bound)
        else:
            assert constant >= 0
    assert lower is not None and upper is not None and lower <= upper
    return lower, upper


def affine_dot(normal: Vector, line: tuple[Affine, ...]) -> Affine:
    return (
        sum((normal[i] * line[i][0] for i in range(N)), ZERO),
        sum((normal[i] * line[i][1] for i in range(N)), ZERO),
    )


def eliminate_second_variable(
    inequalities: tuple[tuple[Fraction, Fraction, Fraction], ...],
) -> tuple[Affine, ...]:
    """Project ``a*u + b*y + c >= 0`` exactly onto the u-axis."""

    lowers = []
    uppers = []
    projected: list[Affine] = []
    for parameter, variable, constant in inequalities:
        if variable > 0:
            # y >= -(parameter*u+constant)/variable
            lowers.append((parameter, variable, constant))
        elif variable < 0:
            # y <= -(parameter*u+constant)/variable
            uppers.append((parameter, variable, constant))
        else:
            projected.append((constant, parameter))
    assert lowers and uppers
    for lower_parameter, lower_variable, lower_constant in lowers:
        for upper_parameter, upper_variable, upper_constant in uppers:
            # upper - lower >= 0
            projected.append(
                (
                    -upper_constant / upper_variable
                    + lower_constant / lower_variable,
                    -upper_parameter / upper_variable
                    + lower_parameter / lower_variable,
                )
            )
    # Affine uses (constant, slope), while the input convention above uses
    # (u coefficient, eliminated-variable coefficient, constant).
    return tuple(projected)


def affine_feasible_interval(
    inequalities: tuple[Affine, ...],
) -> tuple[Fraction, Fraction] | None:
    """Intersect exact inequalities ``constant+slope*u >= 0``."""

    lower: Fraction | None = None
    upper: Fraction | None = None
    for constant, slope in inequalities:
        if slope > 0:
            bound = -constant / slope
            lower = bound if lower is None else max(lower, bound)
        elif slope < 0:
            bound = -constant / slope
            upper = bound if upper is None else min(upper, bound)
        elif constant < 0:
            return None
    assert lower is not None and upper is not None
    return None if upper < lower else (lower, upper)


def repeated_run_endpoint_interval(
    previous: int, current: int, following: int
) -> tuple[Fraction, Fraction] | None:
    """Necessary u-domain for an arbitrary finite repeated-current run.

    A run follows the segment

        mu(b) = (1-b)e_current + b*mu_plus.

    Put y=1/b.  A stage from future coefficient b to current coefficient a
    satisfies, for inactive player i,

        A_i/a + B_i/b + delta_i >= 0,

    where ``A_i=c_i-pair_i``, ``B_i=pair_i-q_i``, and
    ``delta_i=V_i(mu_plus)-c_i``.  Thus the first and last stages of every
    finite subdivision satisfy two separate rational linear feasibility
    systems.  Projecting their internal y-coordinates gives an exact
    over-approximation in the line parameter u.  It is necessary, not claimed
    sufficient; acyclicity of this larger graph is therefore decisive.
    """

    assert previous != current and current != following
    line = line_intersection(current, following)
    probability_lower, probability_upper = probability_interval(line)
    previous_on_line = affine_dot(NORMALS[previous], line)
    at_vertex = NORMALS[previous][current]
    assert at_vertex != 0

    # Aggregate run survival is lambda=-e/(n_a(mu)-e), hence its inverse
    # Y=1/lambda=1-n_a(mu)/e is affine in u.
    y_total: Affine = (
        ONE - previous_on_line[0] / at_vertex,
        -previous_on_line[1] / at_vertex,
    )

    first_stage: list[tuple[Fraction, Fraction, Fraction]] = [
        (ZERO, ONE, -ONE),  # y >= 1
        (y_total[1], -ONE, y_total[0]),  # y <= Y(u)
    ]
    last_stage: list[tuple[Fraction, Fraction, Fraction]] = [
        (ZERO, ONE, -ONE),
        (y_total[1], -ONE, y_total[0]),
    ]

    for player in range(N):
        if player == current:
            continue
        payoff_on_line = (
            sum(
                COLUMNS[quitter][player] * line[quitter][0]
                for quitter in range(N)
            ),
            sum(
                COLUMNS[quitter][player] * line[quitter][1]
                for quitter in range(N)
            ),
        )
        current_column_payoff = COLUMNS[current][player]
        pair_payoff = terminal((1 << player) | (1 << current), player)
        a_coefficient = current_column_payoff - pair_payoff
        b_coefficient = pair_payoff - SOLO[player]
        delta = (
            payoff_on_line[0] - current_column_payoff,
            payoff_on_line[1],
        )

        # First substage: future reciprocal coefficient is exactly 1;
        # A*y + B + delta(u) >= 0.
        first_stage.append(
            (
                delta[1],
                a_coefficient,
                b_coefficient + delta[0],
            )
        )
        # Last substage: current reciprocal coefficient is Y(u);
        # A*Y(u) + B*x + delta(u) >= 0.
        last_stage.append(
            (
                a_coefficient * y_total[1] + delta[1],
                b_coefficient,
                a_coefficient * y_total[0] + delta[0],
            )
        )

    projected = (
        *eliminate_second_variable(tuple(first_stage)),
        *eliminate_second_variable(tuple(last_stage)),
        (-probability_lower, ONE),
        (probability_upper, -ONE),
        # Y(u) >= 1. Strict inequality is checked below.
        (y_total[0] - ONE, y_total[1]),
    )
    feasible = affine_feasible_interval(projected)
    if feasible is None:
        return None
    lower, upper = feasible
    # A genuine run has positive aggregate hazard, equivalently Y>1.  The
    # projected systems use closed endpoint inequalities as a safe
    # over-approximation, so discard a domain supported only at Y=1.
    maximum_excess = max(
        affine_value((y_total[0] - ONE, y_total[1]), lower),
        affine_value((y_total[0] - ONE, y_total[1]), upper),
    )
    return None if maximum_excess <= 0 else feasible


@dataclass(frozen=True)
class Witness:
    previous: int
    current: int
    following: int
    parameter: Fraction
    hazard: Fraction
    future: Vector
    present: Vector

    @property
    def source(self) -> Pair:
        return self.current, self.following

    @property
    def target(self) -> Pair:
        return self.previous, self.current


def valid_at(
    previous: int,
    current: int,
    following: int,
    line: tuple[Affine, ...],
    parameter: Fraction,
    check_inactive: bool = True,
) -> Witness | None:
    future: Vector = tuple(affine_value(entry, parameter) for entry in line)  # type: ignore[assignment]
    if any(coordinate < 0 for coordinate in future) or sum(future, ZERO) != ONE:
        return None
    assert dot(NORMALS[current], future) == 0
    assert dot(NORMALS[following], future) == 0

    previous_normal = NORMALS[previous]
    at_future = dot(previous_normal, future)
    at_vertex = previous_normal[current]
    denominator = at_future - at_vertex
    if denominator == 0:
        return None
    survival = -at_vertex / denominator
    hazard = ONE - survival
    if not ZERO < hazard < ONE:
        return None
    present: Vector = tuple(  # type: ignore[assignment]
        survival * future[player]
        + hazard * (ONE if player == current else ZERO)
        for player in range(N)
    )
    if any(coordinate < 0 for coordinate in present) or sum(present, ZERO) != ONE:
        return None
    assert dot(NORMALS[previous], present) == 0
    assert dot(NORMALS[current], present) == 0

    if check_inactive:
        for player in range(N):
            if player == current:
                continue
            continuation_value = sum(
                COLUMNS[quitter][player] * future[quitter]
                for quitter in range(N)
            )
            pair_payoff = terminal((1 << player) | (1 << current), player)
            difference = (
                survival * SOLO[player]
                + hazard * pair_payoff
                - hazard * COLUMNS[current][player]
                - survival * continuation_value
            )
            if difference > 0:
                return None
    return Witness(
        previous,
        current,
        following,
        parameter,
        hazard,
        future,
        present,
    )


def triple_witnesses(
    previous: int,
    current: int,
    following: int,
    check_inactive: bool = True,
) -> tuple[Witness, ...]:
    assert previous != current and current != following
    line = line_intersection(current, following)
    lower, upper = probability_interval(line)
    critical = {lower, upper}

    # Every condition has constant sign between these rational roots.  Add
    # roots of simplex coordinates, the jump denominator/boundaries, and each
    # inactive action difference numerator.
    for constant, slope in line:
        if slope:
            root = -constant / slope
            if lower <= root <= upper:
                critical.add(root)
    previous_on_line = affine_dot(NORMALS[previous], line)
    at_vertex = NORMALS[previous][current]
    for constant, slope in (
        previous_on_line,
        (previous_on_line[0] - at_vertex, previous_on_line[1]),
    ):
        if slope:
            root = -constant / slope
            if lower <= root <= upper:
                critical.add(root)

    # Derive inactive difference numerator after substituting
    # survival=-n_a(e_j)/(n_a(mu)-n_a(e_j)).  Direct interpolation at two
    # rational parameter values reconstructs its affine numerator safely.
    def inactive_numerator(player: int, parameter: Fraction) -> Fraction:
        future: Vector = tuple(  # type: ignore[assignment]
            affine_value(entry, parameter) for entry in line
        )
        na_mu = dot(NORMALS[previous], future)
        e = NORMALS[previous][current]
        pair_gap = (
            terminal((1 << player) | (1 << current), player)
            - COLUMNS[current][player]
        )
        # Difference times the common denominator L=na_mu-e.
        return e * dot(NORMALS[player], future) + na_mu * pair_gap

    for player in range(N):
        if player == current:
            continue
        value_zero = inactive_numerator(player, ZERO)
        value_one = inactive_numerator(player, ONE)
        slope = value_one - value_zero
        if slope:
            root = -value_zero / slope
            if lower <= root <= upper:
                critical.add(root)

    ordered = sorted(critical)
    samples = set(ordered)
    samples.update(
        (left + right) / 2 for left, right in zip(ordered, ordered[1:])
    )
    witnesses = tuple(
        witness
        for parameter in sorted(samples)
        if (witness := valid_at(
            previous,
            current,
            following,
            line,
            parameter,
            check_inactive=check_inactive,
        )) is not None
    )
    return witnesses


def strongly_connected_components(
    vertices: tuple[Pair, ...], edges: set[tuple[Pair, Pair]]
) -> tuple[tuple[Pair, ...], ...]:
    adjacency = {
        vertex: tuple(target for source, target in edges if source == vertex)
        for vertex in vertices
    }
    reverse = {
        vertex: tuple(source for source, target in edges if target == vertex)
        for vertex in vertices
    }
    seen: set[Pair] = set()
    order: list[Pair] = []

    def visit(vertex: Pair) -> None:
        if vertex in seen:
            return
        seen.add(vertex)
        for target in adjacency[vertex]:
            visit(target)
        order.append(vertex)

    for vertex in vertices:
        visit(vertex)
    seen.clear()
    components: list[tuple[Pair, ...]] = []

    def collect(vertex: Pair, component: list[Pair]) -> None:
        if vertex in seen:
            return
        seen.add(vertex)
        component.append(vertex)
        for source in reverse[vertex]:
            collect(source, component)

    for vertex in reversed(order):
        if vertex not in seen:
            component: list[Pair] = []
            collect(vertex, component)
            components.append(tuple(sorted(component)))
    return tuple(components)


def main() -> None:
    assert N == 4
    vertices = tuple(
        (left, right)
        for left in range(N)
        for right in range(N)
        if left != right
    )
    witnesses: dict[tuple[int, int, int], tuple[Witness, ...]] = {}
    edges: set[tuple[Pair, Pair]] = set()
    for previous in range(N):
        for current in range(N):
            for following in range(N):
                if previous == current or current == following:
                    continue
                found = triple_witnesses(previous, current, following)
                if found:
                    witnesses[(previous, current, following)] = found
                    edges.add((found[0].source, found[0].target))

    components = strongly_connected_components(vertices, edges)
    cyclic = tuple(component for component in components if len(component) > 1)
    assert frozenset(witnesses) == EXPECTED_STRATEGIC_TRIPLES
    assert len(edges) == len(EXPECTED_STRATEGIC_TRIPLES) == 6
    assert not cyclic

    # A maximal run of one singleton mode has the same geometric endpoint
    # relation as a single jump, but its stagewise inactive inequalities do
    # not automatically collapse to the aggregate inequality above.  The
    # inactive-free graph is therefore the honest necessary envelope for
    # arbitrary repeated runs.
    geometric_edges: set[tuple[Pair, Pair]] = set()
    for previous in range(N):
        for current in range(N):
            for following in range(N):
                if previous == current or current == following:
                    continue
                found = triple_witnesses(
                    previous,
                    current,
                    following,
                    check_inactive=False,
                )
                if found:
                    geometric_edges.add((found[0].source, found[0].target))
    geometric_components = strongly_connected_components(vertices, geometric_edges)
    geometric_cyclic = tuple(
        component for component in geometric_components if len(component) > 1
    )
    assert len(geometric_edges) == 24
    assert geometric_cyclic == (tuple(sorted(vertices)),)

    # Exact necessary endpoint envelope for arbitrary finite subdivisions of
    # a maximal repeated-player run.  Because it forgets compatibility of the
    # intermediate substages, this graph contains every genuine run edge and
    # may contain false positives.  Its acyclicity is therefore enough.
    run_intervals: dict[
        tuple[int, int, int], tuple[Fraction, Fraction]
    ] = {}
    run_edges: set[tuple[Pair, Pair]] = set()
    for previous in range(N):
        for current in range(N):
            for following in range(N):
                if previous == current or current == following:
                    continue
                interval = repeated_run_endpoint_interval(
                    previous, current, following
                )
                if interval is not None:
                    run_intervals[(previous, current, following)] = interval
                    run_edges.add(((current, following), (previous, current)))
    run_components = strongly_connected_components(vertices, run_edges)
    run_cyclic = tuple(
        component for component in run_components if len(component) > 1
    )
    assert frozenset(run_intervals) == EXPECTED_RUN_ENVELOPE_TRIPLES
    assert len(run_edges) == len(EXPECTED_RUN_ENVELOPE_TRIPLES) == 10
    assert not run_cyclic

    # A hazard-one phase is outside the finite reciprocal-coordinate chart.
    # The exact perturbed sure-face audit proves that every such local root
    # gives its designated sure quitter a continuation deviation of at least
    # 13/15, independently of a periodic tail.
    assert_credible_first_unchanged()
    print("exact singleton-jump transition graph generated")
    print(f"vertices = {len(vertices)}")
    print(f"feasible triples = {len(witnesses)}")
    print(f"directed edges = {len(edges)}")
    for triple, found in sorted(witnesses.items()):
        witness = found[0]
        print(
            f"  {triple}: parameter={witness.parameter}; "
            f"hazard={witness.hazard}; {witness.source}->{witness.target}"
        )
    print(f"strongly connected components = {components}")
    print(f"nontrivial strongly connected components = {cyclic}")
    if not cyclic:
        print("the reduced singleton-support transition graph is acyclic")
    else:
        print("graph cycles remain; fractional-map compatibility is unresolved")
    print(f"geometric run-envelope edges = {len(geometric_edges)}")
    print(f"geometric run-envelope nontrivial SCCs = {geometric_cyclic}")
    if not geometric_cyclic:
        print("the arbitrary-run geometric envelope is also acyclic")
    else:
        print("repeated-run geometry leaves cycles; stagewise analysis is needed")
    print("finite repeated-run necessary endpoint intervals:")
    for triple, interval in sorted(run_intervals.items()):
        print(f"  {triple}: [{interval[0]},{interval[1]}]")
    print(f"finite repeated-run envelope edges = {len(run_edges)}")
    print(f"finite repeated-run envelope SCCs = {run_components}")
    print("the finite repeated-run necessary envelope is acyclic")
    print("hazard-one faces excluded by exact credible-First gap >= 13/15")

    # A periodic singleton profile using just one identity absorbs at that
    # player's solo outcome.  Player 0 rejects its negative solo reward in
    # favor of Never.  For players 1--3 the displayed inactive player has a
    # strictly profitable immediate quit at every own hazard h in [0,1].
    assert SOLO[0] == Q(-189, 100) < 0
    assert SOLO[1:] == (Q(2), Q(2), Q(2))
    same_mode_witnesses = {
        1: (2, Q(2), Q(4)),
        2: (0, Q(211, 100), Q(189, 100)),
        3: (1, Q(2), Q(4)),
    }
    for quitter, (deviator, intercept, slope) in same_mode_witnesses.items():
        column = COLUMNS[quitter][deviator]
        pair = terminal((1 << quitter) | (1 << deviator), deviator)
        assert SOLO[deviator] - column == intercept
        assert pair - SOLO[deviator] == slope
        assert intercept > 0 and intercept + slope > 0
    print("same-identity singleton cycles are excluded exactly")
    print(
        "zero-hazard phases compress harmlessly; the all-zero profile is Never"
    )
    print(
        "conclusion: no finite periodic singleton-support terminal Nash path"
    )
    print("scope left open: multi-active phases and nonperiodic product jumps")


if __name__ == "__main__":
    main()
