#!/usr/bin/env python3
"""Exact interval certificate for the block-pair period-eleven lasso.

The candidate has public support word

    [7, 7, 14, 14, 11, 11, 9, 9, 13, 13, 7].

There are 31 positive quitting probabilities.  For a sparse polynomial
system we retain the 44 phase/player continuation values as independent
variables.  The 75 equations are:

* 44 cyclic prescribed-payoff recurrences; and
* 31 Quit = Continue equations, one at every active phase/player slot.

The decimal inverse used to precondition the system is only witness
generation.  After it is rounded to rational entries, every Krawczyk bound,
inactive-action inequality, support bound, and contraction check is performed
with ``Fraction`` interval arithmetic.  Thus successful assertions are an
exact certificate; no floating-point result is trusted.

This script proves existence and local uniqueness of an exact zero in the
displayed rational box.  It does not identify the zero as rational.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_stationary_certificate import N, TERMINAL  # noqa: E402


assert N == 4
PERIOD = 11
SUPPORT_WORD = (7, 7, 14, 14, 11, 11, 9, 9, 13, 13, 7)


ROOT_CENTER_TEXT = (
    ("0.070773162508252468", "0.060498957062486383", "0.17873702678622647", "0"),
    ("0.0087055416348124064", "0.10205549180212524", "0.36082370743567099", "0"),
    ("0", "0.16846473882967991", "0.065098107693290316", "0.0097030523813587503"),
    ("0", "0.28149267717706911", "0.097545468121530698", "0.070330324639908015"),
    ("0.002056179806325659", "0.060825485291417368", "0", "0.11501844773867245"),
    ("0.035699881913465702", "0.0089701731507570524", "0", "0.21708955986796688"),
    ("0.060225550649685898", "0", "0", "0.16277294054551064"),
    ("0.096127667694074562", "0", "0", "0.097209555464898692"),
    ("0.17272500809879718", "0", "0.050942654221662664", "0.076391038430525665"),
    ("0.25317128934533362", "0", "0.024484008004623317", "0.0086400718059171568"),
    ("0.053441876508934921", "0.013002213795957967", "0.061305680651160738", "0"),
)


VALUE_CENTER_TEXT = (
    ("-1.8564630287420554", "1.4808055974747236", "2.0790409906346237", "3.9553061900765063"),
    ("-1.6949911832836746", "1.2648006234558551", "2.3863686422741521", "3.7932523245099743"),
    ("-0.70067714723242014", "1.9060893927433531", "2.6819273855148018", "1.978066528578287"),
    ("-1.3004855873019436", "2.0587887445560131", "3.1765035619785635", "1.9450833300639594"),
    ("-2.6355541939277707", "2.453905251535712", "4.1205815340367904", "2.007974582956169"),
    ("-2.8933214279829018", "2.7612585937314704", "3.9185126272420776", "2.142159059409412"),
    ("-2.651091762182042", "3.330517906761191", "2.9654556695407162", "2.2409022025987433"),
    ("-2.3888382218595954", "3.6829080001983567", "2.1513364534560071", "2.3845106707762982"),
    ("-2.2153535320479767", "3.6281651902725423", "1.7177463795013432", "2.638105610217123"),
    ("-1.9862269019761916", "3.2391432036164303", "1.5001100749961096", "2.9754932701321022"),
    ("-1.9187866087857524", "1.7301681716294959", "1.9416507886458307", "3.9174127092605691"),
)


ACTIVE_SLOTS = tuple(
    (phase, player)
    for phase, support in enumerate(SUPPORT_WORD)
    for player in range(N)
    if (support >> player) & 1
)
HAZARD_COUNT = len(ACTIVE_SLOTS)
VALUE_COUNT = PERIOD * N
DIMENSION = HAZARD_COUNT + VALUE_COUNT
assert HAZARD_COUNT == 31
assert DIMENSION == 75

HAZARD_INDEX = {slot: index for index, slot in enumerate(ACTIVE_SLOTS)}


def q(text: str) -> Fraction:
    return Fraction(text)


ROOT_CENTER = tuple(tuple(q(value) for value in row) for row in ROOT_CENTER_TEXT)
VALUE_CENTER = tuple(tuple(q(value) for value in row) for row in VALUE_CENTER_TEXT)
CENTER = tuple(ROOT_CENTER[phase][player] for phase, player in ACTIVE_SLOTS) + tuple(
    VALUE_CENTER[phase][player]
    for phase in range(PERIOD)
    for player in range(N)
)
assert len(CENTER) == DIMENSION


@dataclass(frozen=True)
class Interval:
    low: Fraction
    high: Fraction

    def __post_init__(self) -> None:
        assert self.low <= self.high

    @staticmethod
    def point(value: Fraction | int) -> "Interval":
        value = Fraction(value)
        return Interval(value, value)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self) -> "Interval":
        return Interval(-self.high, -self.low)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.low * other.low,
            self.low * other.high,
            self.high * other.low,
            self.high * other.high,
        )
        return Interval(min(products), max(products))

    def scale(self, scalar: Fraction | int) -> "Interval":
        scalar = Fraction(scalar)
        if scalar >= 0:
            return Interval(scalar * self.low, scalar * self.high)
        return Interval(scalar * self.high, scalar * self.low)

    def abs_upper(self) -> Fraction:
        return max(abs(self.low), abs(self.high))

    def is_zero(self) -> bool:
        return self.low == 0 and self.high == 0


ZERO = Interval.point(0)
ONE = Interval.point(1)


def interval_sum(values: list[Interval] | tuple[Interval, ...]) -> Interval:
    result = ZERO
    for value in values:
        result = result + value
    return result


def interval_product(values: list[Interval] | tuple[Interval, ...]) -> Interval:
    result = ONE
    for value in values:
        result = result * value
    return result


def bit(mask: int, player: int) -> int:
    return (mask >> player) & 1


def probability(
    root: tuple[Interval, ...], mask: int, omitted: int | None = None
) -> Interval:
    factors = []
    for player in range(N):
        if player == omitted:
            continue
        factors.append(root[player] if bit(mask, player) else ONE - root[player])
    return interval_product(factors)


def probability_derivative(
    root: tuple[Interval, ...],
    mask: int,
    variable: int,
    omitted: int | None = None,
) -> Interval:
    if variable == omitted:
        return ZERO
    factors = []
    for player in range(N):
        if player == omitted or player == variable:
            continue
        factors.append(root[player] if bit(mask, player) else ONE - root[player])
    sign = 1 if bit(mask, variable) else -1
    return interval_product(factors).scale(sign)


@dataclass(frozen=True)
class PhaseData:
    immediate: tuple[Interval, ...]
    survival: Interval
    immediate_derivative: tuple[tuple[Interval, ...], ...]
    survival_derivative: tuple[Interval, ...]


def phase_data(root: tuple[Interval, ...]) -> PhaseData:
    immediate = [ZERO for _ in range(N)]
    derivatives = [[ZERO for _ in range(N)] for _ in range(N)]
    for mask in range(1, 1 << N):
        mass = probability(root, mask)
        for player in range(N):
            immediate[player] = immediate[player] + mass.scale(TERMINAL[mask][player])
        for variable in range(N):
            derivative = probability_derivative(root, mask, variable)
            for player in range(N):
                derivatives[player][variable] = (
                    derivatives[player][variable]
                    + derivative.scale(TERMINAL[mask][player])
                )
    survival = probability(root, 0)
    survival_derivative = tuple(
        probability_derivative(root, 0, variable) for variable in range(N)
    )
    return PhaseData(
        tuple(immediate),
        survival,
        tuple(tuple(row) for row in derivatives),
        survival_derivative,
    )


@dataclass(frozen=True)
class OpponentData:
    quit_value: Interval
    absorption: Interval
    survival: Interval
    quit_derivative: tuple[Interval, ...]
    absorption_derivative: tuple[Interval, ...]
    survival_derivative: tuple[Interval, ...]


def opponent_data(root: tuple[Interval, ...], who: int) -> OpponentData:
    quit_value = ZERO
    absorption = ZERO
    quit_derivative = [ZERO for _ in range(N)]
    absorption_derivative = [ZERO for _ in range(N)]
    for opponent_mask in range(1 << N):
        if bit(opponent_mask, who):
            continue
        mass = probability(root, opponent_mask, omitted=who)
        quit_value = quit_value + mass.scale(
            TERMINAL[opponent_mask | (1 << who)][who]
        )
        if opponent_mask:
            absorption = absorption + mass.scale(TERMINAL[opponent_mask][who])
        for variable in range(N):
            derivative = probability_derivative(
                root, opponent_mask, variable, omitted=who
            )
            quit_derivative[variable] = quit_derivative[variable] + derivative.scale(
                TERMINAL[opponent_mask | (1 << who)][who]
            )
            if opponent_mask:
                absorption_derivative[variable] = (
                    absorption_derivative[variable]
                    + derivative.scale(TERMINAL[opponent_mask][who])
                )
    survival = probability(root, 0, omitted=who)
    survival_derivative = tuple(
        probability_derivative(root, 0, variable, omitted=who)
        for variable in range(N)
    )
    return OpponentData(
        quit_value,
        absorption,
        survival,
        tuple(quit_derivative),
        tuple(absorption_derivative),
        survival_derivative,
    )


def value_variable_index(phase: int, player: int) -> int:
    return HAZARD_COUNT + N * phase + player


def unpack_box(
    box: tuple[Interval, ...],
) -> tuple[tuple[tuple[Interval, ...], ...], tuple[tuple[Interval, ...], ...]]:
    roots = []
    for phase, support in enumerate(SUPPORT_WORD):
        row = []
        for player in range(N):
            if bit(support, player):
                row.append(box[HAZARD_INDEX[(phase, player)]])
            else:
                row.append(ZERO)
        roots.append(tuple(row))
    values = tuple(
        tuple(box[value_variable_index(phase, player)] for player in range(N))
        for phase in range(PERIOD)
    )
    return tuple(roots), values


SparseRow = dict[int, Interval]


def add_entry(row: SparseRow, column: int, value: Interval) -> None:
    row[column] = row.get(column, ZERO) + value
    if row[column].is_zero():
        del row[column]


def system_and_jacobian(
    box: tuple[Interval, ...],
) -> tuple[tuple[Interval, ...], tuple[SparseRow, ...]]:
    roots, values = unpack_box(box)
    phases = tuple(phase_data(root) for root in roots)
    equations: list[Interval] = []
    jacobian: list[SparseRow] = []

    # Prescribed-value recurrences.
    for phase in range(PERIOD):
        successor = (phase + 1) % PERIOD
        data = phases[phase]
        for player in range(N):
            equations.append(
                values[phase][player]
                - data.immediate[player]
                - data.survival * values[successor][player]
            )
            row: SparseRow = {}
            add_entry(row, value_variable_index(phase, player), ONE)
            add_entry(
                row,
                value_variable_index(successor, player),
                -data.survival,
            )
            for variable in range(N):
                slot = (phase, variable)
                if slot not in HAZARD_INDEX:
                    continue
                derivative = (
                    -data.immediate_derivative[player][variable]
                    - data.survival_derivative[variable]
                    * values[successor][player]
                )
                add_entry(row, HAZARD_INDEX[slot], derivative)
            jacobian.append(row)

    # Active Quit = Continue equations.
    for phase, player in ACTIVE_SLOTS:
        successor = (phase + 1) % PERIOD
        data = opponent_data(roots[phase], player)
        equations.append(
            data.quit_value
            - data.absorption
            - data.survival * values[successor][player]
        )
        row = {}
        add_entry(
            row,
            value_variable_index(successor, player),
            -data.survival,
        )
        for variable in range(N):
            slot = (phase, variable)
            if slot not in HAZARD_INDEX:
                continue
            derivative = (
                data.quit_derivative[variable]
                - data.absorption_derivative[variable]
                - data.survival_derivative[variable]
                * values[successor][player]
            )
            add_entry(row, HAZARD_INDEX[slot], derivative)
        jacobian.append(row)

    assert len(equations) == len(jacobian) == DIMENSION
    return tuple(equations), tuple(jacobian)


def point_box(values: tuple[Fraction, ...]) -> tuple[Interval, ...]:
    return tuple(Interval.point(value) for value in values)


def rational_preconditioner(point_jacobian: tuple[SparseRow, ...]) -> list[list[Fraction]]:
    """Generate a rational approximate inverse using only Decimal arithmetic.

    Decimal elimination is not trusted as a proof step: its output is rounded
    to exact ``Fraction`` entries and the Krawczyk assertions below validate
    that rational matrix from scratch.
    """
    rational_matrix = [
        [Fraction(0) for _ in range(DIMENSION)] for _ in range(DIMENSION)
    ]
    for row_index, row in enumerate(point_jacobian):
        for column, value in row.items():
            assert value.low == value.high
            rational_matrix[row_index][column] = value.low

    with localcontext() as context:
        context.prec = 50

        def decimal(value: Fraction) -> Decimal:
            return Decimal(value.numerator) / Decimal(value.denominator)

        augmented = []
        for row in range(DIMENSION):
            augmented.append(
                [decimal(value) for value in rational_matrix[row]]
                + [Decimal(1 if row == column else 0) for column in range(DIMENSION)]
            )

        for column in range(DIMENSION):
            pivot = max(
                range(column, DIMENSION),
                key=lambda row: abs(augmented[row][column]),
            )
            assert augmented[pivot][column] != 0
            augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
            pivot_value = augmented[column][column]
            augmented[column] = [value / pivot_value for value in augmented[column]]
            for row in range(DIMENSION):
                if row == column:
                    continue
                multiplier = augmented[row][column]
                if multiplier == 0:
                    continue
                augmented[row] = [
                    value - multiplier * pivot_entry
                    for value, pivot_entry in zip(augmented[row], augmented[column])
                ]

        inverse_decimal = [row[DIMENSION:] for row in augmented]

    # Decimal values are converted to exact decimal rationals.  The subsequent
    # interval validation, not the approximate elimination, proves the claim.
    return [
        [Fraction(str(value)) for value in row]
        for row in inverse_decimal
    ]


def krawczyk_bounds(
    equations_at_center: tuple[Interval, ...],
    jacobian_on_box: tuple[SparseRow, ...],
    preconditioner: list[list[Fraction]],
    radius: Fraction,
) -> tuple[Fraction, Fraction, tuple[Fraction, ...]]:
    residual = []
    for equation in equations_at_center:
        assert equation.low == equation.high
        residual.append(equation.low)

    correction = []
    for output in range(DIMENSION):
        correction.append(
            sum(
                (preconditioner[output][row] * residual[row]
                 for row in range(DIMENSION)),
                Fraction(0),
            )
        )

    # B = I - A J(X), represented by interval entries.  Exploit the sparse
    # rows of J rather than multiplying two dense 75-by-75 matrices.
    defect = [
        [Interval.point(1 if row == column else 0) for column in range(DIMENSION)]
        for row in range(DIMENSION)
    ]
    for equation_row, sparse_row in enumerate(jacobian_on_box):
        for column, jacobian_entry in sparse_row.items():
            for output in range(DIMENSION):
                coefficient = preconditioner[output][equation_row]
                if coefficient:
                    defect[output][column] = (
                        defect[output][column]
                        - jacobian_entry.scale(coefficient)
                    )

    row_sums = tuple(
        sum((entry.abs_upper() for entry in row), Fraction(0))
        for row in defect
    )
    inclusion_ratios = tuple(
        (abs(correction[index]) + row_sums[index] * radius) / radius
        for index in range(DIMENSION)
    )
    return max(row_sums), max(inclusion_ratios), inclusion_ratios


def assert_strategic_inequalities(box: tuple[Interval, ...]) -> tuple[Fraction, Fraction]:
    roots, values = unpack_box(box)
    for phase, player in ACTIVE_SLOTS:
        hazard = roots[phase][player]
        assert 0 < hazard.low < hazard.high < 1

    inactive_upper = None
    for phase, support in enumerate(SUPPORT_WORD):
        successor = (phase + 1) % PERIOD
        for player in range(N):
            if bit(support, player):
                continue
            data = opponent_data(roots[phase], player)
            difference = (
                data.quit_value
                - data.absorption
                - data.survival * values[successor][player]
            )
            assert difference.high < 0
            if inactive_upper is None or difference.high > inactive_upper:
                inactive_upper = difference.high

    opponent_cycle_upper = Fraction(0)
    for player in range(N):
        cycle = interval_product(
            tuple(opponent_data(roots[phase], player).survival for phase in range(PERIOD))
        )
        assert 0 <= cycle.low <= cycle.high < 1
        opponent_cycle_upper = max(opponent_cycle_upper, cycle.high)

    joint_cycle = interval_product(
        tuple(phase_data(roots[phase]).survival for phase in range(PERIOD))
    )
    assert 0 <= joint_cycle.low <= joint_cycle.high < 1
    assert inactive_upper is not None
    return inactive_upper, opponent_cycle_upper


def main() -> None:
    radius = Fraction(1, 10**8)
    center_box = point_box(CENTER)
    equations_at_center, point_jacobian = system_and_jacobian(center_box)
    preconditioner = rational_preconditioner(point_jacobian)

    box = tuple(Interval(value - radius, value + radius) for value in CENTER)
    _, jacobian_on_box = system_and_jacobian(box)
    maximum_defect_row_sum, maximum_inclusion_ratio, _ = krawczyk_bounds(
        equations_at_center,
        jacobian_on_box,
        preconditioner,
        radius,
    )

    # ||I-AJ(X)||_infinity < 1 proves regularity throughout the box.  Strict
    # Krawczyk inclusion proves existence and uniqueness of the exact root.
    assert maximum_defect_row_sum < 1
    assert maximum_inclusion_ratio < 1

    inactive_upper, opponent_cycle_upper = assert_strategic_inequalities(box)

    maximum_center_residual = max(
        equation.abs_upper() for equation in equations_at_center
    )
    print("exact period-eleven Krawczyk certificate passed")
    print(f"dimension = {DIMENSION}")
    print(f"box radius = {radius}")
    print(f"maximum center residual ~= {float(maximum_center_residual):.3e}")
    print(f"maximum ||I-AJ(X)|| row sum ~= {float(maximum_defect_row_sum):.3e}")
    print(f"maximum Krawczyk inclusion ratio ~= {float(maximum_inclusion_ratio):.3e}")
    print(f"largest inactive Quit-minus-Continue upper bound ~= {float(inactive_upper):.6f}")
    print(f"largest opponent-cycle survival upper bound ~= {float(opponent_cycle_upper):.6f}")


if __name__ == "__main__":
    main()
