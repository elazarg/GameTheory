#!/usr/bin/env python3
"""Exact interval certificates for the block-pair period-eleven lasso.

The original lasso has public support word

    [7, 7, 14, 14, 11, 11, 9, 9, 13, 13, 7].

There are 31 positive quitting probabilities.  The first, sparse polynomial
system retains the 44 phase/player continuation values as independent
variables.  Its 75 equations are:

* 44 cyclic prescribed-payoff recurrences; and
* 31 Quit = Continue equations, one at every active phase/player slot.

The second system eliminates the 44 values through the exact cyclic payoff
formula.  After multiplying by the positive joint-cycle denominator, it has
31 polynomial active-indifference equations in the 31 hazards.  Both systems
are certified independently; the original 75-variable system remains a
regression for the elimination and phase orientation.

A second exact reduced certificate changes phase 4 from mask 11 to mask 14.
It is a regression against accidental rigidity of the original support word;
the larger 75-variable formulation is retained only for the original word.

Pass ``--export-reduced-preconditioner`` to emit the validated 31-by-31
rational preconditioner, center, radius, game data, and variable order as
canonical JSON with a SHA-256 fingerprint.  Export still runs both exact
certificates before producing the document.

The decimal inverse used to precondition the system is only witness
generation.  After it is rounded to rational entries, every Krawczyk bound,
inactive-action inequality, support bound, and contraction check is performed
with ``Fraction`` interval arithmetic.  Thus successful assertions are an
exact certificate; no floating-point result is trusted.

This script proves existence and local uniqueness of an exact zero in the two
respective rational boxes.  It does not identify the zero as rational.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from decimal import Decimal, ROUND_HALF_EVEN, localcontext
from fractions import Fraction
from functools import partial
from hashlib import sha256
import json
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


NEARBY_SUPPORT_WORD = (7, 7, 14, 14, 14, 11, 9, 9, 13, 13, 7)
NEARBY_ROOT_CENTER_TEXT = (
    ("0.069263688386350233", "0.042818792380861101", "0.16785488622016514", "0"),
    ("0.0073968227716418823", "0.071460526463632268", "0.35150324309338782", "0"),
    ("0", "0.11506801598053953", "0.042813136089758577", "0.0016823518187853101"),
    ("0", "0.18503939024551086", "0.06959555844283967", "0.040117563823091326"),
    ("0", "0.27991920884450561", "0.081548119792186888", "0.11265198855786279"),
    ("0.035491215162116951", "0.010932669515614597", "0", "0.21704875060474529"),
    ("0.060925914446962146", "0", "0", "0.16807613271724231"),
    ("0.097318063693156445", "0", "0", "0.10101653488210106"),
    ("0.17476560341503711", "0", "0.049783745458097432", "0.078157402326823805"),
    ("0.26178340367149361", "0", "0.02956800509028978", "0.013371405443325707"),
    ("0.051468536661102619", "0.0029775834003244496", "0.050425054590815838", "0"),
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
REDUCED_PRECONDITIONER_PRECISION = 16

HAZARD_INDEX = {slot: index for index, slot in enumerate(ACTIVE_SLOTS)}


def q(text: str) -> Fraction:
    return Fraction(text)


@dataclass(frozen=True)
class ReducedCertificateData:
    name: str
    support_word: tuple[int, ...]
    root_center: tuple[tuple[Fraction, ...], ...]
    active_slots: tuple[tuple[int, int], ...]
    hazard_index: dict[tuple[int, int], int]
    hazard_center: tuple[Fraction, ...]


def make_reduced_certificate_data(
    name: str,
    support_word: tuple[int, ...],
    root_center_text: tuple[tuple[str, ...], ...],
) -> ReducedCertificateData:
    assert len(support_word) == len(root_center_text) == PERIOD
    root_center = tuple(
        tuple(q(value) for value in row) for row in root_center_text
    )
    assert all(len(row) == N for row in root_center)
    active_slots = tuple(
        (phase, player)
        for phase, support in enumerate(support_word)
        for player in range(N)
        if (support >> player) & 1
    )
    hazard_index = {
        slot: index for index, slot in enumerate(active_slots)
    }
    hazard_center = tuple(
        root_center[phase][player] for phase, player in active_slots
    )
    for phase, support in enumerate(support_word):
        for player in range(N):
            value = root_center[phase][player]
            if (support >> player) & 1:
                assert 0 < value < 1
            else:
                assert value == 0
    assert len(active_slots) == 31
    return ReducedCertificateData(
        name,
        support_word,
        root_center,
        active_slots,
        hazard_index,
        hazard_center,
    )


ROOT_CENTER = tuple(tuple(q(value) for value in row) for row in ROOT_CENTER_TEXT)
VALUE_CENTER = tuple(tuple(q(value) for value in row) for row in VALUE_CENTER_TEXT)
HAZARD_CENTER = tuple(
    ROOT_CENTER[phase][player] for phase, player in ACTIVE_SLOTS
)
CENTER = HAZARD_CENTER + tuple(
    VALUE_CENTER[phase][player]
    for phase in range(PERIOD)
    for player in range(N)
)
assert len(CENTER) == DIMENSION

BASE_REDUCED_CERTIFICATE = make_reduced_certificate_data(
    "base", SUPPORT_WORD, ROOT_CENTER_TEXT
)
NEARBY_REDUCED_CERTIFICATE = make_reduced_certificate_data(
    "phase4-mask11-to-mask14", NEARBY_SUPPORT_WORD, NEARBY_ROOT_CENTER_TEXT
)
assert BASE_REDUCED_CERTIFICATE.active_slots == ACTIVE_SLOTS
assert BASE_REDUCED_CERTIFICATE.hazard_index == HAZARD_INDEX
assert BASE_REDUCED_CERTIFICATE.hazard_center == HAZARD_CENTER


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


def positive_reciprocal(value: Interval) -> Interval:
    assert 0 < value.low <= value.high
    return Interval(Fraction(1) / value.high, Fraction(1) / value.low)


@dataclass(frozen=True)
class IntervalDual:
    """An interval value with an exact interval enclosure of its gradient."""

    value: Interval
    derivative: tuple[Interval, ...]

    @staticmethod
    def constant(value: Fraction | int, dimension: int) -> "IntervalDual":
        return IntervalDual(
            Interval.point(value), tuple(ZERO for _ in range(dimension))
        )

    def __add__(self, other: "IntervalDual") -> "IntervalDual":
        assert len(self.derivative) == len(other.derivative)
        return IntervalDual(
            self.value + other.value,
            tuple(
                left + right
                for left, right in zip(self.derivative, other.derivative)
            ),
        )

    def __neg__(self) -> "IntervalDual":
        return IntervalDual(
            -self.value, tuple(-entry for entry in self.derivative)
        )

    def __sub__(self, other: "IntervalDual") -> "IntervalDual":
        return self + (-other)

    def __mul__(self, other: "IntervalDual") -> "IntervalDual":
        assert len(self.derivative) == len(other.derivative)
        return IntervalDual(
            self.value * other.value,
            tuple(
                left * other.value + self.value * right
                for left, right in zip(self.derivative, other.derivative)
            ),
        )

    def scale(self, scalar: Fraction | int) -> "IntervalDual":
        return IntervalDual(
            self.value.scale(scalar),
            tuple(entry.scale(scalar) for entry in self.derivative),
        )


def dual_product(
    values: list[IntervalDual] | tuple[IntervalDual, ...], dimension: int
) -> IntervalDual:
    result = IntervalDual.constant(1, dimension)
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


def unpack_hazard_box(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[tuple[Interval, ...], ...]:
    assert len(box) == len(certificate.active_slots)
    roots = []
    for phase, support in enumerate(certificate.support_word):
        row = []
        for player in range(N):
            if bit(support, player):
                row.append(box[certificate.hazard_index[(phase, player)]])
            else:
                row.append(ZERO)
        roots.append(tuple(row))
    return tuple(roots)


def unpack_box(
    box: tuple[Interval, ...],
) -> tuple[tuple[tuple[Interval, ...], ...], tuple[tuple[Interval, ...], ...]]:
    assert len(box) == DIMENSION
    roots = unpack_hazard_box(box[:HAZARD_COUNT], BASE_REDUCED_CERTIFICATE)
    values = tuple(
        tuple(box[value_variable_index(phase, player)] for player in range(N))
        for phase in range(PERIOD)
    )
    return roots, values


SparseRow = dict[int, Interval]
SystemEvaluator = Callable[
    [tuple[Interval, ...]],
    tuple[tuple[Interval, ...], tuple[SparseRow, ...]],
]


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


def unpack_dual_hazard_box(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[tuple[IntervalDual, ...], ...]:
    dimension = len(certificate.active_slots)
    assert len(box) == dimension
    roots = []
    for phase, support in enumerate(certificate.support_word):
        row = []
        for player in range(N):
            slot = (phase, player)
            if bit(support, player):
                index = certificate.hazard_index[slot]
                derivative = [ZERO for _ in range(dimension)]
                derivative[index] = ONE
                row.append(IntervalDual(box[index], tuple(derivative)))
            else:
                row.append(IntervalDual.constant(0, dimension))
        roots.append(tuple(row))
    return tuple(roots)


def dual_probability(
    root: tuple[IntervalDual, ...], mask: int, omitted: int | None = None
) -> IntervalDual:
    dimension = len(root[0].derivative)
    one = IntervalDual.constant(1, dimension)
    factors = []
    for player in range(N):
        if player == omitted:
            continue
        factors.append(root[player] if bit(mask, player) else one - root[player])
    return dual_product(factors, dimension)


@dataclass(frozen=True)
class ReducedCycleData:
    roots: tuple[tuple[IntervalDual, ...], ...]
    immediate: tuple[tuple[IntervalDual, ...], ...]
    survival: tuple[IntervalDual, ...]
    joint_survival: IntervalDual
    numerator: tuple[tuple[IntervalDual, ...], ...]


def reduced_cycle_data(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> ReducedCycleData:
    dimension = len(certificate.active_slots)
    roots = unpack_dual_hazard_box(box, certificate)
    immediate = []
    survival = []
    for root in roots:
        phase_immediate = [
            IntervalDual.constant(0, dimension) for _ in range(N)
        ]
        for mask in range(1, 1 << N):
            mass = dual_probability(root, mask)
            for player in range(N):
                phase_immediate[player] = (
                    phase_immediate[player]
                    + mass.scale(TERMINAL[mask][player])
                )
        immediate.append(tuple(phase_immediate))
        survival.append(dual_probability(root, 0))

    joint_survival = dual_product(survival, dimension)
    numerator = []
    for phase in range(PERIOD):
        value = [IntervalDual.constant(0, dimension) for _ in range(N)]
        prefix = IntervalDual.constant(1, dimension)
        for offset in range(PERIOD):
            cycle_phase = (phase + offset) % PERIOD
            for player in range(N):
                value[player] = (
                    value[player]
                    + prefix * immediate[cycle_phase][player]
                )
            prefix = prefix * survival[cycle_phase]
        numerator.append(tuple(value))

    return ReducedCycleData(
        roots,
        tuple(immediate),
        tuple(survival),
        joint_survival,
        tuple(numerator),
    )


def reduced_system_and_jacobian(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[tuple[Interval, ...], tuple[SparseRow, ...]]:
    dimension = len(certificate.active_slots)
    data = reduced_cycle_data(box, certificate)
    one = IntervalDual.constant(1, dimension)
    denominator = one - data.joint_survival
    equations = []
    jacobian = []

    for phase, player in certificate.active_slots:
        quit_value = IntervalDual.constant(0, dimension)
        absorption = IntervalDual.constant(0, dimension)
        root = data.roots[phase]
        for opponent_mask in range(1 << N):
            if bit(opponent_mask, player):
                continue
            mass = dual_probability(root, opponent_mask, omitted=player)
            quit_value = quit_value + mass.scale(
                TERMINAL[opponent_mask | (1 << player)][player]
            )
            if opponent_mask:
                absorption = absorption + mass.scale(
                    TERMINAL[opponent_mask][player]
                )
        opponent_survival = dual_probability(root, 0, omitted=player)
        equation = (
            denominator * (quit_value - absorption)
            - opponent_survival
            * data.numerator[(phase + 1) % PERIOD][player]
        )
        equations.append(equation.value)
        jacobian.append(
            {
                column: entry
                for column, entry in enumerate(equation.derivative)
                if not entry.is_zero()
            }
        )

    assert len(equations) == len(jacobian) == dimension
    return tuple(equations), tuple(jacobian)


def reconstructed_cyclic_values(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[
    tuple[tuple[Interval, ...], ...],
    tuple[tuple[Interval, ...], ...],
    Interval,
]:
    roots = unpack_hazard_box(box, certificate)
    phases = tuple(phase_data(root) for root in roots)
    joint_survival = interval_product(tuple(data.survival for data in phases))
    denominator = ONE - joint_survival
    inverse_denominator = positive_reciprocal(denominator)
    values = []
    for phase in range(PERIOD):
        numerator = [ZERO for _ in range(N)]
        prefix = ONE
        for offset in range(PERIOD):
            cycle_phase = (phase + offset) % PERIOD
            for player in range(N):
                numerator[player] = (
                    numerator[player]
                    + prefix * phases[cycle_phase].immediate[player]
                )
            prefix = prefix * phases[cycle_phase].survival
        values.append(
            tuple(value * inverse_denominator for value in numerator)
        )
    return roots, tuple(values), joint_survival


def point_box(values: tuple[Fraction, ...]) -> tuple[Interval, ...]:
    return tuple(Interval.point(value) for value in values)


def rational_preconditioner(
    point_jacobian: tuple[SparseRow, ...], decimal_precision: int = 50
) -> list[list[Fraction]]:
    """Generate a rational approximate inverse using only Decimal arithmetic.

    Decimal elimination is not trusted as a proof step: its output is rounded
    to exact ``Fraction`` entries and the Krawczyk assertions below validate
    that rational matrix from scratch.
    """
    dimension = len(point_jacobian)
    assert dimension
    rational_matrix = [
        [Fraction(0) for _ in range(dimension)] for _ in range(dimension)
    ]
    for row_index, row in enumerate(point_jacobian):
        for column, value in row.items():
            assert 0 <= column < dimension
            assert value.low == value.high
            rational_matrix[row_index][column] = value.low

    assert decimal_precision >= 2
    with localcontext() as context:
        context.prec = decimal_precision
        context.rounding = ROUND_HALF_EVEN

        def decimal(value: Fraction) -> Decimal:
            return Decimal(value.numerator) / Decimal(value.denominator)

        augmented = []
        for row in range(dimension):
            augmented.append(
                [decimal(value) for value in rational_matrix[row]]
                + [Decimal(1 if row == column else 0) for column in range(dimension)]
            )

        for column in range(dimension):
            pivot = max(
                range(column, dimension),
                key=lambda row: abs(augmented[row][column]),
            )
            assert augmented[pivot][column] != 0
            augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
            pivot_value = augmented[column][column]
            augmented[column] = [value / pivot_value for value in augmented[column]]
            for row in range(dimension):
                if row == column:
                    continue
                multiplier = augmented[row][column]
                if multiplier == 0:
                    continue
                augmented[row] = [
                    value - multiplier * pivot_entry
                    for value, pivot_entry in zip(augmented[row], augmented[column])
                ]

        inverse_decimal = [row[dimension:] for row in augmented]

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
    dimension = len(equations_at_center)
    assert dimension == len(jacobian_on_box) == len(preconditioner)
    assert all(len(row) == dimension for row in preconditioner)
    residual = []
    for equation in equations_at_center:
        assert equation.low == equation.high
        residual.append(equation.low)

    correction = []
    for output in range(dimension):
        correction.append(
            sum(
                (preconditioner[output][row] * residual[row]
                 for row in range(dimension)),
                Fraction(0),
            )
        )

    # B = I - A J(X), represented by interval entries.  Exploit the sparse
    # rows of J rather than multiplying two dense square matrices.
    defect = [
        [Interval.point(1 if row == column else 0) for column in range(dimension)]
        for row in range(dimension)
    ]
    for equation_row, sparse_row in enumerate(jacobian_on_box):
        for column, jacobian_entry in sparse_row.items():
            assert 0 <= column < dimension
            for output in range(dimension):
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
        for index in range(dimension)
    )
    return max(row_sums), max(inclusion_ratios), inclusion_ratios


def certify_system(
    center: tuple[Fraction, ...],
    radius: Fraction,
    evaluator: SystemEvaluator,
    preconditioner_precision: int = 50,
) -> tuple[
    tuple[Interval, ...],
    list[list[Fraction]],
    Fraction,
    Fraction,
    Fraction,
]:
    center_box = point_box(center)
    equations_at_center, point_jacobian = evaluator(center_box)
    assert len(equations_at_center) == len(center)
    preconditioner = rational_preconditioner(
        point_jacobian, preconditioner_precision
    )

    box = tuple(Interval(value - radius, value + radius) for value in center)
    _, jacobian_on_box = evaluator(box)
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
    maximum_center_residual = max(
        equation.abs_upper() for equation in equations_at_center
    )
    return (
        box,
        preconditioner,
        maximum_center_residual,
        maximum_defect_row_sum,
        maximum_inclusion_ratio,
    )


def assert_strategic_inequalities_for(
    roots: tuple[tuple[Interval, ...], ...],
    values: tuple[tuple[Interval, ...], ...],
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[Fraction, Fraction, Fraction]:
    assert len(roots) == len(values) == PERIOD
    active_count = 0
    for phase, support in enumerate(certificate.support_word):
        for player in range(N):
            hazard = roots[phase][player]
            if bit(support, player):
                active_count += 1
                assert 0 < hazard.low < hazard.high < 1
            else:
                assert hazard.is_zero()
    assert active_count == len(certificate.active_slots)

    inactive_upper = None
    inactive_count = 0
    for phase, support in enumerate(certificate.support_word):
        successor = (phase + 1) % PERIOD
        for player in range(N):
            if bit(support, player):
                continue
            inactive_count += 1
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
    assert inactive_count == N * PERIOD - len(certificate.active_slots) == 13
    assert inactive_upper is not None
    return inactive_upper, opponent_cycle_upper, joint_cycle.high


def assert_strategic_inequalities(
    box: tuple[Interval, ...],
) -> tuple[Fraction, Fraction, Fraction]:
    roots, values = unpack_box(box)
    return assert_strategic_inequalities_for(
        roots, values, BASE_REDUCED_CERTIFICATE
    )


def assert_reduced_orientation(
    certificate: ReducedCertificateData,
) -> Fraction | None:
    """Check value reconstruction and the exact row identity H = (1-rho)D."""

    point = point_box(certificate.hazard_center)
    equations, _ = reduced_system_and_jacobian(point, certificate)
    roots, values, joint_survival = reconstructed_cyclic_values(
        point, certificate
    )
    denominator = ONE - joint_survival
    phases = tuple(phase_data(root) for root in roots)
    for phase in range(PERIOD):
        successor = (phase + 1) % PERIOD
        for player in range(N):
            assert values[phase][player] == (
                phases[phase].immediate[player]
                + phases[phase].survival * values[successor][player]
            )
    for reduced_equation, (phase, player) in zip(
        equations, certificate.active_slots
    ):
        successor = (phase + 1) % PERIOD
        opponent = opponent_data(roots[phase], player)
        difference = (
            opponent.quit_value
            - opponent.absorption
            - opponent.survival * values[successor][player]
        )
        assert reduced_equation == denominator * difference

    if certificate is not BASE_REDUCED_CERTIFICATE:
        return None

    lifted_point = point + tuple(
        values[phase][player]
        for phase in range(PERIOD)
        for player in range(N)
    )
    full_equations, _ = system_and_jacobian(lifted_point)
    assert all(equation.is_zero() for equation in full_equations[:VALUE_COUNT])
    for reduced_equation, full_equation in zip(
        equations, full_equations[VALUE_COUNT:]
    ):
        assert reduced_equation == denominator * full_equation

    mismatch = Fraction(0)
    for phase in range(PERIOD):
        for player in range(N):
            value = values[phase][player]
            assert value.low == value.high
            mismatch = max(
                mismatch,
                abs(value.low - VALUE_CENTER[phase][player]),
            )
    return mismatch


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def reduced_preconditioner_document(
    preconditioner: list[list[Fraction]],
    radius: Fraction,
    certificate: ReducedCertificateData = BASE_REDUCED_CERTIFICATE,
) -> tuple[str, str, int, int]:
    dimension = len(certificate.active_slots)
    assert len(preconditioner) == dimension
    assert all(len(row) == dimension for row in preconditioner)
    payload = {
        "center": [fraction_text(value) for value in certificate.hazard_center],
        "dimension": dimension,
        "format": "block-pair-k11-reduced-preconditioner-v1",
        "matrix": [
            [fraction_text(value) for value in row]
            for row in preconditioner
        ],
        "preconditioner_decimal_precision": REDUCED_PRECONDITIONER_PRECISION,
        "radius": fraction_text(radius),
        "support_word": list(certificate.support_word),
        "system": "H=(1-rho)*(q-a)-c*N_next",
        "terminal": [
            [mask, *TERMINAL[mask]] for mask in range(1, 1 << N)
        ],
        "variable_order": [list(slot) for slot in certificate.active_slots],
    }
    canonical_payload = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    )
    digest = sha256(canonical_payload.encode("utf-8")).hexdigest()
    document = json.dumps(
        {"payload": payload, "sha256": digest},
        sort_keys=True,
        separators=(",", ":"),
    )
    maximum_denominator_digits = max(
        len(str(value.denominator))
        for row in preconditioner
        for value in row
    )
    return (
        document,
        digest,
        len(canonical_payload.encode("utf-8")),
        maximum_denominator_digits,
    )


def main() -> None:
    arguments = sys.argv[1:]
    export_preconditioner = arguments == ["--export-reduced-preconditioner"]
    if arguments and not export_preconditioner:
        raise SystemExit(
            "usage: block_pair_period_eleven_certificate.py "
            "[--export-reduced-preconditioner]"
        )

    radius = Fraction(1, 10**8)
    (
        full_box,
        _,
        full_center_residual,
        full_defect_row_sum,
        full_inclusion_ratio,
    ) = certify_system(CENTER, radius, system_and_jacobian)
    (
        full_inactive_upper,
        full_opponent_cycle_upper,
        full_joint_cycle_upper,
    ) = assert_strategic_inequalities(full_box)

    base_reduced_evaluator = partial(
        reduced_system_and_jacobian,
        certificate=BASE_REDUCED_CERTIFICATE,
    )
    (
        reduced_box,
        reduced_preconditioner,
        reduced_center_residual,
        reduced_defect_row_sum,
        reduced_inclusion_ratio,
    ) = certify_system(
        BASE_REDUCED_CERTIFICATE.hazard_center,
        radius,
        base_reduced_evaluator,
        REDUCED_PRECONDITIONER_PRECISION,
    )
    reduced_value_center_mismatch = assert_reduced_orientation(
        BASE_REDUCED_CERTIFICATE
    )
    assert reduced_value_center_mismatch is not None
    reduced_roots, reduced_values, reduced_joint_cycle = (
        reconstructed_cyclic_values(reduced_box, BASE_REDUCED_CERTIFICATE)
    )
    (
        reduced_inactive_upper,
        reduced_opponent_cycle_upper,
        reduced_joint_cycle_upper,
    ) = assert_strategic_inequalities_for(
        reduced_roots, reduced_values, BASE_REDUCED_CERTIFICATE
    )
    assert reduced_joint_cycle.high == reduced_joint_cycle_upper

    (
        preconditioner_document,
        preconditioner_digest,
        preconditioner_payload_bytes,
        maximum_denominator_digits,
    ) = reduced_preconditioner_document(
        reduced_preconditioner, radius, BASE_REDUCED_CERTIFICATE
    )

    nearby_reduced_evaluator = partial(
        reduced_system_and_jacobian,
        certificate=NEARBY_REDUCED_CERTIFICATE,
    )
    (
        nearby_box,
        nearby_preconditioner,
        nearby_center_residual,
        nearby_defect_row_sum,
        nearby_inclusion_ratio,
    ) = certify_system(
        NEARBY_REDUCED_CERTIFICATE.hazard_center,
        radius,
        nearby_reduced_evaluator,
        REDUCED_PRECONDITIONER_PRECISION,
    )
    assert assert_reduced_orientation(NEARBY_REDUCED_CERTIFICATE) is None
    nearby_roots, nearby_values, nearby_joint_cycle = (
        reconstructed_cyclic_values(
            nearby_box, NEARBY_REDUCED_CERTIFICATE
        )
    )
    payoff_coordinate_separations = (
        nearby_values[0][0].low - reduced_values[0][0].high,
        nearby_values[0][1].low - reduced_values[0][1].high,
        reduced_values[0][2].low - nearby_values[0][2].high,
        nearby_values[0][3].low - reduced_values[0][3].high,
    )
    assert all(gap > 0 for gap in payoff_coordinate_separations)
    minimum_payoff_coordinate_separation = min(
        payoff_coordinate_separations
    )
    (
        nearby_inactive_upper,
        nearby_opponent_cycle_upper,
        nearby_joint_cycle_upper,
    ) = assert_strategic_inequalities_for(
        nearby_roots, nearby_values, NEARBY_REDUCED_CERTIFICATE
    )
    assert nearby_joint_cycle.high == nearby_joint_cycle_upper
    (
        _,
        nearby_preconditioner_digest,
        nearby_preconditioner_payload_bytes,
        nearby_maximum_denominator_digits,
    ) = reduced_preconditioner_document(
        nearby_preconditioner, radius, NEARBY_REDUCED_CERTIFICATE
    )

    if export_preconditioner:
        print(preconditioner_document)
        return

    print("exact period-eleven 75-variable Krawczyk certificate passed")
    print(f"dimension = {DIMENSION}")
    print(f"box radius = {radius}")
    print(f"maximum center residual ~= {float(full_center_residual):.3e}")
    print(f"maximum ||I-AJ(X)|| row sum ~= {float(full_defect_row_sum):.3e}")
    print(f"maximum Krawczyk inclusion ratio ~= {float(full_inclusion_ratio):.3e}")
    print(f"largest inactive Quit-minus-Continue upper bound ~= {float(full_inactive_upper):.6f}")
    print(f"largest opponent-cycle survival upper bound ~= {float(full_opponent_cycle_upper):.6f}")
    print(f"joint-cycle survival upper bound ~= {float(full_joint_cycle_upper):.6f}")
    print()
    print("exact period-eleven 31-variable eliminated Krawczyk certificate passed")
    print(f"dimension = {HAZARD_COUNT}")
    print(f"box radius = {radius}")
    print(f"maximum center residual ~= {float(reduced_center_residual):.3e}")
    print(f"maximum ||I-AJ(X)|| row sum ~= {float(reduced_defect_row_sum):.3e}")
    print(f"maximum Krawczyk inclusion ratio ~= {float(reduced_inclusion_ratio):.3e}")
    print(f"largest inactive Quit-minus-Continue upper bound ~= {float(reduced_inactive_upper):.6f}")
    print(f"largest opponent-cycle survival upper bound ~= {float(reduced_opponent_cycle_upper):.6f}")
    print(f"joint-cycle survival upper bound ~= {float(reduced_joint_cycle_upper):.6f}")
    print(f"maximum reconstructed-value center mismatch ~= {float(reduced_value_center_mismatch):.3e}")
    print(f"reduced preconditioner SHA-256 = {preconditioner_digest}")
    print(f"reduced preconditioner canonical payload bytes = {preconditioner_payload_bytes}")
    print(f"reduced preconditioner maximum denominator digits = {maximum_denominator_digits}")
    print(
        "reduced preconditioner Decimal generation precision = "
        f"{REDUCED_PRECONDITIONER_PRECISION}"
    )
    print(
        "reduced variable order = "
        + ",".join(f"{phase}:{player}" for phase, player in ACTIVE_SLOTS)
    )
    print()
    print(
        "exact neighboring period-eleven 31-variable eliminated "
        "Krawczyk certificate passed"
    )
    print(f"certificate name = {NEARBY_REDUCED_CERTIFICATE.name}")
    print(
        "support word = "
        + ",".join(
            str(support)
            for support in NEARBY_REDUCED_CERTIFICATE.support_word
        )
    )
    print(f"dimension = {len(NEARBY_REDUCED_CERTIFICATE.active_slots)}")
    print(f"box radius = {radius}")
    print(f"maximum center residual ~= {float(nearby_center_residual):.3e}")
    print(
        "maximum ||I-AJ(X)|| row sum ~= "
        f"{float(nearby_defect_row_sum):.3e}"
    )
    print(
        "maximum Krawczyk inclusion ratio ~= "
        f"{float(nearby_inclusion_ratio):.3e}"
    )
    print(
        "largest inactive Quit-minus-Continue upper bound ~= "
        f"{float(nearby_inactive_upper):.6f}"
    )
    print(
        "largest opponent-cycle survival upper bound ~= "
        f"{float(nearby_opponent_cycle_upper):.6f}"
    )
    print(
        "joint-cycle survival upper bound ~= "
        f"{float(nearby_joint_cycle_upper):.6f}"
    )
    print(
        "minimum phase-zero payoff-coordinate separation ~= "
        f"{float(minimum_payoff_coordinate_separation):.6f}"
    )
    print(
        "neighboring reduced preconditioner SHA-256 = "
        f"{nearby_preconditioner_digest}"
    )
    print(
        "neighboring reduced preconditioner canonical payload bytes = "
        f"{nearby_preconditioner_payload_bytes}"
    )
    print(
        "neighboring reduced preconditioner maximum denominator digits = "
        f"{nearby_maximum_denominator_digits}"
    )


if __name__ == "__main__":
    main()
