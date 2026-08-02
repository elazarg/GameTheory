#!/usr/bin/env python3
"""Exact one-parameter payoff robustness for all three block-pair K11 roots.

The parameter changes one stored terminal payoff,

    r_0({0}) = -2 + theta,

while every other payoff remains fixed.  For every theta in the rational
interval certified below, this script proves that each of the three support
words has a unique exact active-indifference root in its displayed rational
hazard box, retains every strict inactive inequality, and retains playerwise
opponent-cycle contraction.

The proof is a parameter-uniform rectangular Krawczyk/Banach calculation.  An
exact affine model retains the shared theta coefficient through the system,
preconditioner, value reconstruction, and strategic inequalities; its range
is taken only at the end.  Approximate inverses are generated with Decimal,
rounded to rational matrices, and then checked entirely with ``Fraction``
interval arithmetic.  No floating-point result is trusted.

This is an external certificate, not yet a Lean theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import block_pair_period_eleven_certificate as period


Interval = period.Interval
IntervalDual = period.IntervalDual
ReducedCertificateData = period.ReducedCertificateData
SparseRow = period.SparseRow
N = period.N
PERIOD = period.PERIOD
ZERO = period.ZERO
ONE = period.ONE

PARAMETER_MASK = 1
PARAMETER_PLAYER = 0


def terminal_slope(mask: int, player: int) -> Fraction:
    return Fraction(
        int(mask == PARAMETER_MASK and player == PARAMETER_PLAYER)
    )


PARAMETER_UNIT_BOX = Interval(Fraction(-1), Fraction(1))


def parameter_range(coefficient: Interval, radius: Fraction) -> Interval:
    return coefficient * PARAMETER_UNIT_BOX.scale(radius)


@dataclass(frozen=True)
class AffineDual:
    """An interval dual number affine in the single payoff parameter."""

    constant: IntervalDual
    slope: IntervalDual

    @staticmethod
    def zero(dimension: int) -> "AffineDual":
        zero = IntervalDual.constant(0, dimension)
        return AffineDual(zero, zero)

    def __add__(self, other: "AffineDual") -> "AffineDual":
        return AffineDual(
            self.constant + other.constant,
            self.slope + other.slope,
        )

    def __neg__(self) -> "AffineDual":
        return AffineDual(-self.constant, -self.slope)

    def __sub__(self, other: "AffineDual") -> "AffineDual":
        return self + (-other)

    def mul_free(self, value: IntervalDual) -> "AffineDual":
        return AffineDual(self.constant * value, self.slope * value)

    def range(self, parameter_radius: Fraction) -> IntervalDual:
        return IntervalDual(
            self.constant.value
            + parameter_range(self.slope.value, parameter_radius),
            tuple(
                constant
                + parameter_range(slope, parameter_radius)
                for constant, slope in zip(
                    self.constant.derivative, self.slope.derivative
                )
            ),
        )


def affine_dual_terminal_product(
    mass: IntervalDual, mask: int, player: int
) -> AffineDual:
    return AffineDual(
        mass.scale(period.TERMINAL[mask][player]),
        mass.scale(terminal_slope(mask, player)),
    )


@dataclass(frozen=True)
class AffineCycleData:
    roots: tuple[tuple[IntervalDual, ...], ...]
    immediate: tuple[tuple[AffineDual, ...], ...]
    survival: tuple[IntervalDual, ...]
    joint_survival: IntervalDual
    numerator: tuple[tuple[AffineDual, ...], ...]


def affine_cycle_data(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData,
) -> AffineCycleData:
    dimension = len(certificate.active_slots)
    roots = period.unpack_dual_hazard_box(box, certificate)
    immediate = []
    survival = []
    for root in roots:
        phase_immediate = [
            AffineDual.zero(dimension) for _ in range(N)
        ]
        for mask in range(1, 1 << N):
            mass = period.dual_probability(root, mask)
            for player in range(N):
                phase_immediate[player] = (
                    phase_immediate[player]
                    + affine_dual_terminal_product(mass, mask, player)
                )
        immediate.append(tuple(phase_immediate))
        survival.append(period.dual_probability(root, 0))

    joint_survival = period.dual_product(survival, dimension)
    numerator = []
    for phase in range(PERIOD):
        value = [AffineDual.zero(dimension) for _ in range(N)]
        prefix = IntervalDual.constant(1, dimension)
        for offset in range(PERIOD):
            cycle_phase = (phase + offset) % PERIOD
            for player in range(N):
                value[player] = (
                    value[player]
                    + immediate[cycle_phase][player].mul_free(prefix)
                )
            prefix = prefix * survival[cycle_phase]
        numerator.append(tuple(value))

    return AffineCycleData(
        roots,
        tuple(immediate),
        tuple(survival),
        joint_survival,
        tuple(numerator),
    )


def affine_system(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData,
) -> tuple[AffineDual, ...]:
    dimension = len(certificate.active_slots)
    data = affine_cycle_data(box, certificate)
    denominator = (
        IntervalDual.constant(1, dimension) - data.joint_survival
    )
    equations = []

    for phase, player in certificate.active_slots:
        quit_value = AffineDual.zero(dimension)
        absorption = AffineDual.zero(dimension)
        root = data.roots[phase]
        for opponent_mask in range(1 << N):
            if period.bit(opponent_mask, player):
                continue
            mass = period.dual_probability(
                root, opponent_mask, omitted=player
            )
            quit_value = quit_value + affine_dual_terminal_product(
                mass, opponent_mask | (1 << player), player
            )
            if opponent_mask:
                absorption = absorption + affine_dual_terminal_product(
                    mass, opponent_mask, player
                )
        opponent_survival = period.dual_probability(
            root, 0, omitted=player
        )
        equation = (
            (quit_value - absorption).mul_free(denominator)
            - data.numerator[(phase + 1) % PERIOD][player].mul_free(
                opponent_survival
            )
        )
        equations.append(equation)
    assert len(equations) == dimension
    return tuple(equations)


def ranged_system_and_jacobian(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData,
    parameter_radius: Fraction,
) -> tuple[tuple[Interval, ...], tuple[SparseRow, ...]]:
    equations = affine_system(box, certificate)
    values = []
    jacobian = []
    for equation in equations:
        ranged = equation.range(parameter_radius)
        values.append(ranged.value)
        jacobian.append(
            {
                column: entry
                for column, entry in enumerate(ranged.derivative)
                if not entry.is_zero()
            }
        )
    return tuple(values), tuple(jacobian)


@dataclass(frozen=True)
class AffineInterval:
    constant: Interval
    slope: Interval

    @staticmethod
    def zero() -> "AffineInterval":
        return AffineInterval(ZERO, ZERO)

    def __add__(self, other: "AffineInterval") -> "AffineInterval":
        return AffineInterval(
            self.constant + other.constant,
            self.slope + other.slope,
        )

    def __neg__(self) -> "AffineInterval":
        return AffineInterval(-self.constant, -self.slope)

    def __sub__(self, other: "AffineInterval") -> "AffineInterval":
        return self + (-other)

    def mul_free(self, value: Interval) -> "AffineInterval":
        return AffineInterval(self.constant * value, self.slope * value)

    def range(self, parameter_radius: Fraction) -> Interval:
        return self.constant + parameter_range(self.slope, parameter_radius)


def affine_terminal_product(
    mass: Interval, mask: int, player: int
) -> AffineInterval:
    return AffineInterval(
        mass.scale(period.TERMINAL[mask][player]),
        mass.scale(terminal_slope(mask, player)),
    )


def affine_phase_immediate(
    root: tuple[Interval, ...],
) -> tuple[AffineInterval, ...]:
    immediate = [AffineInterval.zero() for _ in range(N)]
    for mask in range(1, 1 << N):
        mass = period.probability(root, mask)
        for player in range(N):
            immediate[player] = (
                immediate[player]
                + affine_terminal_product(mass, mask, player)
            )
    return tuple(immediate)


def parameterized_reconstructed_values(
    box: tuple[Interval, ...],
    certificate: ReducedCertificateData,
) -> tuple[
    tuple[tuple[Interval, ...], ...],
    tuple[tuple[AffineInterval, ...], ...],
    Interval,
]:
    roots = period.unpack_hazard_box(box, certificate)
    immediate = tuple(
        affine_phase_immediate(root) for root in roots
    )
    survival = tuple(period.probability(root, 0) for root in roots)
    joint_survival = period.interval_product(survival)
    inverse_denominator = period.positive_reciprocal(ONE - joint_survival)
    values = []
    for phase in range(PERIOD):
        numerator = [AffineInterval.zero() for _ in range(N)]
        prefix = ONE
        for offset in range(PERIOD):
            cycle_phase = (phase + offset) % PERIOD
            for player in range(N):
                numerator[player] = (
                    numerator[player]
                    + immediate[cycle_phase][player].mul_free(prefix)
                )
            prefix = prefix * survival[cycle_phase]
        values.append(
            tuple(
                value.mul_free(inverse_denominator)
                for value in numerator
            )
        )
    return roots, tuple(values), joint_survival


def affine_opponent_values(
    root: tuple[Interval, ...],
    player: int,
) -> tuple[AffineInterval, AffineInterval, Interval]:
    quit_value = AffineInterval.zero()
    absorption = AffineInterval.zero()
    for opponent_mask in range(1 << N):
        if period.bit(opponent_mask, player):
            continue
        mass = period.probability(root, opponent_mask, omitted=player)
        quit_value = (
            quit_value
            + affine_terminal_product(
                mass, opponent_mask | (1 << player), player
            )
        )
        if opponent_mask:
            absorption = (
                absorption
                + affine_terminal_product(mass, opponent_mask, player)
            )
    survival = period.probability(root, 0, omitted=player)
    return quit_value, absorption, survival


@dataclass(frozen=True)
class UniformCertificateResult:
    box: tuple[Interval, ...]
    maximum_center_residual: Fraction
    maximum_defect_row_sum: Fraction
    maximum_inclusion_ratio: Fraction
    largest_inactive_upper: Fraction
    largest_opponent_cycle_upper: Fraction
    joint_cycle_upper: Fraction


def interval_linear_combination(
    coefficients: list[Fraction], values: tuple[Interval, ...]
) -> Interval:
    result = ZERO
    for coefficient, value in zip(coefficients, values):
        if coefficient:
            result = result + value.scale(coefficient)
    return result


def affine_linear_combination(
    coefficients: list[Fraction], values: tuple[AffineDual, ...]
) -> AffineInterval:
    return AffineInterval(
        interval_linear_combination(
            coefficients, tuple(value.constant.value for value in values)
        ),
        interval_linear_combination(
            coefficients, tuple(value.slope.value for value in values)
        ),
    )


def certify_parameter_box(
    certificate: ReducedCertificateData,
    parameter_radius: Fraction,
    coordinate_radii: tuple[Fraction, ...],
) -> UniformCertificateResult:
    dimension = len(certificate.active_slots)
    assert len(coordinate_radii) == dimension
    assert all(radius > 0 for radius in coordinate_radii)
    center = certificate.hazard_center

    nominal_point = period.point_box(center)
    _, nominal_jacobian = period.reduced_system_and_jacobian(
        nominal_point, certificate
    )
    preconditioner = period.rational_preconditioner(
        nominal_jacobian, period.REDUCED_PRECONDITIONER_PRECISION
    )
    assert len(preconditioner) == dimension

    affine_equations_at_center = affine_system(
        nominal_point, certificate
    )
    equations_at_center = tuple(
        equation.range(parameter_radius).value
        for equation in affine_equations_at_center
    )
    box = tuple(
        Interval(value - radius, value + radius)
        for value, radius in zip(center, coordinate_radii)
    )
    affine_equations_on_box = affine_system(box, certificate)

    correction = tuple(
        affine_linear_combination(
            row, affine_equations_at_center
        ).range(parameter_radius)
        for row in preconditioner
    )
    defect = []
    for output in range(dimension):
        row = []
        for column in range(dimension):
            constant = Interval.point(1 if output == column else 0)
            slope = ZERO
            for equation_row, equation in enumerate(
                affine_equations_on_box
            ):
                coefficient = preconditioner[output][equation_row]
                if coefficient:
                    constant = (
                        constant
                        - equation.constant.derivative[column].scale(
                            coefficient
                        )
                    )
                    slope = (
                        slope
                        - equation.slope.derivative[column].scale(
                            coefficient
                        )
                    )
            row.append(
                constant + parameter_range(slope, parameter_radius)
            )
        defect.append(row)

    defect_row_sums = tuple(
        sum((entry.abs_upper() for entry in row), Fraction(0))
        for row in defect
    )
    inclusion_ratios = []
    for output, row in enumerate(defect):
        image_radius = correction[output].abs_upper() + sum(
            (
                entry.abs_upper() * coordinate_radii[column]
                for column, entry in enumerate(row)
            ),
            Fraction(0),
        )
        inclusion_ratios.append(image_radius / coordinate_radii[output])
    maximum_defect_row_sum = max(defect_row_sums)
    maximum_defect_row = defect_row_sums.index(maximum_defect_row_sum)
    maximum_inclusion_ratio = max(inclusion_ratios)
    maximum_inclusion_row = inclusion_ratios.index(maximum_inclusion_ratio)
    assert maximum_defect_row_sum < 1, (
        "defect row sum",
        maximum_defect_row,
        float(maximum_defect_row_sum),
    )
    assert maximum_inclusion_ratio < 1, (
        "inclusion ratio",
        maximum_inclusion_row,
        float(maximum_inclusion_ratio),
        "correction",
        float(correction[maximum_inclusion_row].abs_upper()),
        "radius",
        float(coordinate_radii[maximum_inclusion_row]),
    )

    roots, values, joint_survival = parameterized_reconstructed_values(
        box, certificate
    )
    inactive_upper = None
    for phase, support in enumerate(certificate.support_word):
        for player in range(N):
            hazard = roots[phase][player]
            if period.bit(support, player):
                assert 0 < hazard.low <= hazard.high < 1
                continue
            assert hazard.is_zero()
            quit_value, absorption, survival = affine_opponent_values(
                roots[phase], player
            )
            difference = (
                quit_value
                - absorption
                - values[(phase + 1) % PERIOD][player].mul_free(survival)
            ).range(parameter_radius)
            assert difference.high < 0
            inactive_upper = (
                difference.high
                if inactive_upper is None
                else max(inactive_upper, difference.high)
            )
    assert inactive_upper is not None

    opponent_cycle_upper = Fraction(0)
    for player in range(N):
        cycle = period.interval_product(
            tuple(
                period.opponent_data(roots[phase], player).survival
                for phase in range(PERIOD)
            )
        )
        assert cycle.high < 1
        opponent_cycle_upper = max(opponent_cycle_upper, cycle.high)
    assert joint_survival.high < 1

    return UniformCertificateResult(
        box,
        max(equation.abs_upper() for equation in equations_at_center),
        maximum_defect_row_sum,
        maximum_inclusion_ratio,
        inactive_upper,
        opponent_cycle_upper,
        joint_survival.high,
    )


# These rectangular radii were generated from a rounded first-order response
# and are merely witness data. The exact checks above carry all trust.
PARAMETER_RADIUS = Fraction(1, 250)
COORDINATE_RADII_TEXT = {
    "base": (
        ".0000849823", ".0001242355", ".0006099297", ".0000638477",
        ".0001698683", ".0004859431", ".0002508478", ".0001292644",
        ".0001890072", ".0002999635", ".0000654403", ".0002843572",
        ".0002570110", ".0001947164", ".0006390741", ".0002755402",
        ".0006050146", ".0008259636", ".0001147098", ".0007261335",
        ".0001702814", ".0003919281", ".0004018347", ".0003719176",
        ".0001522981", ".0005210321", ".0003614718", ".0000520513",
        ".0001213818", ".0000681377", ".0005602963",
    ),
    "phase4-mask11-to-mask14": (
        ".0000858742", ".0001086874", ".0005918721", ".0000487928",
        ".0001494656", ".0005007173", ".0002114137", ".0001076698",
        ".0001375821", ".0002016707", ".0000980988", ".0002337495",
        ".0001698020", ".0001066458", ".0003417717", ".0002672976",
        ".0005881768", ".0007986277", ".0001083206", ".0007001091",
        ".0001613507", ".0003757310", ".0003829725", ".0003539774",
        ".0001417025", ".0005025117", ".0003281609", ".0000458656",
        ".0001202775", ".0000549562", ".0005248752",
    ),
    "phase4-mask11-to-mask10": (
        ".0000771846", ".0000774993", ".0005619070", ".0000522791",
        ".0000982688", ".0004638765", ".0001349452", ".0000770730",
        ".0001403931", ".0001264652", ".0000639381", ".0002139258",
        ".0005081374", ".0003370188", ".0002619204", ".0005736532",
        ".0007886966", ".0001085864", ".0006737596", ".0001630814",
        ".0003556533", ".0003855050", ".0003423746", ".0001436592",
        ".0005206557", ".0003496669", ".0000508383", ".0001101278",
        ".0000360960", ".0005027530",
    ),
}


def main() -> None:
    print(
        "terminal payoff family: r_0({0}) = -2 + theta, "
        f"|theta| <= {PARAMETER_RADIUS}"
    )
    for certificate in (
        period.BASE_REDUCED_CERTIFICATE,
        period.NEARBY_REDUCED_CERTIFICATE,
        period.SUPPORT_TEN_REDUCED_CERTIFICATE,
    ):
        radii = tuple(
            Fraction(text)
            for text in COORDINATE_RADII_TEXT[certificate.name]
        )
        result = certify_parameter_box(
            certificate, PARAMETER_RADIUS, radii
        )
        print(f"exact uniform parameter certificate passed: {certificate.name}")
        print(
            "maximum parameterized center residual ~= "
            f"{float(result.maximum_center_residual):.6e}"
        )
        print(
            "maximum defect row sum ~= "
            f"{float(result.maximum_defect_row_sum):.6e}"
        )
        print(
            "maximum rectangular inclusion ratio ~= "
            f"{float(result.maximum_inclusion_ratio):.6e}"
        )
        print(
            "largest inactive upper bound ~= "
            f"{float(result.largest_inactive_upper):.6e}"
        )


if __name__ == "__main__":
    main()
