#!/usr/bin/env python3
"""Exact full-payoff robustness probe for the K11 memory-three full shift.

Every one of the 60 stored terminal rewards may vary independently in the
sup-norm ball of radius ``PAYOFF_RADIUS``.  Rather than trusting a precomputed
parameter table, this checker enlarges every one-phase active system by exact
expectation/derivative error bounds and proves a parameter-uniform interval
Newton inclusion.  It then replays all 81 directed context-box edges.

The perturbation bounds used below are deliberately elementary.  An expected
terminal reward changes by at most ``epsilon``.  A Quit-minus-Continue value
changes by at most ``2 epsilon``.  Differentiating an expectation with respect
to one Bernoulli hazard gives a difference of two conditional expectations,
so the active Jacobian changes by at most ``4 epsilon`` and the prescribed
immediate-payoff derivative by at most ``2 epsilon``.

All certification arithmetic is exact ``Fraction`` interval arithmetic.  The
payoff parameters are allowed to vary independently at every use, a superset
of one fixed perturbed payoff table, so a pass is conservative.  Floating
point only proposes the nominal scalar quadratic branch; the imported exact
interval Newton check validates it before this checker adds payoff variation.

This is an external exact certificate, not a Lean theorem.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this assertion-based exact certificate must not run under python -O"
    )

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_period_eleven_common_box as base  # noqa: E402
from block_pair_period_eleven_certificate import (  # noqa: E402
    N,
    ONE,
    PERIOD,
    ZERO,
    Interval,
    ReducedCertificateData,
    bit,
    opponent_data,
    phase_data,
)
from block_pair_period_eleven_return_certificate import (  # noqa: E402
    Matrix,
    distance_from_zero,
    identity,
    inverse,
    multiply,
)


VectorBox = tuple[Interval, ...]
PAYOFF_RADIUS = Fraction(1, 10**12)
ROOT_PADDING = Fraction(1, 10**7)
PAYOFF_VALUE_ERROR = Interval(-PAYOFF_RADIUS, PAYOFF_RADIUS)
DIFFERENCE_ERROR = Interval(-2 * PAYOFF_RADIUS, 2 * PAYOFF_RADIUS)
IMMEDIATE_DERIVATIVE_ERROR = Interval(
    -2 * PAYOFF_RADIUS, 2 * PAYOFF_RADIUS
)
DIFFERENCE_DERIVATIVE_ERROR = Interval(
    -4 * PAYOFF_RADIUS, 4 * PAYOFF_RADIUS
)


def robust_active_root(
    support: int,
    successor: VectorBox,
    reference_root: tuple[Fraction, ...],
) -> VectorBox:
    nominal = base.round_vector(
        base.selected_hazard(support, successor, reference_root[3])
    )
    active = [player for player in range(N) if bit(support, player)]
    domain = tuple(
        Interval(
            nominal[player].low - ROOT_PADDING,
            nominal[player].high + ROOT_PADDING,
        )
        if player in active
        else ZERO
        for player in range(N)
    )
    center = tuple(base.midpoint(value) for value in domain)
    center_root = tuple(Interval.point(value) for value in center)

    values = []
    jacobian: Matrix = []
    for player in active:
        point_data = opponent_data(center_root, player)
        values.append(
            point_data.quit_value
            - point_data.absorption
            - point_data.survival * successor[player]
            + DIFFERENCE_ERROR
        )
        data = opponent_data(domain, player)
        jacobian.append(
            [
                data.quit_derivative[variable]
                - data.absorption_derivative[variable]
                - data.survival_derivative[variable]
                * successor[player]
                + DIFFERENCE_DERIVATIVE_ERROR
                for variable in active
            ]
        )

    inverse_jacobian, determinant = inverse(jacobian)
    assert distance_from_zero(determinant) > 0
    correction = base.matrix_times_vector(inverse_jacobian, tuple(values))
    newton = tuple(
        base.outward_round(Interval.point(center[player]) - correction[index])
        for index, player in enumerate(active)
    )
    result = [ZERO for _ in range(N)]
    for index, player in enumerate(active):
        assert domain[player].low < newton[index].low
        assert newton[index].high < domain[player].high
        assert 0 < newton[index].low <= newton[index].high < 1
        result[player] = newton[index]
    return tuple(result)


def robust_predecessor_jacobian(
    root: VectorBox,
    successor: VectorBox,
    support: int,
) -> tuple[Matrix, Interval]:
    active = [player for player in range(N) if bit(support, player)]
    opponents = [opponent_data(root, player) for player in active]
    active_jacobian: Matrix = []
    for equation, player in zip(opponents, active):
        active_jacobian.append(
            [
                equation.quit_derivative[variable]
                - equation.absorption_derivative[variable]
                - equation.survival_derivative[variable]
                * successor[player]
                + DIFFERENCE_DERIVATIVE_ERROR
                for variable in active
            ]
        )
    active_inverse, determinant = inverse(active_jacobian)
    negative_d_w = [
        [
            equation.survival if player == coordinate else ZERO
            for coordinate in range(N)
        ]
        for equation, player in zip(opponents, active)
    ]
    hazard_derivative = multiply(active_inverse, negative_d_w)

    phase = phase_data(root)
    result = identity(N)
    for row in range(N):
        for column in range(N):
            result[row][column] = (
                result[row][column] * phase.survival
            )
            for active_index, variable in enumerate(active):
                coefficient = (
                    phase.immediate_derivative[row][variable]
                    + IMMEDIATE_DERIVATIVE_ERROR
                    + phase.survival_derivative[variable]
                    * successor[row]
                )
                result[row][column] = (
                    result[row][column]
                    + coefficient
                    * hazard_derivative[active_index][column]
                )
    return base.round_matrix(result), determinant


@dataclass(frozen=True)
class RobustChartResult:
    center_predecessor: VectorBox
    jacobian: Matrix
    root: VectorBox
    minimum_inactive_gap: Fraction
    minimum_active_determinant_gap: Fraction


def robust_chart(
    support: int,
    successor: VectorBox,
    reference_root: tuple[Fraction, ...],
    center: tuple[Fraction, ...],
) -> RobustChartResult:
    root = robust_active_root(support, successor, reference_root)
    center_successor = tuple(Interval.point(value) for value in center)
    center_root = robust_active_root(
        support, center_successor, reference_root
    )
    center_phase = phase_data(center_root)
    center_predecessor = base.round_vector(
        tuple(
            immediate
            + PAYOFF_VALUE_ERROR
            + center_phase.survival * value
            for immediate, value in zip(
                center_phase.immediate, center_successor
            )
        )
    )

    jacobian, determinant = robust_predecessor_jacobian(
        root, successor, support
    )
    determinant_gap = distance_from_zero(determinant)
    inactive_gap: Fraction | None = None
    for player in range(N):
        data = opponent_data(root, player)
        difference = (
            data.quit_value
            - data.absorption
            - data.survival * successor[player]
            + DIFFERENCE_ERROR
        )
        if bit(support, player):
            assert difference.low <= 0 <= difference.high
        else:
            assert difference.high < 0
            gap = -difference.high
            inactive_gap = (
                gap if inactive_gap is None else min(inactive_gap, gap)
            )
    assert inactive_gap is not None
    return RobustChartResult(
        center_predecessor,
        jacobian,
        root,
        inactive_gap,
        determinant_gap,
    )


@dataclass(frozen=True)
class RobustReturnResult:
    image: VectorBox
    derivative: Matrix
    minimum_inactive_gap: Fraction
    minimum_active_determinant_gap: Fraction
    opponent_products: tuple[Interval, ...]


def robust_return(
    initial: VectorBox, certificate: ReducedCertificateData
) -> RobustReturnResult:
    initial_center = tuple(base.midpoint(value) for value in initial)
    initial_displacement = tuple(
        value - Interval.point(center)
        for value, center in zip(initial, initial_center)
    )
    center = initial_center
    center_error = tuple(ZERO for _ in range(N))
    derivative = identity(N)
    minimum_inactive_gap: Fraction | None = None
    minimum_determinant_gap: Fraction | None = None
    opponent_products = [ONE for _ in range(N)]

    for phase_index in range(PERIOD - 1, -1, -1):
        successor = base.round_vector(
            tuple(
                Interval.point(point) + error + linear
                for point, error, linear in zip(
                    center,
                    center_error,
                    base.matrix_times_vector(
                        derivative, initial_displacement
                    ),
                )
            )
        )
        result = robust_chart(
            certificate.support_word[phase_index],
            successor,
            certificate.root_center[phase_index],
            center,
        )
        minimum_inactive_gap = (
            result.minimum_inactive_gap
            if minimum_inactive_gap is None
            else min(minimum_inactive_gap, result.minimum_inactive_gap)
        )
        minimum_determinant_gap = (
            result.minimum_active_determinant_gap
            if minimum_determinant_gap is None
            else min(
                minimum_determinant_gap,
                result.minimum_active_determinant_gap,
            )
        )
        for player in range(N):
            opponent_products[player] = (
                opponent_products[player]
                * opponent_data(result.root, player).survival
            )
        new_derivative = base.round_matrix(
            multiply(result.jacobian, derivative)
        )
        propagated_error = base.matrix_times_vector(
            result.jacobian, center_error
        )
        new_center = tuple(
            base.midpoint(value) for value in result.center_predecessor
        )
        center_error = base.round_vector(
            tuple(
                value - Interval.point(point) + error
                for value, point, error in zip(
                    result.center_predecessor,
                    new_center,
                    propagated_error,
                )
            )
        )
        center = new_center
        derivative = new_derivative

    assert minimum_inactive_gap is not None
    assert minimum_determinant_gap is not None
    image = base.round_vector(
        tuple(
            Interval.point(point) + error + linear
            for point, error, linear in zip(
                center,
                center_error,
                base.matrix_times_vector(
                    derivative, initial_displacement
                ),
            )
        )
    )
    return RobustReturnResult(
        image,
        derivative,
        minimum_inactive_gap,
        minimum_determinant_gap,
        tuple(opponent_products),
    )


def interval_text(value: Interval) -> str:
    return (
        f"{value.low.numerator}/{value.low.denominator}:"
        f"{value.high.numerator}/{value.high.denominator}"
    )


EXPECTED_TRANSCRIPT_SHA256 = (
    "cb97d3cf8f02539d0606ab6433e03d44b8bdfa0779865e7a998df6ca8e152491"
)


def main() -> None:
    transcript = sha256()
    edges = 0
    maximum_norm = Fraction(0)
    maximum_opponent = Fraction(0)
    minimum_inactive: Fraction | None = None
    minimum_slack: Fraction | None = None
    for target_context in product(base.ALPHABET, repeat=3):
        current, second, third = target_context
        target = base.context_box(target_context)
        certificate = base.CERTIFICATE_BY_LABEL[current]
        for appended in base.ALPHABET:
            source_context = (second, third, appended)
            source = base.context_box(source_context)
            result = robust_return(source, certificate)
            norm = base.infinity_norm(result.derivative)
            opponent = max(
                value.high for value in result.opponent_products
            )
            slack = base.strict_image_slack(result.image, target)
            assert norm < 1
            assert opponent < 1
            assert 0 < slack
            edges += 1
            maximum_norm = max(maximum_norm, norm)
            maximum_opponent = max(maximum_opponent, opponent)
            minimum_inactive = (
                result.minimum_inactive_gap
                if minimum_inactive is None
                else min(minimum_inactive, result.minimum_inactive_gap)
            )
            minimum_slack = (
                slack if minimum_slack is None else min(minimum_slack, slack)
            )
            transcript.update(
                (
                    f"{target_context}|{source_context}|"
                    + ",".join(
                        interval_text(value) for value in result.image
                    )
                    + "|"
                    + ";".join(
                        ",".join(interval_text(value) for value in row)
                        for row in result.derivative
                    )
                    + "|"
                    + ",".join(
                        interval_text(value)
                        for value in result.opponent_products
                    )
                    + "|"
                    + str(result.minimum_inactive_gap)
                    + "|"
                    + str(result.minimum_active_determinant_gap)
                    + "\n"
                ).encode("ascii")
            )
        print(
            "certified payoff-robust incoming edges for "
            + "-".join(target_context),
            flush=True,
        )

    assert edges == 81
    assert minimum_inactive is not None
    assert minimum_slack is not None
    digest = transcript.hexdigest()
    if EXPECTED_TRANSCRIPT_SHA256 != "TO_BE_FILLED":
        assert digest == EXPECTED_TRANSCRIPT_SHA256
    print("exact full-payoff robust memory-three full shift passed")
    print(f"payoff sup-norm radius = {PAYOFF_RADIUS}")
    print(f"directed edges = {edges}")
    print(f"minimum inactive gap ~= {float(minimum_inactive):.9f}")
    print(f"minimum image slack ~= {float(minimum_slack):.9e}")
    print(f"maximum true return norm ~= {float(maximum_norm):.9f}")
    print(f"maximum opponent product ~= {float(maximum_opponent):.9f}")
    print(f"transcript SHA-256 = {digest}")


if __name__ == "__main__":
    main()
