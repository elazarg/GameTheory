#!/usr/bin/env python3
"""Exact interval contraction checks for the three K11 predecessor returns.

The Krawczyk defect in ``block_pair_period_eleven_certificate.py`` concerns a
preconditioned solver on the full cyclic hazard system.  The playerwise
opponent-cycle products concern Bellman stopping values.  Neither is the
derivative of the dynamical predecessor return.

This script checks that third object directly.  For one phase, active
indifference has the form

    D_M(x, w) = 0,

where ``w`` is the successor value and ``x`` contains the active hazards.  On
each certified box the active Jacobian ``D_x`` is interval-invertible, so the
selected local predecessor chart has

    dx/dw = -(D_x)^(-1) D_w
          = (D_x)^(-1) diag(opponent_survival).

Differentiating ``v = g(x) + s(x) w`` gives its four-by-four Jacobian.  The
eleven phase Jacobians are then composed in predecessor order, beginning with
phase 10 and ending with phase 0.  All arithmetic below uses exact ``Fraction``
intervals.  Successful row-sum assertions therefore prove a genuine local
contraction of each selected predecessor return throughout the product of the
stored hazard and reconstructed-value boxes.

This is an external exact certificate, not a Lean theorem.  It proves local
attraction of the three already isolated cycles; it does not show that the
charts cover a global continuation region or that an arbitrary orbit enters
one of these boxes.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_period_eleven_certificate import (  # noqa: E402
    BASE_REDUCED_CERTIFICATE,
    N,
    NEARBY_REDUCED_CERTIFICATE,
    ONE,
    PERIOD,
    SUPPORT_TEN_REDUCED_CERTIFICATE,
    ZERO,
    Interval,
    ReducedCertificateData,
    bit,
    opponent_data,
    phase_data,
    reconstructed_cyclic_values,
)


Matrix = list[list[Interval]]
RADIUS = Fraction(1, 10**8)


def reciprocal(value: Interval) -> Interval:
    assert value.high < 0 or 0 < value.low
    return Interval(Fraction(1, 1) / value.high, Fraction(1, 1) / value.low)


def determinant(matrix: Matrix) -> Interval:
    dimension = len(matrix)
    assert all(len(row) == dimension for row in matrix)
    if dimension == 0:
        return ONE
    result = ZERO
    for column in range(dimension):
        minor = [
            [row[j] for j in range(dimension) if j != column]
            for row in matrix[1:]
        ]
        term = matrix[0][column] * determinant(minor)
        result = result + (term if column % 2 == 0 else -term)
    return result


def inverse(matrix: Matrix) -> tuple[Matrix, Interval]:
    dimension = len(matrix)
    assert 0 < dimension
    det = determinant(matrix)
    inverse_det = reciprocal(det)
    result: Matrix = []
    for row in range(dimension):
        result_row = []
        for column in range(dimension):
            # Transpose the cofactor matrix.
            minor = [
                [
                    matrix[source_row][source_column]
                    for source_column in range(dimension)
                    if source_column != row
                ]
                for source_row in range(dimension)
                if source_row != column
            ]
            cofactor = determinant(minor)
            if (row + column) % 2:
                cofactor = -cofactor
            result_row.append(cofactor * inverse_det)
        result.append(result_row)
    return result, det


def identity(dimension: int) -> Matrix:
    return [
        [ONE if row == column else ZERO for column in range(dimension)]
        for row in range(dimension)
    ]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    assert left and right
    inner = len(right)
    assert all(len(row) == inner for row in left)
    columns = len(right[0])
    assert all(len(row) == columns for row in right)
    return [
        [
            sum(
                (left[row][middle] * right[middle][column]
                 for middle in range(inner)),
                ZERO,
            )
            for column in range(columns)
        ]
        for row in range(len(left))
    ]


def predecessor_jacobian(
    root: tuple[Interval, ...],
    successor_value: tuple[Interval, ...],
    support: int,
) -> tuple[Matrix, Interval]:
    active = [player for player in range(N) if bit(support, player)]
    opponent = [opponent_data(root, player) for player in active]

    active_jacobian: Matrix = []
    for equation, player in zip(opponent, active):
        active_jacobian.append(
            [
                equation.quit_derivative[variable]
                - equation.absorption_derivative[variable]
                - equation.survival_derivative[variable]
                * successor_value[player]
                for variable in active
            ]
        )
    active_inverse, active_determinant = inverse(active_jacobian)

    # -D_w is diagonal in the active-player equations, with diagonal entry
    # equal to that player's opponent-survival probability.
    negative_d_w = [
        [
            equation.survival if player == coordinate else ZERO
            for coordinate in range(N)
        ]
        for equation, player in zip(opponent, active)
    ]
    hazard_derivative = multiply(active_inverse, negative_d_w)

    phase = phase_data(root)
    result = identity(N)
    for row in range(N):
        for column in range(N):
            result[row][column] = result[row][column] * phase.survival
            for active_index, variable in enumerate(active):
                coefficient = (
                    phase.immediate_derivative[row][variable]
                    + phase.survival_derivative[variable]
                    * successor_value[row]
                )
                result[row][column] = (
                    result[row][column]
                    + coefficient * hazard_derivative[active_index][column]
                )
    return result, active_determinant


def distance_from_zero(value: Interval) -> Fraction:
    assert value.high < 0 or 0 < value.low
    return min(abs(value.low), abs(value.high))


def certify_return(
    certificate: ReducedCertificateData,
) -> tuple[Fraction, Fraction, Matrix]:
    hazard_box = tuple(
        Interval(value - RADIUS, value + RADIUS)
        for value in certificate.hazard_center
    )
    roots, values, _ = reconstructed_cyclic_values(hazard_box, certificate)

    result = identity(N)
    minimum_active_determinant_gap: Fraction | None = None
    # Starting from V^0, apply T_(M_10), T_(M_9), ..., T_(M_0).
    for phase_index in range(PERIOD - 1, -1, -1):
        phase_jacobian, active_determinant = predecessor_jacobian(
            roots[phase_index],
            values[(phase_index + 1) % PERIOD],
            certificate.support_word[phase_index],
        )
        determinant_gap = distance_from_zero(active_determinant)
        if (
            minimum_active_determinant_gap is None
            or determinant_gap < minimum_active_determinant_gap
        ):
            minimum_active_determinant_gap = determinant_gap
        result = multiply(phase_jacobian, result)

    assert minimum_active_determinant_gap is not None
    row_sums = [
        sum((entry.abs_upper() for entry in row), Fraction(0))
        for row in result
    ]
    maximum_row_sum = max(row_sums)
    assert maximum_row_sum < 1
    return minimum_active_determinant_gap, maximum_row_sum, result


def main() -> None:
    for certificate in (
        BASE_REDUCED_CERTIFICATE,
        NEARBY_REDUCED_CERTIFICATE,
        SUPPORT_TEN_REDUCED_CERTIFICATE,
    ):
        determinant_gap, return_row_sum, _ = certify_return(certificate)
        print(f"exact predecessor-return interval certificate passed: {certificate.name}")
        print(
            "minimum active-chart determinant distance from zero ~= "
            f"{float(determinant_gap):.6e}"
        )
        print(
            "maximum return-Jacobian interval row sum ~= "
            f"{float(return_row_sum):.6e}"
        )


if __name__ == "__main__":
    main()
