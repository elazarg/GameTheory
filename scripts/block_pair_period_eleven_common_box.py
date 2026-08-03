#!/usr/bin/env python3
"""Exact finite-memory full-shift certificate for three K11 returns.

This checker addresses the common-box/full-shift probe suggested in item 75
of the proof-mining report.  A single convex phase-zero rectangle suffers
severe interval-correlation loss.  The exact replacement certified here is a
finite-memory graph: there are 27 rational boxes ``Q_(a,b,c)`` indexed by
three-letter words over ``{10,11,14}``, and all 81 edges

    R_a(Q_(b,c,d)) subset interior(Q_(a,b,c))

are valid.  Each ``R_a`` propagates its selected predecessor charts in the
functional order

    T_10, T_9, ..., T_0.

The rational charts (supports 7, 9, 10, and 14) are evaluated directly.  The
selected roots of the quadratic support-11 and support-13 charts are enclosed
by a parameter-uniform interval Newton step.  Correlated centered mean-value
forms enclose chart images and true chart derivatives without trusting
sampled points or independent phase boxes.

For every directed edge the checker proves:

* every selected chart exists on the full propagated successor box and its
  active hazards stay strictly between zero and one;
* every inactive Quit-minus-Continue difference is strictly negative;
* the eleven-chart return maps the full source box into the interior of the
  target box;
* every player has opponent-cycle survival strictly below one; and
* the true four-dimensional return Jacobian has infinity norm below one.

All certification arithmetic uses ``Fraction`` intervals.  The 27 guide
centers are embedded terminating rationals.  Floating point is used only to
choose a candidate root of a scalar quadratic; interval Newton validates that
candidate before it is used.  The single convex box from the report is not
refuted by this checker; it is unnecessary for the graph-directed conclusion.

This is an external exact certificate, not a Lean theorem.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this assertion-based exact certificate must not run under python -O"
    )

from hashlib import sha256
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import sqrt
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_period_eleven_certificate import (  # noqa: E402
    BASE_REDUCED_CERTIFICATE,
    NEARBY_REDUCED_CERTIFICATE,
    SUPPORT_TEN_REDUCED_CERTIFICATE,
    N,
    ONE,
    PERIOD,
    TERMINAL,
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
    multiply,
    predecessor_jacobian,
    reciprocal,
)


VectorBox = tuple[Interval, ...]

CERTIFICATE_BY_LABEL = {
    "10": SUPPORT_TEN_REDUCED_CERTIFICATE,
    "11": BASE_REDUCED_CERTIFICATE,
    "14": NEARBY_REDUCED_CERTIFICATE,
}

ALPHABET = ("10", "11", "14")
CONTEXT_RADIUS = Fraction(2, 10**6)
SAFE_OPPONENT_BLOCK_BOUND = Fraction(18481, 200000)  # 0.092405
PAYOFF_ABS_BOUND = max(
    abs(payoff)
    for row in TERMINAL.values()
    for payoff in row
)
EXPECTED_LIVE_STAGE_BOUND = Fraction(PERIOD) / (
    1 - SAFE_OPPONENT_BLOCK_BOUND
)
FINITE_HORIZON_GAIN_CONSTANT = (
    2 * PAYOFF_ABS_BOUND * EXPECTED_LIVE_STAGE_BOUND
)
assert PAYOFF_ABS_BOUND == 10

# These are deliberately terminating rational guide centers, not asserted
# roots.  The all-box edge checks below are the certificate.
CONTEXT_CENTER_TEXT = {
    ("10", "10", "10"): ("-1.8554498835084622", "1.4811905931508814", "2.0775687096704880", "3.9571791513022211"),
    ("10", "10", "11"): ("-1.8554498266095288", "1.4811909128765229", "2.0775685544835301", "3.9571784297825953"),
    ("10", "10", "14"): ("-1.8554521312243104", "1.4811781785251736", "2.0775748291311806", "3.9572071874231517"),
    ("10", "11", "10"): ("-1.8554481395282559", "1.4812121263406516", "2.0775640858940140", "3.9571339419352528"),
    ("10", "11", "11"): ("-1.8554480754157875", "1.4812125438327336", "2.0775639114826092", "3.9571330157213611"),
    ("10", "11", "14"): ("-1.8554506688167986", "1.4811959580493980", "2.0775709550784314", "3.9571698409446351"),
    ("10", "14", "10"): ("-1.8555244990735035", "1.4803549360395231", "2.0777600510490370", "3.9589234101823613"),
    ("10", "14", "11"): ("-1.8555244103865484", "1.4803554939122842", "2.0777598169444753", "3.9589221877909814"),
    ("10", "14", "14"): ("-1.8555279848485684", "1.4803333461621180", "2.0777692427899092", "3.9589707501173831"),
    ("11", "10", "10"): ("-1.8564600999865795", "1.4807857214680298", "2.0790388103375515", "3.9553604322915396"),
    ("11", "10", "11"): ("-1.8564600341831937", "1.4807860424254377", "2.0790386434662984", "3.9553597326858346"),
    ("11", "10", "14"): ("-1.8564627592069922", "1.4807732324573023", "2.0790454791214361", "3.9553874993117052"),
    ("11", "11", "10"): ("-1.8564630789132248", "1.4808051887111713", "2.0790411430980897", "3.9553071335898210"),
    ("11", "11", "11"): ("-1.8564630287420598", "1.4808055974747123", "2.0790409906346343", "3.9553061900765287"),
    ("11", "11", "14"): ("-1.8564651518157947", "1.4807893246082852", "2.0790472838407762", "3.9553435526980316"),
    ("11", "14", "10"): ("-1.8563546630396994", "1.4800276817013122", "2.0789654880638574", "3.9574157986679581"),
    ("11", "14", "11"): ("-1.8563545978478010", "1.4800282269015288", "2.0789652898711410", "3.9574145420606075"),
    ("11", "14", "14"): ("-1.8563573358884986", "1.4800065438618260", "2.0789734299321836", "3.9574642884621752"),
    ("14", "10", "10"): ("-1.8146925242793418", "1.5036516824346227", "2.0183064134311725", "4.0243284809443187"),
    ("14", "10", "11"): ("-1.8146925375335163", "1.5036519818890501", "2.0183063286905384", "4.0243276303033404"),
    ("14", "10", "14"): ("-1.8146921424298223", "1.5036400005575021", "2.0183099360137902", "4.0243613753861880"),
    ("14", "11", "10"): ("-1.8147026563913729", "1.5036677723737441", "2.0183169868507533", "4.0242626480456634"),
    ("14", "11", "11"): ("-1.8147027182776233", "1.5036681437699787", "2.0183169547174814", "4.0242614958886457"),
    ("14", "11", "14"): ("-1.8147004246512618", "1.5036533210216301", "2.0183185199027903", "4.0243071017913391"),
    ("14", "14", "10"): ("-1.8143117731285640", "1.5030233264755042", "2.0179171384738691", "4.0268653490920827"),
    ("14", "14", "11"): ("-1.8143118591179784", "1.5030238197974424", "2.0179171026822284", "4.0268638134602668"),
    ("14", "14", "14"): ("-1.8143086352717709", "1.5030041565337449", "2.0179188552879945", "4.0269245858844122"),
}

CONTEXT_CENTERS = {
    context: tuple(Fraction(value) for value in values)
    for context, values in CONTEXT_CENTER_TEXT.items()
}

EXPECTED_CONTEXTS = frozenset(product(ALPHABET, repeat=3))
assert frozenset(CONTEXT_CENTERS) == EXPECTED_CONTEXTS

# A scalar chart root is never remotely this far from its certified cycle
# center on the common box.  The wide seed is intentional: interval Newton,
# not this empirical observation, must prove the selected branch exists.
QUADRATIC_ROOT_RADIUS = Fraction(1, 8)
POINT_ROOT_RADIUS = Fraction(1, 10**12)
ROUNDING_POWER = 80


def midpoint(value: Interval) -> Fraction:
    return (value.low + value.high) / 2


def outward_round(value: Interval) -> Interval:
    """Round outward to a fixed dyadic grid, preserving exact enclosure."""

    denominator = 1 << ROUNDING_POWER
    low_integer = (value.low.numerator * denominator) // value.low.denominator
    high_scaled_numerator = value.high.numerator * denominator
    high_integer = -((-high_scaled_numerator) // value.high.denominator)
    return Interval(
        Fraction(low_integer, denominator),
        Fraction(high_integer, denominator),
    )


def round_vector(vector: VectorBox) -> VectorBox:
    return tuple(outward_round(value) for value in vector)


def round_matrix(matrix: Matrix) -> Matrix:
    return [[outward_round(value) for value in row] for row in matrix]


def divide(numerator: Interval, denominator: Interval) -> Interval:
    return numerator * reciprocal(denominator)


def square(value: Interval) -> Interval:
    return value * value


def row_times_vector(row: list[Interval], vector: VectorBox) -> Interval:
    assert len(row) == len(vector)
    result = ZERO
    for coefficient, value in zip(row, vector):
        result = result + coefficient * value
    return result


def matrix_times_vector(matrix: Matrix, vector: VectorBox) -> VectorBox:
    return tuple(row_times_vector(row, vector) for row in matrix)


def quadratic_coefficients(
    support: int, successor: VectorBox
) -> tuple[Interval, Interval, Interval]:
    w0, w1, w2, w3 = successor
    if support == 13:
        a = w0 * w2.scale(2) - w0.scale(29) + w2.scale(36) - w3.scale(30) - Interval.point(192)
        b = -(w0 * w2).scale(4) + w0.scale(33) - w2.scale(52) + w3.scale(10) + Interval.point(194)
        c = (w0 * w2).scale(2) - w0.scale(4) + w2.scale(16) - Interval.point(32)
        return a, b, c
    if support == 11:
        a = (w0 * w1).scale(2) - w0.scale(10) - w1.scale(18) - w3.scale(27) - Interval.point(18)
        b = -(w0 * w1).scale(4) + w0.scale(32) + w1.scale(68) + w3.scale(108) - Interval.point(16)
        c = (w0 * w1).scale(2) - w0.scale(22) - w1.scale(50) - w3.scale(81) + Interval.point(226)
        return a, b, c
    raise AssertionError(f"support {support} is not quadratic")


def quadratic_value(
    coefficients: tuple[Interval, Interval, Interval], z: Interval
) -> Interval:
    a, b, c = coefficients
    return a * square(z) + b * z + c


def quadratic_derivative(
    coefficients: tuple[Interval, Interval, Interval], z: Interval
) -> Interval:
    a, b, _ = coefficients
    return a * z.scale(2) + b


def approximate_quadratic_root(
    support: int, successor: VectorBox, reference: Fraction
) -> Fraction:
    point = tuple(Interval.point(midpoint(value)) for value in successor)
    a_i, b_i, c_i = quadratic_coefficients(support, point)
    a = float(a_i.low)
    b = float(b_i.low)
    c = float(c_i.low)
    discriminant = b * b - 4 * a * c
    assert discriminant > 0
    candidates = ((-b + sqrt(discriminant)) / (2 * a), (-b - sqrt(discriminant)) / (2 * a))
    selected = min(candidates, key=lambda value: abs(value - float(reference)))
    return Fraction(str(selected))


def interval_newton_quadratic(
    support: int,
    successor: VectorBox,
    reference: Fraction,
    point_only: bool = False,
) -> Interval:
    candidate = approximate_quadratic_root(support, successor, reference)
    radius = POINT_ROOT_RADIUS if point_only else QUADRATIC_ROOT_RADIUS
    domain = Interval(candidate - radius, candidate + radius)
    coefficients = quadratic_coefficients(support, successor)
    derivative = quadratic_derivative(coefficients, domain)
    assert derivative.high < 0 or 0 < derivative.low
    value_at_candidate = quadratic_value(
        coefficients, Interval.point(candidate)
    )
    newton = Interval.point(candidate) - divide(value_at_candidate, derivative)
    assert domain.low < newton.low <= newton.high < domain.high
    # A second exact refinement makes subsequent centered forms much tighter.
    refined_derivative = quadratic_derivative(coefficients, newton)
    assert refined_derivative.high < 0 or 0 < refined_derivative.low
    refined = Interval.point(candidate) - divide(
        value_at_candidate, refined_derivative
    )
    assert domain.low < refined.low <= refined.high < domain.high
    return outward_round(refined)


def rational_hazard(support: int, successor: VectorBox) -> VectorBox:
    w0, w1, w2, w3 = successor
    if support == 7:
        middle = w0.scale(3) + w2.scale(5) + Interval.point(8)
        coefficient = (
            w0.scale(18) - w1 * w2 - w1.scale(22)
            + w2.scale(38) + Interval.point(224)
        )
        return (
            -divide((w1 - Interval.point(2)) * (w2 + Interval.point(22)), coefficient),
            divide(w2 - Interval.point(2), w2 + Interval.point(4)),
            divide(
                (w0.scale(2) + w2.scale(3) - Interval.point(2)).scale(3),
                middle.scale(2),
            ),
            ZERO,
        )
    if support == 14:
        middle = w1.scale(5) + w2.scale(3) + Interval.point(2)
        numerator = w1 * w3.scale(5) - w1.scale(20) - w2.scale(12) + w3.scale(26) - Interval.point(8)
        coefficient = w1 * w3.scale(5) - w1.scale(65) - w2.scale(30) + w3.scale(26) - Interval.point(98)
        return (
            ZERO,
            divide(w1.scale(5) + w2.scale(6) - Interval.point(22), middle.scale(2)),
            divide(numerator, coefficient),
            divide(w1 - Interval.point(2), w1 + Interval.point(4)),
        )
    if support == 9:
        return (
            divide(w3 - Interval.point(2), w3 + Interval.point(4)),
            ZERO,
            ZERO,
            ONE + divide(Interval.point(2), w0),
        )
    if support == 10:
        return (
            ZERO,
            divide(w3 - Interval.point(2), w3),
            ZERO,
            divide(w1 - Interval.point(2), w1 + Interval.point(4)),
        )
    raise AssertionError(f"support {support} does not have a rational chart")


def quadratic_hazard(
    support: int,
    successor: VectorBox,
    reference: Fraction,
    point_only: bool = False,
) -> VectorBox:
    w0, w1, w2, _ = successor
    z = interval_newton_quadratic(
        support, successor, reference, point_only=point_only
    )
    if support == 13:
        x0 = divide(
            w2 * z - w2 - z.scale(7) + Interval.point(2),
            (w2 - Interval.point(2)) * (z - ONE),
        )
        x2 = divide(
            w0 * z - w0 - Interval.point(2),
            w0 * z - w0 + z.scale(12) - Interval.point(6),
        )
        return x0, ZERO, x2, z
    if support == 11:
        x0 = divide(
            w1 * z - w1 + z.scale(4) + Interval.point(2),
            w1 * z - w1 - z.scale(5) + Interval.point(11),
        )
        x1 = divide(
            w0 * z - w0 - Interval.point(2),
            w0 * z - w0 - z.scale(3) + Interval.point(7),
        )
        return x0, x1, ZERO, z
    raise AssertionError(f"support {support} is not quadratic")


def selected_hazard(
    support: int,
    successor: VectorBox,
    reference: Fraction,
    point_only: bool = False,
) -> VectorBox:
    if support in (11, 13):
        return quadratic_hazard(
            support, successor, reference, point_only=point_only
        )
    return rational_hazard(support, successor)


@dataclass(frozen=True)
class ChartResult:
    predecessor: VectorBox
    jacobian: Matrix
    root: VectorBox
    minimum_inactive_gap: Fraction
    minimum_active_determinant_gap: Fraction


def chart(
    support: int,
    successor: VectorBox,
    reference_root: tuple[Fraction, ...],
    center: tuple[Fraction, ...] | None = None,
) -> ChartResult:
    reference = reference_root[3]
    root = round_vector(selected_hazard(support, successor, reference))
    for player in range(N):
        if bit(support, player):
            assert 0 < root[player].low <= root[player].high < 1
        else:
            assert root[player].is_zero()

    if center is None:
        center = tuple(midpoint(value) for value in successor)
    center_successor = tuple(Interval.point(value) for value in center)
    center_root = round_vector(selected_hazard(
        support, center_successor, reference, point_only=support in (11, 13)
    ))
    center_phase = phase_data(center_root)
    center_value = tuple(
        immediate + center_phase.survival * value
        for immediate, value in zip(
            center_phase.immediate, center_successor
        )
    )

    jacobian, determinant = predecessor_jacobian(root, successor, support)
    jacobian = round_matrix(jacobian)
    determinant_gap = distance_from_zero(determinant)
    predecessor = round_vector(center_value)

    inactive_gap: Fraction | None = None
    for player in range(N):
        data = opponent_data(root, player)
        difference = (
            data.quit_value
            - data.absorption
            - data.survival * successor[player]
        )
        if bit(support, player):
            # The interval must at least be consistent with the exact active
            # identities used to define this chart.
            assert difference.low <= 0 <= difference.high
        else:
            assert difference.high < 0
            gap = -difference.high
            inactive_gap = gap if inactive_gap is None else min(inactive_gap, gap)

    # Full support has no inactive constraint; it does not occur in these words.
    assert inactive_gap is not None
    return ChartResult(
        predecessor,
        jacobian,
        root,
        inactive_gap,
        determinant_gap,
    )


@dataclass(frozen=True)
class ReturnResult:
    image: VectorBox
    derivative: Matrix
    minimum_inactive_gap: Fraction
    minimum_active_determinant_gap: Fraction
    opponent_products: tuple[Interval, ...]


def selected_return(
    initial: VectorBox, certificate: ReducedCertificateData
) -> ReturnResult:
    initial_center = tuple(midpoint(value) for value in initial)
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
        successor = round_vector(tuple(
            Interval.point(point) + error + linear
            for point, error, linear in zip(
                center,
                center_error,
                matrix_times_vector(derivative, initial_displacement),
            )
        ))
        support = certificate.support_word[phase_index]
        result = chart(
            support,
            successor,
            certificate.root_center[phase_index],
            center=center,
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
        new_derivative = round_matrix(
            multiply(result.jacobian, derivative)
        )
        propagated_error = matrix_times_vector(
            result.jacobian, center_error
        )
        new_center = tuple(midpoint(value) for value in result.predecessor)
        center_error = round_vector(tuple(
            value - Interval.point(point) + error
            for value, point, error in zip(
                result.predecessor, new_center, propagated_error
            )
        ))
        center = new_center
        derivative = new_derivative

    assert minimum_inactive_gap is not None
    assert minimum_determinant_gap is not None
    image = round_vector(tuple(
        Interval.point(point) + error + linear
        for point, error, linear in zip(
            center,
            center_error,
            matrix_times_vector(derivative, initial_displacement),
        )
    ))
    return ReturnResult(
        image,
        derivative,
        minimum_inactive_gap,
        minimum_determinant_gap,
        tuple(opponent_products),
    )


def infinity_norm(matrix: Matrix) -> Fraction:
    return max(
        sum((entry.abs_upper() for entry in row), Fraction(0))
        for row in matrix
    )


def context_box(context: tuple[str, str, str]) -> VectorBox:
    center = CONTEXT_CENTERS[context]
    return tuple(
        Interval(value - CONTEXT_RADIUS, value + CONTEXT_RADIUS)
        for value in center
    )


def context_box_sup_separation(
    left: tuple[str, str, str], right: tuple[str, str, str]
) -> Fraction:
    """Exact l-infinity distance between two equal-radius axis boxes."""

    return max(
        max(abs(x - y) - 2 * CONTEXT_RADIUS, Fraction(0))
        for x, y in zip(CONTEXT_CENTERS[left], CONTEXT_CENTERS[right])
    )


def certify_context_separation() -> tuple[Fraction, Fraction, int]:
    pairs = tuple(combinations(sorted(CONTEXT_CENTERS), 2))
    first_symbol = tuple(
        context_box_sup_separation(left, right)
        for left, right in pairs
        if left[0] != right[0]
    )
    second_symbol = tuple(
        context_box_sup_separation(left, right)
        for left, right in pairs
        if left[0] == right[0] and left[1] != right[1]
    )
    overlap_pairs = tuple(
        (left, right)
        for left, right in pairs
        if context_box_sup_separation(left, right) == 0
    )
    minimum_first = min(first_symbol)
    minimum_second = min(second_symbol)
    assert 0 < minimum_first
    assert 0 < minimum_second
    assert len(overlap_pairs) == 9
    assert all(
        left[:2] == right[:2]
        and {left[2], right[2]} == {"10", "11"}
        for left, right in overlap_pairs
    )
    return minimum_first, minimum_second, len(overlap_pairs)


def strict_image_slack(image: VectorBox, target: VectorBox) -> Fraction:
    return min(
        min(inner.low - outer.low, outer.high - inner.high)
        for inner, outer in zip(image, target)
    )


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def interval_text(value: Interval) -> str:
    return f"{fraction_text(value.low)}:{fraction_text(value.high)}"


@dataclass
class GraphSummary:
    edges: int = 0
    minimum_inactive_gap: Fraction | None = None
    minimum_determinant_gap: Fraction | None = None
    maximum_return_norm: Fraction = Fraction(0)
    maximum_opponent_product: Fraction = Fraction(0)
    minimum_image_slack: Fraction | None = None


def update_graph_summary(
    summary: GraphSummary,
    result: ReturnResult,
    slack: Fraction,
) -> None:
    summary.edges += 1
    summary.minimum_inactive_gap = (
        result.minimum_inactive_gap
        if summary.minimum_inactive_gap is None
        else min(summary.minimum_inactive_gap, result.minimum_inactive_gap)
    )
    summary.minimum_determinant_gap = (
        result.minimum_active_determinant_gap
        if summary.minimum_determinant_gap is None
        else min(
            summary.minimum_determinant_gap,
            result.minimum_active_determinant_gap,
        )
    )
    summary.maximum_return_norm = max(
        summary.maximum_return_norm, infinity_norm(result.derivative)
    )
    summary.maximum_opponent_product = max(
        summary.maximum_opponent_product,
        *(value.high for value in result.opponent_products),
    )
    summary.minimum_image_slack = (
        slack
        if summary.minimum_image_slack is None
        else min(summary.minimum_image_slack, slack)
    )


def hash_edge(
    transcript: object,
    target_context: tuple[str, str, str],
    source_context: tuple[str, str, str],
    source: VectorBox,
    target: VectorBox,
    result: ReturnResult,
) -> None:
    assert hasattr(transcript, "update")
    lines = [
        f"target={','.join(target_context)}",
        f"source={','.join(source_context)}",
        "source_box=" + ",".join(interval_text(value) for value in source),
        "target_box=" + ",".join(interval_text(value) for value in target),
        "image=" + ",".join(interval_text(value) for value in result.image),
        "derivative=" + ";".join(
            ",".join(interval_text(value) for value in row)
            for row in result.derivative
        ),
        "opponent="
        + ",".join(interval_text(value) for value in result.opponent_products),
        "inactive=" + fraction_text(result.minimum_inactive_gap),
        "determinant="
        + fraction_text(result.minimum_active_determinant_gap),
    ]
    transcript.update(("|".join(lines) + "\n").encode("ascii"))


# Filled after the first deterministic exact replay; kept as a regression
# against changes to centers, chart orientation, rounding, or edge order.
EXPECTED_TRANSCRIPT_SHA256 = (
    "cb0450723132c3458a25e729ed5dc5dd64da4af5417e8fbdea38d57866766238"
)


def certify_context_graph() -> tuple[GraphSummary, str]:
    summary = GraphSummary()
    transcript = sha256()
    for target_context in product(ALPHABET, repeat=3):
        current, second, third = target_context
        target = context_box(target_context)
        certificate = CERTIFICATE_BY_LABEL[current]
        for appended in ALPHABET:
            source_context = (second, third, appended)
            source = context_box(source_context)
            result = selected_return(source, certificate)
            return_norm = infinity_norm(result.derivative)
            assert return_norm < 1
            assert all(
                opponent.high < 1
                for opponent in result.opponent_products
            )
            slack = strict_image_slack(result.image, target)
            assert 0 < slack
            update_graph_summary(summary, result, slack)
            hash_edge(
                transcript,
                target_context,
                source_context,
                source,
                target,
                result,
            )
        print(
            "certified all incoming edges for context "
            + "-".join(target_context),
            flush=True,
        )

    assert summary.edges == 3**4
    assert summary.minimum_inactive_gap is not None
    assert summary.minimum_determinant_gap is not None
    assert summary.minimum_image_slack is not None
    assert summary.maximum_opponent_product < SAFE_OPPONENT_BLOCK_BOUND
    digest = transcript.hexdigest()
    if EXPECTED_TRANSCRIPT_SHA256 != "TO_BE_FILLED":
        assert digest == EXPECTED_TRANSCRIPT_SHA256
    return summary, digest


def main() -> None:
    summary, digest = certify_context_graph()
    first_separation, second_separation, overlap_count = (
        certify_context_separation()
    )
    print("exact memory-three graph-directed full-shift certificate passed")
    print(f"context boxes = {len(CONTEXT_CENTERS)}, directed edges = {summary.edges}")
    print(f"uniform box radius = {CONTEXT_RADIUS}")
    print(
        "minimum inactive gap ~= "
        f"{float(summary.minimum_inactive_gap):.9f}"
    )
    print(
        "minimum active determinant gap ~= "
        f"{float(summary.minimum_determinant_gap):.9e}"
    )
    print(
        "minimum directed-image slack ~= "
        f"{float(summary.minimum_image_slack):.9e}"
    )
    print(
        "maximum true return infinity norm ~= "
        f"{float(summary.maximum_return_norm):.9f}"
    )
    print(
        "maximum opponent-cycle survival ~= "
        f"{float(summary.maximum_opponent_product):.9f}"
    )
    print(
        "safe opponent-block bound = "
        f"{SAFE_OPPONENT_BLOCK_BOUND}"
    )
    print(
        "uniform expected-live-stage bound = "
        f"{EXPECTED_LIVE_STAGE_BOUND}"
    )
    print(
        "uniform N-stage deviation-gain bound = "
        f"{FINITE_HORIZON_GAIN_CONSTANT}/N"
    )
    print(
        "minimum different-first-symbol box separation ~= "
        f"{float(first_separation):.9f}"
    )
    print(
        "minimum same-first/different-second box separation ~= "
        f"{float(second_separation):.9e}"
    )
    print(f"overlapping context-box pairs = {overlap_count}")
    print(f"transcript SHA-256 = {digest}")


if __name__ == "__main__":
    main()
