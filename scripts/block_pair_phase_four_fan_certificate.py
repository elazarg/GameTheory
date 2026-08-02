#!/usr/bin/env python3
"""Exact phase-four support-fan certificate for the block-pair K11 cycles.

All three certified cycles share phase 5 with support 11, while phase 4 has
support 10, 11, or 14.  This script gives that observation a precise local
scope.  It checks that the three exact phase-5 continuation boxes lie in one
explicit rational box ``W`` and proves that, for every continuation value in
``W``, no other nonempty phase-4 support can satisfy active indifference and
inactive weak continuation.

For fixed ``w_i``, player ``i``'s Quit-minus-Continue difference is
multi-affine in the opponents' hazards; it is also affine in ``w_i``.  Its
range on a rational rectangle has extrema among the finitely many corners.
The exclusion checker recursively bisects the closed active-hazard cube.  A
cell is discarded when one active equation has a strict sign or one inactive
player strictly prefers Quit throughout the cell.  Exact ``Fraction``
arithmetic and exhaustion of the stack give a finite certificate; using
closed hazard cubes only strengthens exclusion of the required open active
chambers.

Every leaf is serialized in deterministic depth-first order and hashed.  The
full-support transcript digest is a regression against accidentally weakening
that hardest exclusion.  No floating-point calculation is trusted.

The support-10 sheet itself is rational.  For ``x = (0,b,0,d)``,

    d = (w_1 - 2) / (w_1 + 4),
    b = (w_3 - 2) / w_3.

The script checks its hazard range and both inactive inequalities throughout
``W``.  The result is local to ``W`` and does not assert that an arbitrary
continuation value enters it or that every value in ``W`` lies on all three
selected sheets.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_period_eleven_certificate import (  # noqa: E402
    BASE_REDUCED_CERTIFICATE,
    N,
    NEARBY_REDUCED_CERTIFICATE,
    SUPPORT_TEN_REDUCED_CERTIFICATE,
    ZERO,
    Interval,
    bit,
    opponent_data,
    reconstructed_cyclic_values,
)
from block_pair_stationary_certificate import TERMINAL  # noqa: E402


RADIUS = Fraction(1, 10**8)
PHASE = 4
SUCCESSOR_PHASE = 5

# Coordinates are deliberately simple and substantially wider than the three
# reconstructed exact phase-5 boxes.
CONTINUATION_BOX = (
    (Fraction(-29, 10), Fraction(-289, 100)),
    (Fraction(69, 25), Fraction(1381, 500)),
    (Fraction(391, 100), Fraction(79, 20)),
    (Fraction(107, 50), Fraction(2143, 1000)),
)

FAN_MASKS = frozenset({10, 11, 14})
EXCLUDED_MASKS = tuple(
    mask for mask in range(1, 1 << N) if mask not in FAN_MASKS
)

# Filled from the deterministic exact replay below.  Changing the box,
# splitting rule, payoff table, or leaf test must change this fingerprint.
EXPECTED_MASK_FIFTEEN_DIGEST = (
    "de26f13bb272c639f08d108e450158aab6203c539ae44da5b214e1368c825d73"
)


def local_difference(
    player: int, root: tuple[Fraction, ...], successor_value: Fraction
) -> Fraction:
    """Exact Quit-minus-Continue difference at one point."""

    result = Fraction(0)
    for opponents in range(1 << N):
        if bit(opponents, player):
            continue
        probability = Fraction(1)
        for opponent in range(N):
            if opponent == player:
                continue
            probability *= (
                root[opponent]
                if bit(opponents, opponent)
                else 1 - root[opponent]
            )
        quit_payoff = TERMINAL[opponents | (1 << player)][player]
        continue_payoff = (
            successor_value
            if opponents == 0
            else TERMINAL[opponents][player]
        )
        result += probability * (quit_payoff - continue_payoff)
    return result


HazardBox = tuple[tuple[Fraction, Fraction], ...]
ExclusionReason = tuple[str, int, Fraction, Fraction]


def difference_range(player: int, box: HazardBox) -> tuple[Fraction, Fraction]:
    varying_opponents = [
        opponent
        for opponent in range(N)
        if opponent != player and box[opponent][0] != box[opponent][1]
    ]
    values = []
    for corner in range(1 << len(varying_opponents)):
        root = [interval[0] for interval in box]
        for index, opponent in enumerate(varying_opponents):
            root[opponent] = box[opponent][bit(corner, index)]
        for successor_value in CONTINUATION_BOX[player]:
            values.append(
                local_difference(player, tuple(root), successor_value)
            )
    return min(values), max(values)


def cell_exclusion_reason(
    mask: int, box: HazardBox
) -> ExclusionReason | None:
    for player in range(N):
        lower, upper = difference_range(player, box)
        if bit(mask, player):
            # Active indifference needs zero in this range.
            if 0 < lower or upper < 0:
                return "active", player, lower, upper
        else:
            # An inactive player must weakly prefer Continue: D_i <= 0.
            if 0 < lower:
                return "inactive", player, lower, upper
    return None


def split_widest_active(mask: int, box: HazardBox) -> tuple[HazardBox, HazardBox]:
    active = [player for player in range(N) if bit(mask, player)]
    player = max(active, key=lambda index: box[index][1] - box[index][0])
    lower, upper = box[player]
    assert lower < upper
    midpoint = (lower + upper) / 2
    left = list(box)
    right = list(box)
    left[player] = (lower, midpoint)
    right[player] = (midpoint, upper)
    return tuple(left), tuple(right)


@dataclass(frozen=True)
class ExclusionResult:
    nodes: int
    leaves: int
    maximum_depth: int
    reason_counts: tuple[tuple[str, int, int], ...]
    digest: str


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def exclude_mask(mask: int) -> ExclusionResult:
    assert mask in EXCLUDED_MASKS
    initial_box: HazardBox = tuple(
        (Fraction(0), Fraction(1))
        if bit(mask, player)
        else (Fraction(0), Fraction(0))
        for player in range(N)
    )
    stack = [(initial_box, "")]
    transcript = sha256()
    nodes = 0
    leaves = 0
    maximum_depth = 0
    reason_counts: Counter[tuple[str, int]] = Counter()

    while stack:
        box, path = stack.pop()
        nodes += 1
        assert nodes < 10_000
        reason = cell_exclusion_reason(mask, box)
        if reason is not None:
            kind, player, lower, upper = reason
            leaves += 1
            maximum_depth = max(maximum_depth, len(path))
            reason_counts[(kind, player)] += 1
            transcript.update(
                (
                    f"{path}|{kind}|{player}|{fraction_text(lower)}|"
                    f"{fraction_text(upper)}\n"
                ).encode("ascii")
            )
            continue

        left, right = split_widest_active(mask, box)
        # Push right first so that lexicographic left/0 paths are replayed first.
        stack.append((right, path + "1"))
        stack.append((left, path + "0"))

    return ExclusionResult(
        nodes,
        leaves,
        maximum_depth,
        tuple(
            (kind, player, count)
            for (kind, player), count in sorted(reason_counts.items())
        ),
        transcript.hexdigest(),
    )


def positive_reciprocal(value: Interval) -> Interval:
    assert 0 < value.low <= value.high
    return Interval(Fraction(1) / value.high, Fraction(1) / value.low)


def quotient(numerator: Interval, denominator: Interval) -> Interval:
    return numerator * positive_reciprocal(denominator)


def certify_support_ten_chart() -> tuple[
    Interval, Interval, tuple[Interval, Interval]
]:
    w = tuple(Interval(lower, upper) for lower, upper in CONTINUATION_BOX)
    b = quotient(w[3] - Interval.point(2), w[3])
    d = quotient(w[1] - Interval.point(2), w[1] + Interval.point(4))
    assert 0 < b.low <= b.high < 1
    assert 0 < d.low <= d.high < 1
    root = (ZERO, b, ZERO, d)
    inactive_differences = []
    for player in (0, 2):
        data = opponent_data(root, player)
        difference = (
            data.quit_value
            - data.absorption
            - data.survival * w[player]
        )
        assert difference.high < 0
        inactive_differences.append(difference)
    return b, d, tuple(inactive_differences)


def assert_successor_boxes_contained() -> dict[str, tuple[Interval, ...]]:
    result = {}
    for certificate in (
        BASE_REDUCED_CERTIFICATE,
        NEARBY_REDUCED_CERTIFICATE,
        SUPPORT_TEN_REDUCED_CERTIFICATE,
    ):
        hazard_box = tuple(
            Interval(value - RADIUS, value + RADIUS)
            for value in certificate.hazard_center
        )
        _, values, _ = reconstructed_cyclic_values(hazard_box, certificate)
        phase_five = values[SUCCESSOR_PHASE]
        for player, value in enumerate(phase_five):
            lower, upper = CONTINUATION_BOX[player]
            assert lower <= value.low <= value.high <= upper
        result[certificate.name] = phase_five
    assert len(result) == 3
    return result


def main() -> None:
    phase_five_boxes = assert_successor_boxes_contained()
    assert len(EXCLUDED_MASKS) == 12
    assert FAN_MASKS.isdisjoint(EXCLUDED_MASKS)
    assert FAN_MASKS | frozenset(EXCLUDED_MASKS) == frozenset(range(1, 1 << N))

    excluded = {mask: exclude_mask(mask) for mask in EXCLUDED_MASKS}
    assert len(excluded) + len(FAN_MASKS) == (1 << N) - 1
    full_support = excluded[15]
    assert full_support.digest == EXPECTED_MASK_FIFTEEN_DIGEST

    b, d, inactive_differences = certify_support_ten_chart()

    print("exact phase-four support-fan exclusion passed")
    print(
        "continuation box = "
        + " x ".join(f"[{lower},{upper}]" for lower, upper in CONTINUATION_BOX)
    )
    print("certified phase-five boxes contained = " + ",".join(phase_five_boxes))
    print("admissible support candidates = 10,11,14")
    print(
        "excluded-mask subdivision nodes = "
        + ",".join(f"{mask}:{excluded[mask].nodes}" for mask in EXCLUDED_MASKS)
    )
    print(f"support-10 x1 range ~= [{float(b.low):.6f},{float(b.high):.6f}]")
    print(f"support-10 x3 range ~= [{float(d.low):.6f},{float(d.high):.6f}]")
    print(
        "support-10 inactive upper bounds ~= "
        + ",".join(
            f"player{player}:{float(difference.high):.6f}"
            for player, difference in zip((0, 2), inactive_differences)
        )
    )
    print(f"mask-15 subdivision leaves = {full_support.leaves}")
    print(f"mask-15 maximum depth = {full_support.maximum_depth}")
    print(f"mask-15 leaf reasons = {full_support.reason_counts}")
    print(f"mask-15 transcript SHA-256 = {full_support.digest}")


if __name__ == "__main__":
    main()
