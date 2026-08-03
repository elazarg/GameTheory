#!/usr/bin/env python3
"""Exact direct replay of the three mixed period-22 cycles from Question 119.

The memory-three full-shift checker already implies existence of every mixed
periodic word.  This smaller regression independently starts from the three
published rational centers, composes the two selected period-eleven returns in
functional order, and checks word-specific trapping cubes, contraction,
strategic margins, opponent absorption, and separation from the pure-word
traps.

All proof arithmetic is ``Fraction`` interval arithmetic supplied by
``block_pair_period_eleven_common_box``.  Floating point appears only in human
readable output; the imported interval-Newton routine validates every selected
quadratic root exactly.  This script is an external certificate, not a Lean
theorem.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError(
        "this verifier relies on assertions; do not run Python with -O"
    )

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_period_eleven_common_box as common  # noqa: E402


RADIUS = Fraction(1, 10**8)
OPPONENT_PRODUCT_BOUND = Fraction(8151, 10**6)


@dataclass(frozen=True)
class MixedWord:
    first: str
    second: str
    first_center: tuple[Fraction, ...]
    second_center: tuple[Fraction, ...]
    derivative_bound: Fraction
    image_radius_bound: Fraction


def vector(*coordinates: str) -> tuple[Fraction, ...]:
    return tuple(Fraction(coordinate) for coordinate in coordinates)


WORDS = (
    MixedWord(
        "10",
        "11",
        vector(
            "-1.8554481381601413583891664619440168108",
            "1.4812121317953193100533978291797422917",
            "2.0775640823139855183059240168708863165",
            "3.9571339295426345082307942752247766498",
        ),
        vector(
            "-1.8564600365580336613873522893984988602",
            "1.4807860350767856912420886080089512989",
            "2.0790386488323763351606785119660598970",
            "3.9553597473310079439784695733067785030",
        ),
        Fraction(143, 10**5),
        Fraction(562, 10**13),
    ),
    MixedWord(
        "10",
        "14",
        vector(
            "-1.8555245638938090139180225730469760584",
            "1.4803546682913068313668114906794282609",
            "2.0777602183928427036379446641079301418",
            "3.9589240105024078626999730567161401453",
        ),
        vector(
            "-1.8146920958204841497663145667764077864",
            "1.5036403626889476667553941105828591427",
            "2.0183097330229485108898744579078591291",
            "4.0243604807450666920400575793869011182",
        ),
        Fraction(159, 10**5),
        Fraction(554, 10**13),
    ),
    MixedWord(
        "11",
        "14",
        vector(
            "-1.8563547033893387395515377199903419636",
            "1.4800278465928266446960794262801672987",
            "2.0789655351190177306432469267067929986",
            "3.9574153243282400127758615630522456835",
        ),
        vector(
            "-1.8147003866743969973602891676221486952",
            "1.5036537017703367020343030086606151301",
            "2.0183183241680450264358488447038481767",
            "4.0243061375457684378865972005300593172",
        ),
        Fraction(1371, 10**6),
        Fraction(418, 10**13),
    ),
)


CERTIFICATES = {
    "10": common.SUPPORT_TEN_REDUCED_CERTIFICATE,
    "11": common.BASE_REDUCED_CERTIFICATE,
    "14": common.NEARBY_REDUCED_CERTIFICATE,
}


PURE_CENTERS = {
    "10": vector(
        "-1.8554498835", "1.4811905932", "2.0775687097", "3.9571791513"
    ),
    "11": vector(
        "-1.8564630287", "1.4808055975", "2.0790409906", "3.9553061901"
    ),
    "14": vector(
        "-1.8143086353", "1.5030041565", "2.0179188553", "4.0269245859"
    ),
}


EXPECTED_TRANSCRIPT_SHA256 = (
    "cb0838beeb53f72e24f8d46980a42db1e6f7c4440c7036ea1a92e76e73e1f3c2"
)


def centered_box(
    center: tuple[Fraction, ...], radius: Fraction
) -> common.VectorBox:
    return tuple(
        common.Interval(coordinate - radius, coordinate + radius)
        for coordinate in center
    )


def contained_strictly(
    inner: common.VectorBox, outer: common.VectorBox
) -> bool:
    return all(
        outside.low < inside.low <= inside.high < outside.high
        for inside, outside in zip(inner, outer)
    )


def disjoint_in_every_coordinate(
    left: common.VectorBox, right: common.VectorBox
) -> bool:
    return all(
        first.high < second.low or second.high < first.low
        for first, second in zip(left, right)
    )


def maximum_radius(
    box: common.VectorBox, center: tuple[Fraction, ...]
) -> Fraction:
    return max(
        max(abs(interval.low - coordinate), abs(interval.high - coordinate))
        for interval, coordinate in zip(box, center)
    )


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def replay(word: MixedWord) -> tuple[str, ...]:
    first_box = centered_box(word.first_center, RADIUS)
    second_box = centered_box(word.second_center, RADIUS)

    # Temporal word W_first W_second means R_second acts first in the
    # predecessor composition F = R_first o R_second.
    second_result = common.selected_return(
        first_box, CERTIFICATES[word.second]
    )
    first_result = common.selected_return(
        second_result.image, CERTIFICATES[word.first]
    )
    derivative = common.multiply(
        first_result.derivative, second_result.derivative
    )
    derivative_norm = common.infinity_norm(derivative)
    image_radius = maximum_radius(first_result.image, word.first_center)

    assert contained_strictly(second_result.image, second_box)
    assert contained_strictly(first_result.image, first_box)
    assert derivative_norm < word.derivative_bound
    assert image_radius < word.image_radius_bound
    assert second_result.minimum_inactive_gap > 0
    assert first_result.minimum_inactive_gap > 0
    assert second_result.minimum_active_determinant_gap > 0
    assert first_result.minimum_active_determinant_gap > 0

    opponent_products = tuple(
        left.high * right.high
        for left, right in zip(
            second_result.opponent_products, first_result.opponent_products
        )
    )
    assert all(product < OPPONENT_PRODUCT_BOUND for product in opponent_products)

    pure_first = centered_box(PURE_CENTERS[word.first], RADIUS)
    pure_second = centered_box(PURE_CENTERS[word.second], RADIUS)
    assert disjoint_in_every_coordinate(first_box, pure_first)
    assert disjoint_in_every_coordinate(second_result.image, pure_second)

    label = f"{word.first}-{word.second}"
    print(
        f"exact mixed cycle passed: {label}; "
        f"norm ~= {float(derivative_norm):.9f}; "
        f"image radius ~= {float(image_radius):.9e}; "
        f"opponent max ~= {float(max(opponent_products)):.9f}"
    )
    return (
        label,
        fraction_text(derivative_norm),
        fraction_text(image_radius),
        *(fraction_text(product) for product in opponent_products),
    )


def main() -> None:
    transcript = "\n".join("|".join(replay(word)) for word in WORDS)
    digest = sha256(transcript.encode("ascii")).hexdigest()
    assert digest == EXPECTED_TRANSCRIPT_SHA256
    print("exact Q119 mixed-cycle replay passed")
    print(f"transcript SHA-256 = {digest}")


if __name__ == "__main__":
    main()
