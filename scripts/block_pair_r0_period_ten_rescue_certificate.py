#!/usr/bin/env python3
"""Exact interval certificate for the perturbed block-pair period-ten rescue.

The perturbed table changes only

    r_0({0}) = -2 + 11/100 = -189/100.

It was introduced as a possible counterexample seed after the three familiar
period-eleven sheets left their support chambers.  This checker certifies that
the seed is nevertheless rescued by the support word

    (7, 7, 14, 14, 8, 10, 9, 13, 13, 7).

In particular, the old five-mask atlas was not exhaustive: the rescue uses
the omitted transition ``14 -> 8 -> 10 -> 9``.

The active system has a one-dimensional timing redundancy.  At phase 4 only
player 3 quits, and at phase 5 only players 1 and 3 quit.  The table has

    r_3({3}) = r_3({1,3}) = 2,    r_3({1}) = 0.

If ``b`` and ``e`` are the phase-5 hazards of players 1 and 3, respectively,
and ``z`` is player 3's phase-6 continuation value, then

    D_4^3 = 2 - [2e + (1-e)(1-b)z]
          = (1-e) [2 - (1-b)z]
          = (1-e) D_5^3.

Thus one active row is redundant.  We fix the phase-4 player-3 hazard to the
exact rational value 1/10, omit that redundant row, and certify the remaining
25-dimensional square system by exact rational Krawczyk inequalities.  The
displayed identity restores the omitted active equality.

The certified box also has strictly negative inactive Quit-minus-Continue
gaps and strictly contracting opponent-cycle products.  Together with exact
Bellman policy recursion, these are precisely the hypotheses of
``isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate_finite``
in ``QuittingPeriodicCompiler.lean``.  Consequently the exact root has zero
terminal exploitability and yields a uniform-equilibrium payoff.

Floating point is used only to generate the printed center.  Every accepted
claim is rechecked using ``Fraction`` interval arithmetic; the Decimal inverse
is merely a proposed rational preconditioner whose Krawczyk bounds are checked
from scratch.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_period_eleven_certificate as interval  # noqa: E402
import block_pair_stationary_certificate as polynomial  # noqa: E402


if not __debug__:
    raise SystemExit("refusing to run with Python assertions disabled")


PERIOD = 10
SUPPORT_WORD = (7, 7, 14, 14, 8, 10, 9, 13, 13, 7)
FIXED_SLOT = (4, 3)
FIXED_HAZARD = Fraction(1, 10)
OMITTED_ACTIVE_ROW = (4, 3)
RADIUS = Fraction(1, 10**10)


ROOT_CENTER_TEXT = (
    ("0.067098590243744746", "0.059688038283639298", "0.16922736271217112", "0"),
    ("0.0014502040621949843", "0.096114604381395477", "0.34446105215442679", "0"),
    ("0", "0.15390310343220387", "0.057574498506611338", "0.026471270638316093"),
    ("0", "0.22821082162965578", "0.079078017085194671", "0.087223009710480803"),
    ("0", "0", "0", "0.1"),
    ("0", "0.15857844186570075", "0", "0.21481864434648987"),
    ("0.094232457162923042", "0", "0", "0.10267981962732323"),
    ("0.16783052700733242", "0", "0.04677927466306013", "0.074736700520061594"),
    ("0.24549813211451116", "0", "0.018182815689941019", "0.0075252389012781277"),
    ("0.051132836359625004", "0.01389261877999971", "0.054597009729035112", "0"),
)


# Reuse the audited exact interval engine in a fresh process, with the shorter
# period and the one rational payoff perturbation installed before constructing
# the certificate data.  The imported module reads both globals dynamically.
interval.PERIOD = PERIOD
interval.TERMINAL = dict(interval.TERMINAL)
interval.TERMINAL[1] = (Fraction(-189, 100), 8, 0, 0)

CERTIFICATE = interval.make_reduced_certificate_data(
    "perturbed-period-ten-rescue", SUPPORT_WORD, ROOT_CENTER_TEXT
)
FIXED_INDEX = CERTIFICATE.hazard_index[FIXED_SLOT]
OMITTED_ROW_INDEX = CERTIFICATE.active_slots.index(OMITTED_ACTIVE_ROW)
FREE_CENTER = tuple(
    value
    for index, value in enumerate(CERTIFICATE.hazard_center)
    if index != FIXED_INDEX
)
FREE_SLOTS = tuple(
    slot
    for index, slot in enumerate(CERTIFICATE.active_slots)
    if index != FIXED_INDEX
)

assert len(CERTIFICATE.active_slots) == 26
assert len(FREE_CENTER) == len(FREE_SLOTS) == 25
assert CERTIFICATE.hazard_center[FIXED_INDEX] == FIXED_HAZARD


def lift_free_box(
    box: tuple[interval.Interval, ...], fixed: interval.Interval
) -> tuple[interval.Interval, ...]:
    """Insert the fixed phase-4 player-3 coordinate into a free box."""

    assert len(box) == len(FREE_CENTER)
    iterator = iter(box)
    result = tuple(
        fixed if index == FIXED_INDEX else next(iterator)
        for index in range(len(CERTIFICATE.hazard_center))
    )
    try:
        next(iterator)
    except StopIteration:
        pass
    else:
        raise AssertionError("free box contained unused coordinates")
    return result


def sliced_system_and_jacobian(
    box: tuple[interval.Interval, ...],
) -> tuple[tuple[interval.Interval, ...], tuple[interval.SparseRow, ...]]:
    """The 25 independent active rows on the exact rational slice."""

    full_box = lift_free_box(box, interval.Interval.point(FIXED_HAZARD))
    equations, jacobian = interval.reduced_system_and_jacobian(
        full_box, CERTIFICATE
    )
    sliced_equations = []
    sliced_jacobian = []
    for row_index, (equation, row) in enumerate(zip(equations, jacobian)):
        if row_index == OMITTED_ROW_INDEX:
            continue
        sliced_equations.append(equation)
        sliced_jacobian.append(
            {
                (column if column < FIXED_INDEX else column - 1): entry
                for column, entry in row.items()
                if column != FIXED_INDEX
            }
        )
    assert len(sliced_equations) == len(sliced_jacobian) == len(FREE_CENTER)
    return tuple(sliced_equations), tuple(sliced_jacobian)


def assert_redundant_active_row_identity() -> None:
    """Check the exact table facts and polynomial identity restoring row 4:3."""

    assert SUPPORT_WORD[4] == 1 << 3
    assert SUPPORT_WORD[5] == (1 << 1) | (1 << 3)
    assert interval.TERMINAL[1 << 3][3] == 2
    assert interval.TERMINAL[(1 << 1) | (1 << 3)][3] == 2
    assert interval.TERMINAL[1 << 1][3] == 0

    one = polynomial.const(1)
    two = polynomial.const(2)
    b = polynomial.X[1]
    e = polynomial.X[3]
    z = polynomial.X[0]
    one_sub_b = polynomial.sub(one, b)
    one_sub_e = polynomial.sub(one, e)
    phase_five_value = polynomial.add(
        polynomial.scale(2, e),
        polynomial.mul(polynomial.mul(one_sub_e, one_sub_b), z),
    )
    phase_four_difference = polynomial.sub(two, phase_five_value)
    phase_five_difference = polynomial.sub(
        two, polynomial.mul(one_sub_b, z)
    )
    assert phase_four_difference == polynomial.mul(
        one_sub_e, phase_five_difference
    )


def transcript_digest(
    preconditioner: list[list[Fraction]],
) -> tuple[str, int]:
    """Hash all deterministic rational witness data used by the certificate."""

    def text(value: Fraction) -> str:
        return interval.fraction_text(value)

    payload = {
        "version": 1,
        "terminal": [
            [mask, *[text(Fraction(value)) for value in interval.TERMINAL[mask]]]
            for mask in range(1, 1 << interval.N)
        ],
        "support_word": list(SUPPORT_WORD),
        "fixed_slot": list(FIXED_SLOT),
        "fixed_hazard": text(FIXED_HAZARD),
        "omitted_active_row": list(OMITTED_ACTIVE_ROW),
        "free_slots": [list(slot) for slot in FREE_SLOTS],
        "free_center": [text(value) for value in FREE_CENTER],
        "radius": text(RADIUS),
        "preconditioner": [
            [text(value) for value in row] for row in preconditioner
        ],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return sha256(canonical.encode("utf-8")).hexdigest(), len(
        canonical.encode("utf-8")
    )


def main() -> None:
    assert sys.argv[1:] == []
    assert_redundant_active_row_identity()

    (
        free_box,
        preconditioner,
        center_residual,
        defect_row_sum,
        inclusion_ratio,
    ) = interval.certify_system(
        FREE_CENTER,
        RADIUS,
        sliced_system_and_jacobian,
        preconditioner_precision=80,
    )

    # The broader interval around the fixed rational coordinate contains the
    # exact sliced root and lets the common strategic checker require genuine
    # positive-width intervals for every active hazard.
    strategic_box = lift_free_box(
        free_box,
        interval.Interval(FIXED_HAZARD - RADIUS, FIXED_HAZARD + RADIUS),
    )
    roots, values, joint_cycle = interval.reconstructed_cyclic_values(
        strategic_box, CERTIFICATE
    )
    (
        inactive_upper,
        opponent_cycle_upper,
        joint_cycle_upper,
    ) = interval.assert_strategic_inequalities_for(
        roots, values, CERTIFICATE
    )
    assert joint_cycle.high == joint_cycle_upper

    # This checks, using exact rational arithmetic at the supplied center, the
    # common-denominator orientation H = (1-rho)D and policy-value recursion
    # for all 26 active rows.  Krawczyk zeros 25 rows; the polynomial identity
    # above zeros the omitted row at the same exact root.
    assert interval.assert_reduced_orientation(CERTIFICATE) is None

    digest, payload_bytes = transcript_digest(preconditioner)
    phase_zero_value = values[0]

    print("exact perturbed block-pair period-ten rescue certificate passed")
    print("support word = " + ",".join(str(mask) for mask in SUPPORT_WORD))
    print("omitted-mask transition = 14 -> 8 -> 10 -> 9")
    print(f"slice dimension = {len(FREE_CENTER)}")
    print(f"fixed hazard phase 4/player 3 = {FIXED_HAZARD}")
    print(f"box radius = {RADIUS}")
    print(f"maximum center residual ~= {float(center_residual):.3e}")
    print(f"maximum ||I-AJ(X)|| row sum ~= {float(defect_row_sum):.3e}")
    print(f"maximum Krawczyk inclusion ratio ~= {float(inclusion_ratio):.3e}")
    print(
        "largest inactive Quit-minus-Continue upper bound ~= "
        f"{float(inactive_upper):.9f}"
    )
    print(
        "largest opponent-cycle survival upper bound ~= "
        f"{float(opponent_cycle_upper):.9f}"
    )
    print(f"joint-cycle survival upper bound ~= {float(joint_cycle_upper):.9f}")
    print(
        "phase-zero payoff enclosure ~= ("
        + ", ".join(
            f"[{float(value.low):.9f},{float(value.high):.9f}]"
            for value in phase_zero_value
        )
        + ")"
    )
    print("terminal exploitability = 0 (exact cyclic Bellman/Snell compiler)")
    print("perturbed table status = retired as a counterexample candidate")
    print(f"certificate SHA-256 = {digest}")
    print(f"certificate canonical payload bytes = {payload_bytes}")


if __name__ == "__main__":
    main()
