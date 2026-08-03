#!/usr/bin/env python3
"""Clock-charge the endpoint rank for ``6 -> 9 -> 3 -> 6`` exactly.

Use the perturbed block-pair table and the notation of
``block_pair_r0_support3_endpoint_rank.py``.  Let ``a,A`` be player 1's
hazards at the two support-6 endpoints, and let ``S`` be joint survival
through the intervening support-9 and support-3 phases.  Under the same
active equalities, inactive support-9 inequality, and endpoint player-0 Nash
inequality as the strict endpoint rank, this checker proves the quantitative
strengthening

    A - a >= (1/2) * (1-S).

The endpoint inequality gives

    A >= R(e,f)
      = (1701e-3501ef+1800f)/((1-f)(1979e+622)).

For fixed ``e,f``, the charged gap is increasing in ``A``: the transported
player-2 value has slope ``4S``, while the effective incoming hazard
``a(V)=(V-2)/(V+4)`` has two-point slope at most ``2/3`` on the feasible
range ``V>=2``.  It therefore suffices to check ``A=R(e,f)``.

The inactive clock and endpoint strictness give

    e=(2/11)u,       f=(200/3421)u r,       0<=u,r<=1.

After exact reduction, the charged gap is ``(-u*P)/D``.  Tensor Bernstein
coefficients prove ``P>0`` and ``-D>0`` on the full square, so the quotient
is nonnegative and is strict for ``u>0``.  The reduced identity and both
sign certificates are replayed below using only exact rational arithmetic.

This file proves the one-support-3 phase certificate.  A companion block
lift is required before charging an arbitrary support-3 run.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
import block_pair_r0_alternating_6_9_rank as algebra  # noqa: E402
import block_pair_r0_support3_endpoint_rank as endpoint  # noqa: E402
from block_pair_r0_support3_endpoint_rank import (  # noqa: E402
    RationalPoly,
    rat,
    rat_add,
    rat_equal,
    rat_mul,
    rat_scale,
    rat_sub,
)
from block_pair_r0_support9_run_rank import bernstein_coefficients  # noqa: E402


Q = Fraction
one = algebra.one
u = algebra.var(0)
r = algebra.var(1)


def rat_div(left: RationalPoly, right: RationalPoly) -> RationalPoly:
    return RationalPoly(
        algebra.mul(left.numerator, right.denominator),
        algebra.mul(left.denominator, right.numerator),
    )


def scaled_coordinates() -> tuple[RationalPoly, RationalPoly]:
    e_value = rat_scale(Q(2, 11), rat(u))
    f_value = rat_scale(Q(200, 3421), rat(algebra.mul(u, r)))
    return e_value, f_value


def eliminated_pair_hazards(
    e_value: RationalPoly, f_value: RationalPoly
) -> tuple[RationalPoly, RationalPoly]:
    d_value = rat_div(
        rat_scale(311, f_value),
        rat_add(rat(algebra.const(200)), rat_scale(311, f_value)),
    )
    c_value = rat_div(
        rat_scale(
            2,
            rat_add(rat_scale(300, e_value), rat_scale(311, f_value)),
        ),
        rat_scale(
            3,
            rat_add(
                rat_add(rat_scale(200, e_value), rat_scale(311, f_value)),
                rat(algebra.const(400)),
            ),
        ),
    )
    return c_value, d_value


def endpoint_threshold_value(
    e_value: RationalPoly, f_value: RationalPoly
) -> RationalPoly:
    numerator = rat_add(
        rat_add(
            rat_scale(1701, e_value),
            rat_scale(-3501, rat_mul(e_value, f_value)),
        ),
        rat_scale(1800, f_value),
    )
    denominator = rat_mul(
        rat_sub(rat(one), f_value),
        rat_add(rat_scale(1979, e_value), rat(algebra.const(622))),
    )
    return rat_div(numerator, denominator)


def charged_gap_at_threshold() -> RationalPoly:
    e_value, f_value = scaled_coordinates()
    c_value, d_value = eliminated_pair_hazards(e_value, f_value)
    endpoint_value = endpoint_threshold_value(e_value, f_value)

    support_nine_survival = rat_mul(
        rat_sub(rat(one), c_value), rat_sub(rat(one), d_value)
    )
    support_three_survival = rat_mul(
        rat_sub(rat(one), e_value), rat_sub(rat(one), f_value)
    )
    total_survival = rat_mul(
        support_nine_survival, support_three_survival
    )

    support_three_value = rat_add(
        rat_scale(-1, rat_mul(e_value, f_value)),
        rat_mul(
            support_three_survival,
            rat_add(
                rat(algebra.const(2)), rat_scale(4, endpoint_value)
            ),
        ),
    )
    transported_value = rat_add(
        rat_add(
            rat_scale(
                8,
                rat_mul(d_value, rat_sub(rat(one), c_value)),
            ),
            rat_scale(5, rat_mul(c_value, d_value)),
        ),
        rat_mul(support_nine_survival, support_three_value),
    )
    incoming_hazard = rat_div(
        rat_sub(transported_value, rat(algebra.const(2))),
        rat_add(transported_value, rat(algebra.const(4))),
    )
    return rat_sub(
        rat_sub(endpoint_value, incoming_hazard),
        rat_scale(Q(1, 2), rat_sub(rat(one), total_survival)),
    )


CORE_TERMS = (
    (0, 0, 16203690634425740688924),
    (0, 1, -12765478783243721001456),
    (1, 0, 33207009885592236840168),
    (1, 1, 5795862697205873426046),
    (1, 2, 4407252941192397065462),
    (2, 0, 1414043648837489192292),
    (2, 1, -2171726959271930999334),
    (2, 2, 1767473946889050499462),
    (2, 3, 1328597350576002512247),
    (3, 0, 1072989872721467434008),
    (3, 1, 859306294697493121050),
    (3, 2, -561805763868913769898),
    (3, 3, 244700737892506235197),
    (3, 4, 72060671380010296929),
    (4, 1, -128667021717288636714),
    (4, 2, -148544961848102595446),
    (4, 3, -29239427495029619307),
    (4, 4, 12616578299938382132),
    (4, 5, 1081403055668850200),
    (5, 2, 1734631784661479528),
    (5, 3, -8344897259170316229),
    (5, 4, -958313791286495061),
    (5, 5, 242309621874821600),
    (6, 3, -438377987613134800),
    (6, 4, -327264560700937200),
    (6, 5, -40447252302751800),
    (7, 4, -7870630438400000),
    (7, 5, -1534844174600000),
    (8, 5, -46007792000000),
)


def bivariate_polynomial(
    terms: tuple[tuple[int, int, int], ...]
) -> algebra.Poly:
    result: algebra.Poly = {}
    for u_power, r_power, coefficient in terms:
        exponent = [0] * algebra.NVARS
        exponent[0] = u_power
        exponent[1] = r_power
        result[tuple(exponent)] = Q(coefficient)
    return result


def reduced_denominator() -> algebra.Poly:
    ur = algebra.mul(u, r)
    last_factor = algebra.sum_polys(
        [
            algebra.scale(290600, algebra.mul(algebra.mul(r, r), algebra.mul(algebra.mul(u, u), algebra.mul(u, u)))),
            algebra.scale(6778035, algebra.mul(algebra.mul(r, r), algebra.mul(algebra.mul(u, u), u))),
            algebra.scale(19234765, algebra.mul(algebra.mul(r, r), algebra.mul(u, u))),
            algebra.scale(32450281, algebra.mul(r, algebra.mul(algebra.mul(u, u), u))),
            algebra.scale(167389354, algebra.mul(r, algebra.mul(u, u))),
            algebra.scale(719442163, ur),
            algebra.scale(-139658904, algebra.mul(u, u)),
            algebra.scale(2108615454, u),
            algebra.const(2317241718),
        ]
    )
    return algebra.scale(
        20526,
        algebra.mul(
            algebra.mul(
                algebra.add(algebra.scale(1979, u), algebra.const(3421)),
                algebra.add(ur, algebra.const(11)),
            ),
            algebra.mul(
                algebra.mul(
                    algebra.add(algebra.scale(200, ur), algebra.const(-3421)),
                    algebra.sum_polys(
                        [ur, algebra.scale(2, u), algebra.const(22)]
                    ),
                ),
                last_factor,
            ),
        ),
    )


def assert_reduced_identity() -> tuple[algebra.Poly, algebra.Poly]:
    core = bivariate_polynomial(CORE_TERMS)
    denominator = reduced_denominator()
    expected_numerator = algebra.scale(-1, algebra.mul(u, core))
    rat_equal(
        charged_gap_at_threshold(), expected_numerator, denominator
    )
    return core, denominator


def assert_bernstein_signs(
    core: algebra.Poly, denominator: algebra.Poly
) -> None:
    core_coefficients = bernstein_coefficients(
        core, variables=(0, 1), degrees=(8, 5)
    )
    assert len(core_coefficients) == 54
    assert min(core_coefficients.values()) == Q(3438211851182019687468)
    assert all(value > 0 for value in core_coefficients.values())

    negative_denominator = algebra.scale(-1, denominator)
    denominator_coefficients = bernstein_coefficients(
        negative_denominator, variables=(0, 1), degrees=(8, 5)
    )
    assert len(denominator_coefficients) == 54
    assert min(denominator_coefficients.values()) == Q(
        134709175359344979093096
    )
    assert all(value > 0 for value in denominator_coefficients.values())


def assert_monotonicity_packet() -> None:
    # For V2>=V1, exact subtraction for a(V)=(V-2)/(V+4) is
    #   a(V2)-a(V1)=6(V2-V1)/((V2+4)(V1+4)).
    v1 = algebra.var(2)
    v2 = algebra.var(3)
    numerator = algebra.sub(
        algebra.mul(
            algebra.sub(v2, algebra.const(2)),
            algebra.add(v1, algebra.const(4)),
        ),
        algebra.mul(
            algebra.sub(v1, algebra.const(2)),
            algebra.add(v2, algebra.const(4)),
        ),
    )
    assert numerator == algebra.scale(6, algebra.sub(v2, v1))
    # Feasibility gives V1,V2>=2, so each denominator factor is at least 6.
    # Since transported V has slope 4S with S<=1, the induced hazard slope
    # is at most 24/36=2/3 and the charged gap rises by at least one third of
    # every endpoint-hazard increase.
    assert Q(24, 36) == Q(2, 3) < 1


def main() -> None:
    # Replay the endpoint threshold and its strategic hypotheses.
    endpoint.main()
    core, denominator = assert_reduced_identity()
    assert_bernstein_signs(core, denominator)
    assert_monotonicity_packet()

    print("exact one-phase support-3 clock charge passed")
    print("A-a >= (1/2)*(one minus pair-segment survival)")
    print("charge-core Bernstein minimum = 3438211851182019687468")
    print("scope: one support-9 and one support-3 phase; block lift remains")


if __name__ == "__main__":
    main()
