#!/usr/bin/env python3
"""Exact Möbius transport and rank falsifiers for support-3/9 blocks.

For an active player at a pair support, the opponent hazard transports across
adjacent pair phases by ``F_k(x)=k*x/(1-x)``.  In the perturbed five-mask
core the shared-player-0 coordinate gives

    9->9: k=200/411,       9->3: k=200/311,
    3->3: k=900/311,       3->9: k=300/137.

Consequences checked exactly here:

* every positive hazard grows through each support-3 self transition;
* every nonempty block ``9->3+->9`` strictly raises the support-9 player-3
  hazard, already by the factor 60000/42607>1 for one support-3 phase;
* this scalar rank does not survive arbitrary support-9 waiting: the exact
  active-coordinate path ``9->3->9->9`` starting at hazard 1/100 ends below
  1/100;
* a shared-coordinate cycle with support word ``9^m 3^n`` can exist only if

      (200/411)^(m-1) (200/311) (900/311)^(n-1) (300/137) < 1.

  The direct 9/3 cycle fails this test, whereas 9,9,3 passes it.  The latter
  has the unique positive shared-coordinate cycle displayed below.

These are active-coordinate statements only.  The exact rational reversal
does not assert inactive Nash inequalities or a full Bellman path.  Indeed
numerical searches currently reject the 9,9,3 active roots on other hazards;
that observation is not part of this certificate.  Any full block theorem
must therefore use inactive values or a vector rank, not this scalar alone.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("this exact checker must not run under python -O")

from fractions import Fraction
from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parent))
from block_pair_r0_constant_pair_support import COEFFICIENTS  # noqa: E402


Q = Fraction
ONE = Q(1)

K99 = Q(200, 411)
K93 = Q(200, 311)
K33 = Q(900, 311)
K39 = Q(300, 137)


def mobius(coefficient: Fraction, hazard: Fraction) -> Fraction:
    assert coefficient > 0 and 0 < hazard < 1
    return coefficient * hazard / (1 - hazard)


def reciprocal_composition(
    coefficients: tuple[Fraction, ...],
) -> tuple[Fraction, Fraction]:
    """Return alpha,beta for ``1/x_out=alpha/x_in-beta``."""

    alpha = ONE
    beta = Q(0)
    for coefficient in coefficients:
        # y'=(y-1)/k.
        alpha, beta = alpha / coefficient, (beta + 1) / coefficient
    return alpha, beta


def positive_cycle_hazard(
    coefficients: tuple[Fraction, ...],
) -> Fraction | None:
    alpha, beta = reciprocal_composition(coefficients)
    if alpha <= 1:
        return None
    result = (alpha - 1) / beta
    assert 0 < result < 1
    return result


def block_product(m: int, n: int) -> Fraction:
    assert m >= 1 and n >= 1
    return K99 ** (m - 1) * K93 * K33 ** (n - 1) * K39


def assert_payoff_coefficients() -> None:
    a01, b01 = COEFFICIENTS[0, 1]
    a03, b03 = COEFFICIENTS[0, 3]
    assert (a01, b01) == (Q(-9, 2), Q(-311, 200))
    assert (a03, b03) == (Q(-1), Q(-411, 200))
    assert a03 / b03 == K99
    assert a03 / b01 == K93
    assert a01 / b01 == K33
    assert a01 / b03 == K39


def assert_support_three_block_growth() -> None:
    assert K33 > 1
    assert K93 * K39 == Q(60000, 42607) > 1
    for length in range(1, 8):
        lower_factor = K93 * K33 ** (length - 1) * K39
        assert lower_factor > 1


def assert_exact_scalar_rank_reversal() -> None:
    start = Q(1, 100)
    at_three = mobius(K93, start)
    back_at_nine = mobius(K39, at_three)
    after_nine_wait = mobius(K99, back_at_nine)
    assert (start, at_three, back_at_nine, after_nine_wait) == (
        Q(1, 100),
        Q(200, 30789),
        Q(60000, 4190693),
        Q(4000000, 565904941),
    )
    assert back_at_nine > start
    assert after_nine_wait < start


def assert_cycle_product_fork() -> None:
    direct = block_product(1, 1)
    first_open = block_product(2, 1)
    assert direct == Q(60000, 42607) > 1
    assert first_open == Q(4000000, 5837159) < 1

    # Word 9,9,3 uses transition coefficients 99,93,39.  Its reciprocal
    # affine map has one positive fixed point because the product is below 1.
    coefficients = (K99, K93, K39)
    start = positive_cycle_hazard(coefficients)
    assert start == Q(5511477, 31512877)
    assert start is not None
    first_wait = mobius(K99, start)
    at_three = mobius(K93, first_wait)
    closed = mobius(K39, at_three)
    assert (first_wait, at_three, closed) == (
        Q(1837159, 17810959),
        Q(1837159, 24839259),
        start,
    )

    alpha, beta = reciprocal_composition(coefficients)
    assert alpha == Q(5837159, 4000000)
    assert beta == Q(31512877, 12000000)


def main() -> None:
    assert_payoff_coefficients()
    assert_support_three_block_growth()
    assert_exact_scalar_rank_reversal()
    assert_cycle_product_fork()

    print("exact support-3/9 Möbius block transport passed")
    print("every 9->3+->9 block raises the shared support-9 hazard")
    print("exact active-coordinate reversal exists after one extra 9 wait")
    print("direct 9/3 product > 1; 9,9,3 product = 4000000/5837159 < 1")
    print("scope: active coordinates only; inactive Nash/full Bellman remain")


if __name__ == "__main__":
    main()
