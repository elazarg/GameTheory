/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# All-Pay Auction

In an all-pay auction, every bidder pays their bid regardless of whether
they win. This models contests, lobbying, and rent-seeking.

## Main results

These lemmas record the elementary payoff inequalities used in an all-pay
auction model. They are arithmetic facts, not dominance or equilibrium
statements about a formal game object.

* `allPay_overbid_unprofitable` — both win and loss payoffs are negative when
  a nonnegative prize is overbid
* `allPay_winner_profit_of_lt` — `v - bid` is positive when `bid < v`
-/

namespace GameTheory

open Math.Probability

/-- If a nonnegative prize value `v` is overbid, both possible all-pay payoff
    expressions are negative. The bidder either:
    - Loses: pays `b > v` and gets nothing → payoff = `-b < 0`
    - Wins: pays `b > v` and gets `v` → payoff = `v - b < 0`
    A dominance conclusion additionally requires a formal allocation and
    tie-breaking model, which this arithmetic lemma does not provide. -/
theorem allPay_overbid_unprofitable (v b : ℝ) (hv : v ≥ 0) (hb : b > v) :
    (0 : ℝ) > v - b ∧ (0 : ℝ) > -b := by
  constructor <;> linarith

/-- The all-pay winner payoff `v - bid` is positive when the bid is below the
prize value. -/
theorem allPay_winner_profit_of_lt (v bid : ℝ) (hbid : bid < v) :
    v - bid > 0 := by linarith

/-- Compatibility form of `allPay_winner_profit_of_lt`. The positive-bid
hypothesis is unnecessary for the arithmetic conclusion. -/
theorem allPay_winner_profit (v bid : ℝ) (_hwin : bid > 0) (hbid : bid < v) :
    v - bid > 0 :=
  allPay_winner_profit_of_lt v bid hbid

/-- If the two payoff expressions are `v - b₁` and `-b₂`, strictly positive
bids make their sum strictly less than `v`. -/
theorem allPay_rent_dissipation (v b₁ b₂ : ℝ) (hb₁ : b₁ > 0) (hb₂ : b₂ > 0) :
    (v - b₁) + (-b₂) < v := by linarith

/-- The symmetric fair-tie payoff expression `v / 2 - b` is negative whenever
`b > v / 2`. This arithmetic fact alone is not an equilibrium theorem. -/
theorem allPay_symmetric_negative (v b : ℝ) (hb : b > v / 2) :
    v / 2 - b < 0 := by linarith

end GameTheory
