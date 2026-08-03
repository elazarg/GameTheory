/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.FiniteProductFlowKinematics

/-!
# The two-state product-flow regression

This file formalizes the exact two-state Stay/Go calculation that separates
first active positive cut balance from later signed residual balance.

At state `u`, Go has probability `ε²`, Stay loops at `u`, and Go moves to an
absorbing state `v`.  The initial law gives each state mass `1/2`.  The exact
discounted stock at `u` and the rare `u → v` flux are

`d(ε) = 1 / (2 * (1 + ε - ε²))`,

`F(ε) = (1 - ε) * d(ε) * ε²`.

The cut equation is `ε d + F = ε / 2`.  After subtracting its first-order
part and dividing by `ε²`, the reset-stock residual is strictly negative and
the rare outgoing flux is strictly positive; the two terms cancel exactly.
Thus the second-scale equation is signed, not a new positive balance law.
-/

set_option autoImplicit false

namespace Math
namespace Probability
namespace TwoStateProductFlowRegression

noncomputable section

/-- The nonconstant factor in the resolvent denominator. -/
def denominator (ε : ℝ) : ℝ :=
  1 + ε - ε ^ 2

/-- Discounted occupation stock of the Stay/Go state `u`. -/
def stock (ε : ℝ) : ℝ :=
  1 / (2 * denominator ε)

/-- Discounted edge flux from `u` to the absorbing state `v`. -/
def rareFlux (ε : ℝ) : ℝ :=
  (1 - ε) * stock ε * ε ^ 2

/-- The resolvent denominator is positive at every genuine discount. -/
theorem denominator_pos {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    0 < denominator ε := by
  have hproduct : 0 < ε * (1 - ε) :=
    mul_pos hε (sub_pos.mpr hεone)
  unfold denominator
  nlinarith

theorem denominator_ne_zero {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    denominator ε ≠ 0 :=
  ne_of_gt (denominator_pos hε hεone)

theorem stock_pos {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    0 < stock ε := by
  unfold stock
  exact one_div_pos.mpr
    (mul_pos zero_lt_two (denominator_pos hε hεone))

theorem rareFlux_pos {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    0 < rareFlux ε := by
  unfold rareFlux
  exact mul_pos (mul_pos (sub_pos.mpr hεone) (stock_pos hε hεone))
    (sq_pos_of_pos hε)

/-- Exact discounted regression at `u`: reset inflow plus the Stay self-loop
reconstructs its stock. -/
theorem stock_balance {ε : ℝ} (hdenominator : denominator ε ≠ 0) :
    stock ε = ε / 2 +
      (1 - ε) * (1 - ε ^ 2) * stock ε := by
  unfold stock
  field_simp [hdenominator]
  unfold denominator
  ring

/-- Exact cut balance for `{u}`. -/
theorem cut_balance {ε : ℝ} (hdenominator : denominator ε ≠ 0) :
    ε * stock ε + rareFlux ε = ε / 2 := by
  unfold rareFlux stock
  field_simp [hdenominator]
  unfold denominator
  ring

/-- Exact normalized second-order stock formula.  Its value tends to `1` as
`ε` tends to zero. -/
theorem stock_second_normalized {ε : ℝ}
    (hε : ε ≠ 0) (hdenominator : denominator ε ≠ 0) :
    (stock ε - 1 / 2 + ε / 2) / ε ^ 2 =
      (2 - ε) / (2 * denominator ε) := by
  unfold stock
  field_simp [hε, hdenominator]
  unfold denominator
  ring

/-- Exact third-order remainder after the first three stock coefficients
`1/2 - ε/2 + ε²`. -/
theorem stock_expansion_remainder {ε : ℝ}
    (hdenominator : denominator ε ≠ 0) :
    stock ε - (1 / 2 - ε / 2 + ε ^ 2) =
      ε ^ 3 * (2 * ε - 3) / (2 * denominator ε) := by
  unfold stock
  field_simp [hdenominator]
  unfold denominator
  ring

/-- Exact normalized rare outgoing flux.  Its value tends to `1/2` as `ε`
tends to zero. -/
theorem rareFlux_second_normalized {ε : ℝ}
    (hε : ε ≠ 0) :
    rareFlux ε / ε ^ 2 =
      (1 - ε) / (2 * denominator ε) := by
  unfold rareFlux stock
  field_simp [hε]

/-- Exact fourth-order remainder after the first two rare-flux coefficients
`ε²/2 - ε³`. -/
theorem rareFlux_expansion_remainder {ε : ℝ}
    (hdenominator : denominator ε ≠ 0) :
    rareFlux ε - (ε ^ 2 / 2 - ε ^ 3) =
      ε ^ 4 * (3 - 2 * ε) / (2 * denominator ε) := by
  unfold rareFlux stock
  field_simp [hdenominator]
  unfold denominator
  ring

/-- The reset-stock term has a negative second-order residual. -/
theorem resetStock_second_normalized {ε : ℝ}
    (hε : ε ≠ 0) (hdenominator : denominator ε ≠ 0) :
    (ε * stock ε - ε / 2) / ε ^ 2 =
      (ε - 1) / (2 * denominator ε) := by
  unfold stock
  field_simp [hε, hdenominator]
  unfold denominator
  ring

theorem resetStock_second_normalized_neg {ε : ℝ}
    (hε : 0 < ε) (hεone : ε < 1) :
    (ε * stock ε - ε / 2) / ε ^ 2 < 0 := by
  rw [resetStock_second_normalized (ne_of_gt hε)
    (denominator_ne_zero hε hεone)]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hεone)
    (mul_pos zero_lt_two (denominator_pos hε hεone))

theorem rareFlux_second_normalized_pos {ε : ℝ}
    (hε : 0 < ε) (hεone : ε < 1) :
    0 < rareFlux ε / ε ^ 2 := by
  exact div_pos (rareFlux_pos hε hεone) (sq_pos_of_pos hε)

/-- At the newly visible `ε²` scale, the positive rare flux and the negative
reset-stock residual cancel exactly. -/
theorem second_scale_signed_cancellation {ε : ℝ}
    (hε : ε ≠ 0) (hdenominator : denominator ε ≠ 0) :
    (ε * stock ε - ε / 2) / ε ^ 2 +
        rareFlux ε / ε ^ 2 = 0 := by
  rw [resetStock_second_normalized hε hdenominator,
    rareFlux_second_normalized hε]
  ring

end

end TwoStateProductFlowRegression
end Probability
end Math
