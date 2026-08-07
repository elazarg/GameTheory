/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Projective first-event Bellman packets

A discounted one-state Bellman equation has the scalar form

`v = (1 - ε) * (a + c * v)`.

Here `ε` is the discount-complement (the probability of an artificial
cemetery event), `c` is the probability of surviving the physical stage, and
`q = 1 - c` is the real absorption probability.  The first-event
denominator is

`D = ε + (1 - ε) * q = 1 - (1 - ε) * c`.

Normalizing by `D` gives two nonnegative projective weights

`ω₀ = ε / D`, `ω₁ = (1 - ε) * q / D`,

whose sum is one.  The Bellman equation becomes

`D * v = (1 - ε) * a`.

When `q > 0`, this is equivalently

`v = ω₁ * (a / q)`:

`a / q` is the payoff conditional on a real absorption event and `ω₀` is the
cemetery mass.  Keeping `ω₀` is the load-bearing compactification step in the
matching discount/absorption regime.
-/

noncomputable section

namespace Math

/-- Total first-event mass: artificial discount plus discounted real
absorption. -/
def projectiveFirstEventDenominator (ε q : ℝ) : ℝ :=
  ε + (1 - ε) * q

/-- Projective weight of the artificial discount/cemetery event. -/
def projectiveCemeteryWeight (ε q : ℝ) : ℝ :=
  ε / projectiveFirstEventDenominator ε q

/-- Projective weight of a real absorption event. -/
def projectiveAbsorptionWeight (ε q : ℝ) : ℝ :=
  (1 - ε) * q / projectiveFirstEventDenominator ε q

/-- The first-event denominator is positive whenever the discount-complement
is positive, at most one, and the real absorption mass is nonnegative. -/
theorem projectiveFirstEventDenominator_pos
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) :
    0 < projectiveFirstEventDenominator ε q := by
  unfold projectiveFirstEventDenominator
  have hsecond : 0 ≤ (1 - ε) * q :=
    mul_nonneg (sub_nonneg.mpr hε1) hq
  linarith

/-- The cemetery weight is nonnegative. -/
theorem projectiveCemeteryWeight_nonneg
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) :
    0 ≤ projectiveCemeteryWeight ε q := by
  unfold projectiveCemeteryWeight
  exact div_nonneg hε.le
    (projectiveFirstEventDenominator_pos hε hε1 hq).le

/-- The real-absorption weight is nonnegative. -/
theorem projectiveAbsorptionWeight_nonneg
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) :
    0 ≤ projectiveAbsorptionWeight ε q := by
  unfold projectiveAbsorptionWeight
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hε1) hq)
    (projectiveFirstEventDenominator_pos hε hε1 hq).le

/-- **Exact projective normalization.**  Cemetery and real-absorption weights
sum to one. -/
theorem projectiveCemeteryWeight_add_absorptionWeight
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 ≤ q) :
    projectiveCemeteryWeight ε q +
        projectiveAbsorptionWeight ε q = 1 := by
  have hD : projectiveFirstEventDenominator ε q ≠ 0 :=
    (projectiveFirstEventDenominator_pos hε hε1 hq).ne'
  unfold projectiveCemeteryWeight projectiveAbsorptionWeight
  field_simp [hD, projectiveFirstEventDenominator]

/-- **Exact Bellman balance after first-event normalization.** -/
theorem projectiveBellman_balance
    (ε q c a v : ℝ)
    (hq : q = 1 - c)
    (hrec : v = (1 - ε) * (a + c * v)) :
    projectiveFirstEventDenominator ε q * v = (1 - ε) * a := by
  unfold projectiveFirstEventDenominator
  rw [hq]
  linear_combination hrec

/-- With positive real absorption, the normalized Bellman value is the
real-absorption projective weight times the payoff conditional on absorption. -/
theorem projectiveBellman_value_eq_absorptionWeight_mul_conditional
    {ε q c a v : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq0 : 0 < q)
    (hq : q = 1 - c)
    (hrec : v = (1 - ε) * (a + c * v)) :
    v = projectiveAbsorptionWeight ε q * (a / q) := by
  have hDpos := projectiveFirstEventDenominator_pos hε hε1 hq0.le
  have hbalance := projectiveBellman_balance ε q c a v hq hrec
  calc
    v = ((1 - ε) * a) / projectiveFirstEventDenominator ε q := by
      apply (eq_div_iff hDpos.ne').2
      simpa [mul_comm] using hbalance
    _ = projectiveAbsorptionWeight ε q * (a / q) := by
      unfold projectiveAbsorptionWeight
      field_simp [hDpos.ne', hq0.ne']
      ring

end Math
