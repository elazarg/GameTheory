/-
# Normalized discounted real series

Game-free algebra for the normalized geometric sums used by deterministic and
monitored repeated-payoff semantics.
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheoryMath

/-- The normalized discounted sum of a real sequence. -/
abbrev normalizedDiscountedSum (discount : ℝ) (payoff : ℕ → ℝ) : ℝ :=
  (1 - discount) * ∑' t : ℕ, discount ^ t * payoff t

/-- Pointwise ordering passes through a normalized discounted sum whenever
both weighted series are summable and the discount lies in `[0, 1)`. -/
theorem normalizedDiscountedSum_le
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {first second : ℕ → ℝ}
    (hfirst : Summable fun t => discount ^ t * first t)
    (hsecond : Summable fun t => discount ^ t * second t)
    (hle : ∀ t, first t ≤ second t) :
    normalizedDiscountedSum discount first ≤
      normalizedDiscountedSum discount second := by
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hdiscount1.le)
  exact hfirst.tsum_le_tsum
    (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hdiscount0 t))
    hsecond

/-- Sufficient patience makes a fixed continuation margin dominate any bounded
one-period gain. -/
theorem exists_discountFactor_threshold_oneStep
    {gain margin : ℝ} (hgain : 0 ≤ gain) (hmargin : 0 < margin) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        (1 - discount) * gain < discount * margin := by
  let threshold : ℝ := gain / (gain + margin)
  have hdenominator : 0 < gain + margin := by linarith
  refine ⟨threshold, div_nonneg hgain hdenominator.le, ?_, ?_⟩
  · rw [div_lt_one hdenominator]
    linarith
  · intro discount hdiscount _
    have hmul : gain < discount * (gain + margin) :=
      (div_lt_iff₀ hdenominator).1 hdiscount
    nlinarith

end GameTheoryMath
