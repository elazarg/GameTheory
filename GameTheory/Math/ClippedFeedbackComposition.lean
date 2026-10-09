import GameTheory.Math.ClippedArithmetic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Clipped affine feedback without premature saturation

Adding the positive signal at half scale leaves room for the negative signal before doubling.
Three clipped affine steps therefore equal one projected signed update. Nonexpansiveness of
clipping propagates independent input errors and a common gate error to the final update.
-/

namespace GameTheory.Math
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Half-scale addition and subtraction followed by doubling implement projected feedback. -/
theorem clippedFeedback_three_steps (q θ aPlus aMinus : F)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp0 : 0 ≤ aPlus) (hp1 : aPlus ≤ 1) (hm0 : 0 ≤ aMinus) :
    max 0 (min 1 (2 * max 0 (min 1
      (max 0 (min 1 (q / 2 + θ / 2 * aPlus)) - θ / 2 * aMinus)))) =
      max 0 (min 1 (q + θ * (aPlus - aMinus))) := by
  have hh0 : 0 ≤ q / 2 + θ / 2 * aPlus :=
    add_nonneg (div_nonneg hq0 (by norm_num))
      (mul_nonneg (div_nonneg hθ0 (by norm_num)) hp0)
  have hprod : θ * aPlus ≤ 1 := by
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hp1)]
  have hh1 : q / 2 + θ / 2 * aPlus ≤ 1 := by linarith
  rw [unitClamp_eq_self hh0 hh1]
  have hraw : q / 2 + θ / 2 * aPlus - θ / 2 * aMinus ≤ 1 := by
    have hm := mul_nonneg (div_nonneg hθ0 (by norm_num : (0 : F) ≤ 2)) hm0
    linarith
  rw [min_eq_right hraw]
  have he : 2 * (q / 2 + θ / 2 * aPlus - θ / 2 * aMinus) =
      q + θ * (aPlus - aMinus) := by ring
  by_cases h : 0 ≤ q / 2 + θ / 2 * aPlus - θ / 2 * aMinus
  · rw [max_eq_right h, he]
  · have hr : q / 2 + θ / 2 * aPlus - θ / 2 * aMinus ≤ 0 := le_of_not_ge h
    have ht : q + θ * (aPlus - aMinus) ≤ 0 := by linarith
    rw [max_eq_left hr, mul_zero]
    have hc : max 0 (min 1 (q + θ * (aPlus - aMinus))) = 0 :=
      max_eq_left ((min_le_right _ _).trans ht)
    rw [hc]
    simp

private theorem abs_half_sub_le {a a' η : F} (h : |a' - a| ≤ η) :
    |a' / 2 - a / 2| ≤ η / 2 := by
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : F) < 2)]
  exact div_le_div_of_nonneg_right h (by norm_num)

private theorem abs_scaled_half_sub_le {a a' θ η : F} (hθ : 0 ≤ θ)
    (h : |a' - a| ≤ η) : |θ / 2 * a' - θ / 2 * a| ≤ θ / 2 * η := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg hθ (by norm_num))]
  exact mul_le_mul_of_nonneg_left h (div_nonneg hθ (by norm_num))

/-- Error propagation through the three literal clipped affine feedback steps. -/
theorem clippedFeedback_three_steps_error
    (q θ aPlus aMinus q' aPlus' aMinus' h s out ηq ηPlus ηMinus δ : F)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp0 : 0 ≤ aPlus) (hp1 : aPlus ≤ 1) (hm0 : 0 ≤ aMinus)
    (hq : |q' - q| ≤ ηq) (hp : |aPlus' - aPlus| ≤ ηPlus)
    (hm : |aMinus' - aMinus| ≤ ηMinus)
    (hh : |h - max 0 (min 1 (q' / 2 + θ / 2 * aPlus'))| ≤ δ)
    (hs : |s - max 0 (min 1 (h - θ / 2 * aMinus'))| ≤ δ)
    (hout : |out - max 0 (min 1 (2 * s))| ≤ δ) :
    |out - max 0 (min 1 (q + θ * (aPlus - aMinus)))| ≤
      5 * δ + ηq + θ * (ηPlus + ηMinus) := by
  let h0 := max 0 (min 1 (q / 2 + θ / 2 * aPlus))
  let s0 := max 0 (min 1 (h0 - θ / 2 * aMinus))
  have heh : |h - h0| ≤ δ + ηq / 2 + θ / 2 * ηPlus := by
    have hc := unitClamp_nonexpansive (q' / 2 + θ / 2 * aPlus')
      (q / 2 + θ / 2 * aPlus)
    have he : (q' / 2 + θ / 2 * aPlus') - (q / 2 + θ / 2 * aPlus) =
        (q' / 2 - q / 2) + (θ / 2 * aPlus' - θ / 2 * aPlus) := by ring
    rw [he] at hc
    have hadd := abs_add_le (q' / 2 - q / 2) (θ / 2 * aPlus' - θ / 2 * aPlus)
    have hqh := abs_half_sub_le hq
    have hph := abs_scaled_half_sub_le hθ0 hp
    have ht := abs_sub_le h (max 0 (min 1 (q' / 2 + θ / 2 * aPlus'))) h0
    change |h - h0| ≤ _
    change |max 0 (min 1 (q' / 2 + θ / 2 * aPlus')) - h0| ≤ _ at hc
    linarith
  have hes : |s - s0| ≤ 2 * δ + ηq / 2 + θ / 2 * (ηPlus + ηMinus) := by
    have hc := unitClamp_nonexpansive (h - θ / 2 * aMinus') (h0 - θ / 2 * aMinus)
    have he : (h - θ / 2 * aMinus') - (h0 - θ / 2 * aMinus) =
        (h - h0) - (θ / 2 * aMinus' - θ / 2 * aMinus) := by ring
    rw [he] at hc
    have hadd := abs_sub_le (h - h0) (0 : F) (θ / 2 * aMinus' - θ / 2 * aMinus)
    simp only [sub_zero, zero_sub, abs_neg] at hadd
    have hmh := abs_scaled_half_sub_le hθ0 hm
    have ht := abs_sub_le s (max 0 (min 1 (h - θ / 2 * aMinus'))) s0
    change |max 0 (min 1 (h - θ / 2 * aMinus')) - s0| ≤ _ at hc
    linarith
  have heout : |out - max 0 (min 1 (2 * s0))| ≤
      5 * δ + ηq + θ * (ηPlus + ηMinus) := by
    have hc := unitClamp_nonexpansive (2 * s) (2 * s0)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : F) < 2)] at hc
    have ht := abs_sub_le out (max 0 (min 1 (2 * s))) (max 0 (min 1 (2 * s0)))
    linarith
  simpa only [h0, s0, clippedFeedback_three_steps q θ aPlus aMinus
    hq0 hq1 hθ0 hθ1 hp0 hp1 hm0] using heout

/-- A common bound on the three input errors and three gate errors gives error at most eightfold. -/
theorem clippedFeedback_three_steps_error_common
    (q θ aPlus aMinus q' aPlus' aMinus' h s out δ : F)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp0 : 0 ≤ aPlus) (hp1 : aPlus ≤ 1) (hm0 : 0 ≤ aMinus)
    (hq : |q' - q| ≤ δ) (hp : |aPlus' - aPlus| ≤ δ)
    (hm : |aMinus' - aMinus| ≤ δ)
    (hh : |h - max 0 (min 1 (q' / 2 + θ / 2 * aPlus'))| ≤ δ)
    (hs : |s - max 0 (min 1 (h - θ / 2 * aMinus'))| ≤ δ)
    (hout : |out - max 0 (min 1 (2 * s))| ≤ δ) :
    |out - max 0 (min 1 (q + θ * (aPlus - aMinus)))| ≤ 8 * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hq
  have he := clippedFeedback_three_steps_error q θ aPlus aMinus q' aPlus' aMinus'
    h s out δ δ δ δ hq0 hq1 hθ0 hθ1 hp0 hp1 hm0 hq hp hm hh hs hout
  have hprod := mul_nonneg (sub_nonneg.mpr hθ1) hδ
  nlinarith

end GameTheory.Math
