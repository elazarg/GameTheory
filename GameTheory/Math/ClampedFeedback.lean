import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-! Approximate clamped feedback controls an inward-pointing scalar residual.
Boundary estimates account for clipping separately from interior updates. -/

namespace GameTheory.Math
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- An approximately stationary clamped update controls an inward-pointing
residual despite an additive error in the update signal. -/
theorem clampedFeedback_residual_bound (x θ a d η ρ L : F)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ : 0 < θ)
    (hnoise : |a - d| ≤ η)
    (hstep : |x - max 0 (min 1 (x + θ * a))| ≤ ρ)
    (hlo : -L * x ≤ d) (hhi : d ≤ L * (1 - x))
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) :
    |d| ≤ η + ρ / θ + L * ρ := by
  have hquot : 0 ≤ ρ / θ := div_nonneg hρ hθ.le
  have hmul : 0 ≤ L * ρ := mul_nonneg hL hρ
  obtain ⟨hnoiseLo, hnoiseHi⟩ := abs_le.mp hnoise
  by_cases hlower : x + θ * a ≤ 0
  · have hclamp : max 0 (min 1 (x + θ * a)) = 0 := by
      rw [min_eq_right (hlower.trans zero_le_one), max_eq_left hlower]
    rw [hclamp, sub_zero, abs_of_nonneg hx0] at hstep
    have ha : a ≤ 0 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  · by_cases hupper : 1 ≤ x + θ * a
    · have hclamp : max 0 (min 1 (x + θ * a)) = 1 := by
        rw [min_eq_left hupper, max_eq_right zero_le_one]
      rw [hclamp, abs_of_nonpos (sub_nonpos.mpr hx1)] at hstep
      have ha : 0 ≤ a := by nlinarith
      rw [abs_le]
      constructor <;> nlinarith
    · have hclamp : max 0 (min 1 (x + θ * a)) = x + θ * a := by
        rw [min_eq_right (le_of_not_ge hupper), max_eq_right (le_of_not_ge hlower)]
      rw [hclamp] at hstep
      obtain ⟨hstepLo, hstepHi⟩ := abs_le.mp hstep
      have hcancel : ρ / θ * θ = ρ := div_mul_cancel₀ _ hθ.ne'
      have haLo : -(ρ / θ) ≤ a := by nlinarith
      have haHi : a ≤ ρ / θ := by nlinarith
      rw [abs_le]
      constructor <;> linarith
end GameTheory.Math
