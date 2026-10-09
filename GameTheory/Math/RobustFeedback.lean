import GameTheory.Math.RobustAverage
import GameTheory.Math.ClampedFeedback

/-! Robust finite averaging and approximate projected feedback bound the underlying signal.
Exceptional samples contribute a count-dependent error; clipping is controlled by the
inward signal bounds at the interval endpoints. -/
namespace GameTheory.Math
open scoped BigOperators
variable {ι F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A projected feedback equation driven by imperfect samples bounds the true signal. -/
theorem robustAverage_feedback_residual (s bad : Finset ι) (hs : 0 < s.card)
    (hbad : bad ⊆ s) (b : ℕ) (hb : bad.card ≤ b) (f : ι → F)
    (x θ d ε ρ L : F) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ : 0 < θ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hd : |d| ≤ 1) (hε : 0 ≤ ε)
    (hgood : ∀ i ∈ s, i ∉ bad → |f i - d| ≤ ε)
    (hfeedback : |x - max 0 (min 1 (x + θ * ((∑ i ∈ s, f i) / (s.card : F))))| ≤ ρ)
    (hlower : -L * x ≤ d) (hupper : d ≤ L * (1 - x))
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) :
    |d| ≤ ε + 2 * (b : F) / (s.card : F) + ρ / θ + L * ρ := by
  have havg := robustAverage_bound s bad hs hbad b hb f d ε hf hd hε hgood
  have hη : 0 ≤ ε + 2 * (b : F) / (s.card : F) :=
    add_nonneg hε (div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
  exact clampedFeedback_residual_bound x θ ((∑ i ∈ s, f i) / (s.card : F)) d
    (ε + 2 * (b : F) / (s.card : F)) ρ L hx0 hx1 hθ havg hfeedback
    hlower hupper hL hρ hη
end GameTheory.Math
