import GameTheory.Math.RobustAverage
import GameTheory.Math.ClampedFeedback
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Robust finite averaging and approximate projected feedback bound the underlying signal.
Exceptional samples contribute a count-dependent error; clipping is controlled by the
inward signal bounds at the interval endpoints. -/
namespace GameTheory.Math
open scoped BigOperators
variable {ι F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Exceptional errors enter the residual estimate with their actual magnitude budget. -/
theorem robustAverage_feedback_error (s bad : Finset ι) (hs : 0 < s.card)
    (hbad : bad ⊆ s) (b : ℕ) (hb : bad.card ≤ b) (f : ι → F)
    (x θ d ε R ρ L : F) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ : 0 < θ)
    (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hgood : ∀ i ∈ s, i ∉ bad → |f i - d| ≤ ε)
    (hexceptional : ∀ i ∈ bad, |f i - d| ≤ R)
    (hfeedback : |x - max 0 (min 1 (x + θ * ((∑ i ∈ s, f i) / (s.card : F))))| ≤ ρ)
    (hlower : -L * x ≤ d) (hupper : d ≤ L * (1 - x)) :
    |d| ≤ ε + R * (b : F) / (s.card : F) + ρ / θ + L * ρ := by
  have havg := robustAverage_error_bound s bad hs hbad b hb f d ε R hε hR hgood hexceptional
  exact clampedFeedback_residual_bound x θ ((∑ i ∈ s, f i) / (s.card : F)) d
    (ε + R * (b : F) / (s.card : F)) ρ L hx0 hx1 hθ havg hfeedback
    hlower hupper

/-- A projected feedback equation driven by imperfect samples bounds the true signal. -/
theorem robustAverage_feedback_residual (s bad : Finset ι) (hs : 0 < s.card)
    (hbad : bad ⊆ s) (b : ℕ) (hb : bad.card ≤ b) (f : ι → F)
    (x θ d ε ρ L : F) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ : 0 < θ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hd : |d| ≤ 1) (hε : 0 ≤ ε)
    (hgood : ∀ i ∈ s, i ∉ bad → |f i - d| ≤ ε)
    (hfeedback : |x - max 0 (min 1 (x + θ * ((∑ i ∈ s, f i) / (s.card : F))))| ≤ ρ)
    (hlower : -L * x ≤ d) (hupper : d ≤ L * (1 - x)) :
    |d| ≤ ε + 2 * (b : F) / (s.card : F) + ρ / θ + L * ρ := by
  apply robustAverage_feedback_error s bad hs hbad b hb f x θ d ε 2 ρ L hx0 hx1 hθ
    hε (by positivity) hgood _ hfeedback hlower hupper
  intro i hi
  have hab := abs_sub_le (f i) 0 d
  simp only [sub_zero, zero_sub, abs_neg] at hab
  linarith [hf i (hbad hi)]

/-- Forty-one samples tolerate two exceptional errors of at most twenty-five eighths. -/
theorem robustFeedback_fortyOne_residual (bad : Finset (Fin 41)) (hb : bad.card ≤ 2)
    (f : Fin 41 → F) (x θ d ε ρ L : F)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ : 0 < θ)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 512)
    (hgood : ∀ i, i ∉ bad → |f i - d| ≤ ε)
    (hexceptional : ∀ i ∈ bad, |f i - d| ≤ 25 / 8)
    (hfeedback : |x - max 0 (min 1 (x + θ * ((∑ i, f i) / 41)))| ≤ ρ)
    (hlower : -L * x ≤ d) (hupper : d ≤ L * (1 - x))
    (hround : ρ / θ + L * ρ ≤ 1 / 512) :
    |d| ≤ 1 / 6 := by
  have h := robustAverage_feedback_error Finset.univ bad (by simp)
    (Finset.subset_univ bad) 2 hb f x θ d ε (25 / 8) ρ L hx0 hx1 hθ
    hε (by positivity) (by simpa using hgood) hexceptional
    (by simpa using hfeedback) hlower hupper
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
  have hbudget : (1 : F) / 512 + (25 / 8) * 2 / 41 + 1 / 512 ≤ 1 / 6 := by norm_num
  calc
    |d| ≤ ε + (25 / 8) * 2 / 41 + ρ / θ + L * ρ := h
    _ ≤ 1 / 512 + (25 / 8) * 2 / 41 + 1 / 512 := by linarith
    _ ≤ 1 / 6 := hbudget

end GameTheory.Math
