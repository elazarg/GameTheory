module

/-
# Integrating cumulative quantities against a finite measure

Fubini exchanges an interval integral up to a random endpoint with integration
against the measure of a closed upper tail. Quantities may have either sign;
no density or atomlessness assumption is needed.
-/

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability

open MeasureTheory Set

private theorem integral_cutoff_slice {a b x : ℝ} {q : ℝ → ℝ}
    (hx : x ∈ Icc a b) :
    (∫ t, (if t ≤ x then q t else 0) ∂volume.restrict (Ioc a b)) =
      ∫ t in a..x, q t := by
  have hslice : (fun t => if t ≤ x then q t else 0) = (Iic x).indicator q := by
    ext t
    simp [Set.indicator]
  have hs : Iic x ∩ Ioc a b = Ioc a x := by
    ext t
    constructor
    · rintro ⟨htx, hat, _⟩
      exact ⟨hat, htx⟩
    · rintro ⟨hat, htx⟩
      exact ⟨htx, hat, htx.trans hx.2⟩
  rw [hslice, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hs, intervalIntegral.integral_of_le hx.1]

private theorem integrable_cutoff_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} {q : ℝ → ℝ} (hq : IntervalIntegrable q volume a b) :
    Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then q p.2 else 0)
      (μ.prod (volume.restrict (Ioc a b))) := by
  convert
    (hq.1.comp_snd μ).indicator
      (measurableSet_le measurable_snd measurable_fst) using 1
  ext p
  by_cases hp : p.2 ≤ p.1 <;> simp [hp]

/-- An interval-integrable quantity has an integrable cumulative quantity
under every finite measure concentrated on the interval. -/
theorem integrable_intervalIntegral (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} {q : ℝ → ℝ} (hq : IntervalIntegrable q volume a b)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Icc a b) :
    Integrable (fun x => ∫ t in a..x, q t) μ := by
  apply (integrable_cutoff_kernel μ hq).integral_prod_left.congr
  filter_upwards [hsupport] with x hx
  exact integral_cutoff_slice hx

/-- The expected cumulative quantity equals the interval integral of the
quantity weighted by the finite measure of the closed upper tail. The
quantity may be signed, and the measure may have atoms. -/
theorem integral_intervalIntegral_eq_integral_mul_tail
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b)
    {q : ℝ → ℝ} (hq : IntervalIntegrable q volume a b)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Icc a b) :
    (∫ x, (∫ t in a..x, q t) ∂μ) =
      ∫ t in a..b, q t * (μ (Ici t)).toReal := by
  calc
    (∫ x, (∫ t in a..x, q t) ∂μ) =
        ∫ x, ∫ t, (if t ≤ x then q t else 0)
          ∂volume.restrict (Ioc a b) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hsupport] with x hx
      exact (integral_cutoff_slice hx).symm
    _ = ∫ t, ∫ x, (if t ≤ x then q t else 0)
        ∂μ ∂volume.restrict (Ioc a b) :=
      integral_integral_swap (integrable_cutoff_kernel μ hq)
    _ = ∫ t in a..b, q t * (μ (Ici t)).toReal := by
      rw [intervalIntegral.integral_of_le hab]
      apply integral_congr_ae
      filter_upwards with t
      have hslice : (fun x => if t ≤ x then q t else 0) =
          (Ici t).indicator (fun _ => q t) := by
        ext x
        simp [Set.indicator]
      rw [hslice, integral_indicator measurableSet_Ici, setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]

end GameTheory.Math.Probability
