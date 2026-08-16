/-
  EXP-112: bounded real expectation for direct countable PMFs.

  The expectation notion here is Mathlib's Bochner integral against
  `PMF.toMeasure`; no second probability or expectation wrapper is introduced.
  Every observable in this slice carries an explicit pointwise norm bound.
-/

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecificLimits.Basic
import GameTheory.Experimental.PostArchitecture.CountableDiscreteStopping
import GameTheory.Math.Probability.FinDist

noncomputable section

open scoped BigOperators ENNReal

namespace GameTheory.Experimental.PostArchitecture.CountablePMFExpectation

open MeasureTheory
open GameTheory.Math.Probability

private instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

private instance optionNatMeasurableSingletonClass :
    MeasurableSingletonClass (Option ℕ) := ⟨fun _ => trivial⟩

theorem pmf_integral_eq_tsum_of_bound {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ)
    {C : ℝ} (hbound : ∀ a, ‖f a‖ ≤ C) :
    (∫ a, f a ∂p.toMeasure) = ∑' a, (p a).toReal * f a := by
  rw [PMF.integral_eq_tsum p f]
  · simp only [smul_eq_mul]
  · apply Integrable.of_bound AEStronglyMeasurable.of_discrete C
    exact ae_of_all _ hbound

theorem finDist_integral_eq_expect_of_bound {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : FinDist α) (f : α → ℝ) {C : ℝ} (hbound : ∀ a, ‖f a‖ ≤ C) :
    (∫ a, f a ∂μ.toPMF.toMeasure) = μ.expect f := by
  rw [pmf_integral_eq_tsum_of_bound μ.toPMF f hbound]
  rfl

private def stopObservable : Option ℕ → ℝ
  | none => 0
  | some n => ((1 : ℝ) / 2) ^ n

private theorem stopObservable_bound (a : Option ℕ) :
    ‖stopObservable a‖ ≤ 1 := by
  cases a with
  | none => simp [stopObservable]
  | some n =>
      rw [stopObservable, Real.norm_eq_abs, abs_of_nonneg]
      · exact pow_le_one₀ (by norm_num) (by norm_num)
      · positivity

theorem halfStoppingLaw_integral_stopObservable :
    (∫ a, stopObservable a ∂
      (CountableDiscreteStopping.halfStoppingLaw.toMeasure)) = (2 : ℝ) / 3 := by
  rw [pmf_integral_eq_tsum_of_bound
    CountableDiscreteStopping.halfStoppingLaw stopObservable stopObservable_bound]
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.tsum_eq]
  let g : ℕ ⊕ PUnit.{1} → ℝ := fun c =>
    (CountableDiscreteStopping.halfStoppingLaw
        ((Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm c)).toReal *
      stopObservable ((Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm c)
  show (∑' c : ℕ ⊕ PUnit.{1}, g c) = (2 : ℝ) / 3
  have hsum : HasSum g
      ((1 / 2 : ℝ) * (1 - (1 : ℝ) / 4)⁻¹ + 0) := HasSum.sum (f := g) ?_ ?_
  rw [hsum.tsum_eq]
  norm_num
  · have hscaled :=
      (hasSum_geometric_of_lt_one (r := (1 : ℝ) / 4) (by norm_num) (by norm_num)).mul_left
        ((1 : ℝ) / 2)
    have hfun : g ∘ Sum.inl = fun n : ℕ => (1 / 2 : ℝ) * ((1 : ℝ) / 4) ^ n := by
      funext n
      simp only [Function.comp_apply, g, Equiv.optionEquivSumPUnit_symm_inl,
        stopObservable, CountableDiscreteStopping.halfStoppingLaw_some_toReal,
        CountableDiscreteStopping.halfMass_eq_pow]
      rw [pow_succ]
      rw [show (1 / 2 : ℝ) ^ n * (1 / 2) * (1 / 2) ^ n =
          (1 / 2) * ((1 / 2 : ℝ) ^ n * (1 / 2) ^ n) by ring]
      rw [← mul_pow]
      norm_num
    rw [hfun]
    exact hscaled
  · have hfun : g ∘ Sum.inr = fun _ : PUnit.{1} => (0 : ℝ) := by
      funext c
      simp only [Function.comp_apply, g, Equiv.optionEquivSumPUnit_symm_inr,
        stopObservable]
      rw [CountableDiscreteStopping.halfStoppingLaw_none_toReal]
      ring
    rw [hfun]
    exact hasSum_zero

end GameTheory.Experimental.PostArchitecture.CountablePMFExpectation
