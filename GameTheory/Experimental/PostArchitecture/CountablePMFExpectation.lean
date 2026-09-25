/-
  EXP-112: exact guarded PMF expectation and its canonical measure bridge.

  The observable is bounded, so the canonical payoff-integrability guard is
  discharged by the public bound. The theorem consumes the shared expect/integral
  bridge rather than defining a second expectation API.
-/

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecificLimits.Basic
import GameTheory.Experimental.PostArchitecture.CountableDiscreteStopping
import GameTheory.Math.Probability.Measure

noncomputable section

open scoped BigOperators ENNReal

namespace GameTheory.Experimental.PostArchitecture.CountablePMFExpectation

open MeasureTheory
open GameTheory.Math.Probability

/-- The discrete measurable structure used by the stopping-law experiment. -/
instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

/-- Every singleton is measurable in the experiment's discrete carrier. -/
instance optionNatMeasurableSingletonClass :
    MeasurableSingletonClass (Option ℕ) := ⟨fun _ => trivial⟩

def stopObservable : Option ℕ → ℝ
  | none => 0
  | some n => ((1 : ℝ) / 2) ^ n

theorem stopObservable_bound (a : Option ℕ) :
    ‖stopObservable a‖ ≤ 1 := by
  cases a with
  | none => simp [stopObservable]
  | some n =>
      rw [stopObservable, Real.norm_eq_abs, abs_of_nonneg]
      · exact pow_le_one₀ (by norm_num) (by norm_num)
      · positivity

theorem halfStoppingLaw_expect_stopObservable :
    expect CountableDiscreteStopping.halfStoppingLaw stopObservable
      (payoffIntegrable_of_bounded _ stopObservable (C := 1)
        (fun a => by
          have := stopObservable_bound a
          simpa [Real.norm_eq_abs] using this)) = (2 : ℝ) / 3 := by
  rw [expect_eq_integral]
  rw [PMF.integral_eq_tsum
    CountableDiscreteStopping.halfStoppingLaw stopObservable
    ((payoffIntegrable_iff_integrable
      CountableDiscreteStopping.halfStoppingLaw stopObservable).mp
        (payoffIntegrable_of_bounded _ stopObservable (C := 1)
          (fun a => by
            have := stopObservable_bound a
            simpa [Real.norm_eq_abs] using this)))]
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

/-- The same exact value through the canonical Bochner-integral bridge. -/
theorem halfStoppingLaw_integral_stopObservable :
    (∫ a, stopObservable a ∂
      CountableDiscreteStopping.halfStoppingLaw.toMeasure) = (2 : ℝ) / 3 := by
  rw [← expect_eq_integral]
  exact halfStoppingLaw_expect_stopObservable

end GameTheory.Experimental.PostArchitecture.CountablePMFExpectation
