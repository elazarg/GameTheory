/-
  EXP-110: a direct Mathlib PMF stopping law with infinite support.

  This is intentionally experiment-only.  The finite-support probability core
  remains canonical; the only bridge used below is `FinDist.toPMF`.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import GameTheory.Math.Probability.FinDist

noncomputable section

open scoped BigOperators ENNReal

namespace GameTheory.Experimental.CountableDiscreteStopping

open GameTheory.Math.Probability

private def halfMass (n : ℕ) : ℝ := (1 : ℝ) / 2 / 2 ^ n

private theorem hasSum_halfMass : HasSum halfMass 1 := by
  have hmass : halfMass = fun n : ℕ => (1 : ℝ) / 2 / 2 ^ n := rfl
  rw [hmass]
  simpa only [one_div] using (hasSum_geometric_two' 1)

private theorem halfMass_nonneg (n : ℕ) : 0 ≤ halfMass n := by
  unfold halfMass
  positivity

private theorem halfMass_pos (n : ℕ) : 0 < halfMass n := by
  unfold halfMass
  exact div_pos (by norm_num) (pow_pos (by norm_num) _)

/-- The constant hazard used by the stopping-law slice. -/
def halfHazard (_ : ℕ) : ℝ := (1 : ℝ) / 2

private def halfSurvival (n : ℕ) : ℝ :=
  ∏ time ∈ Finset.range n, (1 - halfHazard time)

private theorem halfSurvival_eq_pow (n : ℕ) :
    halfSurvival n = ((1 : ℝ) / 2) ^ n := by
  have h : (1 : ℝ) - (2 : ℝ)⁻¹ = 2⁻¹ := by norm_num
  simp [halfSurvival, halfHazard, h]

theorem halfMass_eq_pow (n : ℕ) :
    halfMass n = ((1 : ℝ) / 2) ^ (n + 1) := by
  unfold halfMass
  rw [pow_succ]
  calc
    (1 : ℝ) / 2 / 2 ^ n = (1 / 2) * (2⁻¹) ^ n := by
      rw [div_eq_mul_inv, inv_pow]
    _ = (1 / 2) ^ n * (1 / 2) := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      ring

theorem halfMass_eq_survival_mul_hazard (n : ℕ) :
    halfMass n = halfSurvival n * halfHazard n := by
  rw [halfSurvival_eq_pow, halfHazard, halfMass_eq_pow, pow_succ]

theorem halfMass_eq_survival_sub_succ (n : ℕ) :
    halfMass n = halfSurvival n - halfSurvival (n + 1) := by
  simp only [halfMass_eq_pow, halfSurvival_eq_pow, pow_succ]
  ring

private def halfNatLaw : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (halfMass n), by
    have hsum : ∑' n, ENNReal.ofReal (halfMass n) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg halfMass_nonneg hasSum_halfMass.summable]
      rw [hasSum_halfMass.tsum_eq]
      norm_num
    rw [← hsum]
    exact ENNReal.summable.hasSum⟩

/-- The first-stop law for a hazard equal to one half at every date. -/
def halfStoppingLaw : PMF (Option ℕ) := halfNatLaw.map some

@[simp]
theorem halfStoppingLaw_none : halfStoppingLaw none = 0 := by
  rw [halfStoppingLaw, PMF.map_apply]
  simp

@[simp]
theorem halfStoppingLaw_none_toReal : (halfStoppingLaw none).toReal = 0 := by
  rw [halfStoppingLaw_none]
  rfl

@[simp]
theorem halfStoppingLaw_some (n : ℕ) :
    halfStoppingLaw (some n) = ENNReal.ofReal (halfMass n) := by
  rw [halfStoppingLaw, PMF.map_apply]
  rw [tsum_eq_single n]
  · rw [if_pos rfl]
    rfl
  · intro b hbn
    have hne : some n ≠ some b := fun h => hbn (Option.some_injective ℕ h).symm
    simp [hne]

theorem halfStoppingLaw_some_toReal (n : ℕ) :
    (halfStoppingLaw (some n)).toReal = halfMass n := by
  rw [halfStoppingLaw_some, ENNReal.toReal_ofReal (halfMass_nonneg n)]

theorem halfStoppingLaw_some_toReal_pow (n : ℕ) :
    (halfStoppingLaw (some n)).toReal = ((1 : ℝ) / 2) ^ (n + 1) := by
  rw [halfStoppingLaw_some_toReal, halfMass_eq_pow]

theorem halfStoppingLaw_some_pos_ennreal (n : ℕ) :
    0 < halfStoppingLaw (some n) := by
  rw [halfStoppingLaw_some, ENNReal.ofReal_pos]
  exact halfMass_pos _

theorem halfStoppingLaw_some_pos (n : ℕ) :
    0 < (halfStoppingLaw (some n)).toReal := by
  rw [halfStoppingLaw_some_toReal]
  exact div_pos (by norm_num) (pow_pos (by norm_num) _)

theorem halfStoppingLaw_support_infinite :
    halfStoppingLaw.support.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => some n) (Option.some_injective ℕ)
  intro n
  rw [PMF.mem_support_iff, halfStoppingLaw_some]
  exact ENNReal.ofReal_ne_zero_iff.mpr (halfMass_pos _)

theorem no_finDist_representation :
    ¬ ∃ μ : FinDist (Option ℕ), μ.toPMF = halfStoppingLaw := by
  rintro ⟨μ, hμ⟩
  have hfinite : halfStoppingLaw.support.Finite := by
    rw [← hμ]
    exact μ.support_finite
  exact halfStoppingLaw_support_infinite.not_finite hfinite

end GameTheory.Experimental.CountableDiscreteStopping
