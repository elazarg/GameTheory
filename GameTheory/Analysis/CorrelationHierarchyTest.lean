/-
# Coarse correlated equilibrium without correlated equilibrium, at full support

A uniform device recommends the same one of three actions to both players.
Every recommendation has positive probability, yet the device is a coarse
correlated equilibrium and not a correlated one for the first player's
utility: after the recommendation `1` the first player prefers `0`, while no
recommendation-blind commitment beats obedience. The aggregation of correlated
comparisons into coarse ones is not undone by full support.

The mediated extension therefore preserves correlated equilibrium but not
coarse correlated equilibrium, and the commitment form the reverse.
-/

import GameTheory.Analysis.CorrelationHierarchy
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Tests.CorrelationHierarchy

open GameTheory GameTheory.Math.Probability GameTheory.GameForm

/-- Two players, three actions each; the outcome is the action pair. -/
@[reducible]
def form : GameForm Bool where
  sig := { Strategy := fun _ => Fin 3, Outcome := Fin 3 × Fin 3 }
  play profile := PMF.pure (profile false, profile true)

/-- The same uniform recommendation to both players. -/
def device : PMF (Profile form.sig) :=
  (PMF.uniformOfFintype (Fin 3)).map fun recommended _ => recommended

/-- The first player likes the matched outcomes `0` and `2` and the
mismatch `(0, 1)`; the second player is indifferent. -/
def utility : Fin 3 × Fin 3 → Bool → ℝ
  | (0, 0), false => 1
  | (0, 1), false => 1
  | (2, 2), false => 1
  | _, _ => 0

theorem outcomeLaw_map (g : Fin 3 → Profile form.sig) :
    form.outcomeLaw ((PMF.uniformOfFintype (Fin 3)).map g) =
      (PMF.uniformOfFintype (Fin 3)).map fun recommended =>
        (g recommended false, g recommended true) := by
  simp only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def]
  exact PMF.bind_pure_comp _ _

theorem expect_uniform_map (g : Fin 3 → Fin 3 × Fin 3) (u : Fin 3 × Fin 3 → ℝ) :
    expect ((PMF.uniformOfFintype (Fin 3)).map g) u = (u (g 0) + u (g 1) + u (g 2)) / 3 := by
  rw [expect_map, expect_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Fin.sum_univ_three,
    Function.comp_apply]
  norm_num
  ring

theorem coarse_holds (who : Bool) (replacement : Fin 3) :
    (equilibriumComparison form device (DeviationScheme.unilateralConstant form.sig) id who
      replacement).Holds (utility · who) := by
  rw [IncentiveComparison.holds_iff]
  simp only [equilibriumComparison, DeviationScheme.unilateralConstant_apply, device,
    PMF.map_comp, outcomeLaw_map, Function.comp_def]
  rw [expect_uniform_map, expect_uniform_map]
  cases who <;> fin_cases replacement <;> simp [utility, Profile.update, Function.update] <;>
    norm_num

theorem correlated_fails :
    ¬ (equilibriumComparison form device (DeviationScheme.recommendation form.sig) id false
      (fun recommended => if recommended = 1 then 0 else recommended)).Holds
        (utility · false) := by
  rw [IncentiveComparison.holds_iff]
  simp only [equilibriumComparison, DeviationScheme.recommendation_apply, device,
    PMF.map_comp, outcomeLaw_map, Function.comp_def]
  rw [expect_uniform_map, expect_uniform_map]
  simp [utility, Profile.update, Function.update]
  norm_num

/-- Every recommendation has positive probability for every player. -/
theorem device_full_support (who : Bool) (recommended : Fin 3) :
    device.map (fun profile => profile who) recommended ≠ 0 := by
  simp only [device, PMF.map_comp, Function.comp_def]
  simp

theorem coarse_not_implies_correlated :
    ¬ IncentiveComparison.Implies
      (equilibriumComparison form device (DeviationScheme.unilateralConstant form.sig) id)
      (equilibriumComparison form device (DeviationScheme.recommendation form.sig) id) :=
  fun himplies => correlated_fails (himplies utility coarse_holds false _)

/-- **Descent fails through the mediated extension.** -/
theorem mediated_separates :
    IncentiveComparison.Implies
        (equilibriumComparison form device (DeviationScheme.recommendation form.sig) id)
        (equilibriumComparison (form.mediated device) (PMF.pure (form.obedient device))
          (DeviationScheme.recommendation _) id) ∧
      ¬ IncentiveComparison.Implies
        (equilibriumComparison form device (DeviationScheme.unilateralConstant form.sig) id)
        (equilibriumComparison (form.mediated device) (PMF.pure (form.obedient device))
          (DeviationScheme.unilateralConstant _) id) := by
  obtain ⟨hcorrelated, hiff⟩ := form.mediated_preservation device id
  exact ⟨hcorrelated, fun h => coarse_not_implies_correlated (hiff.1 h)⟩

/-- **Ascent fails from the commitment form.** -/
theorem commitment_separates :
    IncentiveComparison.Implies
        (equilibriumComparison (form.commitment device) (PMF.pure fun _ => none)
          (DeviationScheme.unilateralConstant _) id)
        (equilibriumComparison form device (DeviationScheme.unilateralConstant form.sig) id) ∧
      ¬ IncentiveComparison.Implies
        (equilibriumComparison (form.commitment device) (PMF.pure fun _ => none)
          (DeviationScheme.recommendation _) id)
        (equilibriumComparison form device (DeviationScheme.recommendation form.sig) id) := by
  obtain ⟨hcoarse, hiff⟩ := form.commitment_preservation device id
  exact ⟨hcoarse, fun h => coarse_not_implies_correlated (hiff.1 h)⟩

end GameTheory.Tests.CorrelationHierarchy
