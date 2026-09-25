/-
# Nondegenerate trembling-hand fixture

The fair Matching Pennies equilibrium has full support even though the game has
no pure Nash equilibrium.  It therefore exercises genuine mixed refinement,
not a point-mass or singleton shortcut.
-/

import GameTheory.Analysis.TremblingHand
import GameTheory.Examples.Classic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace GameTheory.Analysis.TremblingHandTest

open Filter GameTheory GameTheory.Finite GameTheory.Math.Probability GameTheory.Examples

/-- Both actions receive strictly positive probability at the fair profile. -/
theorem fairPennies_fullSupport (who : Fin 2) :
    ∀ action, action ∈ (fairPennies who).support := by
  intro action
  rw [PMF.mem_support_iff, fairPennies, TableGame.toMixed_apply]
  norm_num [uniformPennies]

/-- The fair mixed Nash profile carries an explicit positive, vanishing
perturbation certificate through the general theorem. -/
theorem fairPennies_isTremblingHandPerfect :
  matchingPennies.toForm.IsTremblingHandPerfect
      (euPreference matchingPennies.utility) fairPennies :=
  GameTheory.IsNash.isTremblingHandPerfect_of_fullSupport
    matchingPennies.toForm fairPennies_isNash fairPennies_fullSupport

/-- Nondegeneracy is visible in the statement: the game has no pure Nash
profile but does have a trembling-hand-perfect mixed profile. -/
theorem matchingPennies_refinement_without_pure_equilibrium :
    (∀ profile : Profile matchingPennies.sig,
      ¬ IsNash matchingPennies.toForm
        (euPreference matchingPennies.utility) profile) ∧
      matchingPennies.toForm.IsTremblingHandPerfect
        (euPreference matchingPennies.utility) fairPennies :=
  ⟨matchingPennies_noPureNash, fairPennies_isTremblingHandPerfect⟩

/-! ## A weakly dominated Nash equilibrium is not perfect -/

@[reducible]
def dominatedForm : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Fin 2 → Bool }
  play profile := PMF.pure profile

/-- Player zero earns one only when both players choose `true`; player one is
indifferent. Thus `false` is weakly dominated for player zero. -/
def dominatedUtility (outcome : Fin 2 → Bool) (who : Fin 2) : ℝ :=
  if who = 0 ∧ outcome 0 = true ∧ outcome 1 = true then 1 else 0

def dominatedGame : UtilityGame (Fin 2) :=
  ⟨dominatedForm, dominatedUtility⟩

private def bitsTT : Fin 2 → Bool := ![true, true]
private def bitsTF : Fin 2 → Bool := ![true, false]
private def bitsFT : Fin 2 → Bool := ![false, true]
private def bitsFF : Fin 2 → Bool := ![false, false]

private theorem boolProfiles :
    (Finset.univ : Finset (Fin 2 → Bool)) =
      {bitsTT, bitsTF, bitsFT, bitsFF} := by
  decide

private theorem pmfBool_sum_toReal_one (μ : PMF Bool) :
    (μ false).toReal + (μ true).toReal = 1 := by
  have h := congrArg ENNReal.toReal μ.tsum_coe
  rw [ENNReal.tsum_toReal_eq (fun action => μ.apply_ne_top action)] at h
  simpa only [tsum_fintype, Fintype.sum_bool, ENNReal.toReal_one,
    add_comm] using h

/-- Player zero's mixed payoff is the product of the two `true` masses. -/
theorem dominated_expectedUtility_zero
    (mixedProfile : Profile dominatedForm.sig.mixed) :
    expectedUtility dominatedUtility 0
        (dominatedForm.mixed.play mixedProfile)
        (payoffIntegrable_of_finite (dominatedForm.mixed.play mixedProfile)
          (fun outcome => dominatedUtility outcome 0)) =
      (mixedProfile 0 true).toReal * (mixedProfile 1 true).toReal := by
  let hproduct := payoffIntegrable_of_finite (independentProduct mixedProfile)
    (fun outcome => dominatedUtility outcome 0)
  have hlaw : dominatedForm.mixed.play mixedProfile =
      independentProduct mixedProfile := by
    rw [GameForm.mixed_play]
    simp [dominatedForm]
  calc
    expectedUtility dominatedUtility 0
        (dominatedForm.mixed.play mixedProfile)
        (payoffIntegrable_of_finite (dominatedForm.mixed.play mixedProfile)
          (fun outcome => dominatedUtility outcome 0))
        = expectedUtility dominatedUtility 0
            (independentProduct mixedProfile) hproduct :=
          expectedUtility_congr_law dominatedUtility 0 hlaw _ hproduct
    _ = ∑ profile, (independentProduct mixedProfile profile).toReal *
          dominatedUtility profile 0 := by
        rw [expectedUtility, expect_eq_sum]
    _ = (mixedProfile 0 true).toReal * (mixedProfile 1 true).toReal := by
      rw [boolProfiles, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp [dominatedUtility, bitsTT, bitsTF, bitsFT, bitsFF,
        independentProduct_apply, Fin.prod_univ_two]

def weakProfile : Profile dominatedForm.sig := fun _ => false

abbrev weakMixedProfile : Profile dominatedForm.sig.mixed :=
  dominatedForm.purify weakProfile

/-- Mutual `false` is Nash: player zero is indifferent between its two actions
when player one chooses `false`, and player one is always indifferent. -/
theorem weakProfile_isNash :
    IsNash dominatedForm (euPreference dominatedUtility) weakProfile := by
  rw [isNash_iff]
  intro who alternative
  rw [euPreference_apply]
  fin_cases who <;> cases alternative <;>
    refine ⟨payoffIntegrable_pure weakProfile _,
      payoffIntegrable_pure (weakProfile.update _ _) _, ?_⟩ <;>
      simp [expectedUtility_pure, dominatedForm, dominatedUtility,
        weakProfile]

theorem weakMixedProfile_isNash :
    IsNash dominatedForm.mixed (euPreference dominatedUtility)
      weakMixedProfile :=
  weakProfile_isNash.purify_of_finite

/-- The weakly dominated Nash equilibrium is not trembling-hand perfect.
Against every positive tremble by player one, player zero strictly benefits by
moving every unconstrained unit of mass from `false` to `true`; hence the
`false` mass must vanish with the perturbation and cannot converge to one. -/
theorem weakMixedProfile_not_isTremblingHandPerfect :
    ¬ dominatedForm.IsTremblingHandPerfect
      (euPreference dominatedUtility) weakMixedProfile := by
  intro hperfect
  rcases hperfect with ⟨lower, approximating, hequilibria, hzero, hconverges⟩
  have hmassLe (n : ℕ) : lower n 0 false + lower n 0 true ≤ 1 := by
    have hsum := pmfBool_sum_toReal_one (approximating n 0)
    have hfalse := (hequilibria n).2.1 0 false
    have htrue := (hequilibria n).2.1 0 true
    linarith
  let shiftedWeight : ℕ → Bool → ℝ := fun n action =>
    if action then 1 - lower n 0 false else lower n 0 false
  have hshiftedNonneg (n : ℕ) (action : Bool) :
      0 ≤ shiftedWeight n action := by
    cases action <;> simp only [shiftedWeight, Bool.false_eq_true,
      ite_false, ite_true]
    · exact (hequilibria n).1 0 false |>.le
    · linarith [hmassLe n, (hequilibria n).1 0 true]
  have hshiftedSum (n : ℕ) : ∑ action, shiftedWeight n action = 1 := by
    rw [Fintype.sum_bool]
    simp [shiftedWeight]
  let shifted : ℕ → PMF Bool := fun n =>
    PMF.ofFintype (fun action => ENNReal.ofReal (shiftedWeight n action)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun action _ => hshiftedNonneg n action), hshiftedSum n]
      norm_num)
  have hshiftedRespects (n : ℕ) :
      dominatedForm.StrategyRespectsPerturbation (lower n 0) (shifted n) := by
    intro action
    rw [show (shifted n action).toReal = shiftedWeight n action by
      simp [shifted, PMF.ofFintype_apply, ENNReal.toReal_ofReal,
        hshiftedNonneg]]
    cases action <;> simp only [shiftedWeight, Bool.false_eq_true,
      ite_false, ite_true]
    · exact le_rfl
    · linarith [hmassLe n]
  have hfalseEq (n : ℕ) :
      (approximating n 0 false).toReal = lower n 0 false := by
    have hpref :=
      ((dominatedForm.isPerturbedEq_iff (euPreference dominatedUtility)
        (lower n) (approximating n)).mp (hequilibria n).2).2
        0 (shifted n) (hshiftedRespects n)
    rcases hpref with ⟨hpreferred, halternative, hle⟩
    have hpreferredFormula :
        expectedUtility dominatedUtility 0
          (dominatedForm.mixed.play (approximating n)) hpreferred =
          (approximating n 0 true).toReal *
          (approximating n 1 true).toReal := by
      let hcanonical := payoffIntegrable_of_finite
        (dominatedForm.mixed.play (approximating n))
        (fun outcome => dominatedUtility outcome 0)
      rw [expectedUtility_congr_law dominatedUtility 0 rfl hpreferred
        hcanonical]
      exact dominated_expectedUtility_zero (approximating n)
    have halternativeFormula :
        expectedUtility dominatedUtility 0
          (dominatedForm.mixed.play ((approximating n).update 0 (shifted n)))
          halternative =
          ((approximating n).update 0 (shifted n) 0 true).toReal *
          ((approximating n).update 0 (shifted n) 1 true).toReal := by
      let hcanonical := payoffIntegrable_of_finite
        (dominatedForm.mixed.play ((approximating n).update 0 (shifted n)))
        (fun outcome => dominatedUtility outcome 0)
      rw [expectedUtility_congr_law dominatedUtility 0 rfl halternative
        hcanonical]
      exact dominated_expectedUtility_zero _
    rw [hpreferredFormula, halternativeFormula] at hle
    have hopponentPos : 0 < (approximating n 1 true).toReal :=
      lt_of_lt_of_le ((hequilibria n).1 1 true)
        ((hequilibria n).2.1 1 true)
    have hsum := pmfBool_sum_toReal_one (approximating n 0)
    have hfalseLower := (hequilibria n).2.1 0 false
    have hshiftedTrue : (shifted n true).toReal = 1 - lower n 0 false := by
      rw [show (shifted n true).toReal = shiftedWeight n true by
        simp [shifted, PMF.ofFintype_apply, ENNReal.toReal_ofReal,
          hshiftedNonneg]]
      simp [shiftedWeight]
    simp only [Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)] at hle
    rw [hshiftedTrue] at hle
    nlinarith
  have htarget :
      Tendsto (fun n => (approximating n 0 false).toReal) atTop (nhds 1) := by
    simpa [weakMixedProfile, weakProfile, GameForm.purify] using
      (hconverges 0).toReal false
  have hlower :
      Tendsto (fun n => lower n 0 false) atTop (nhds 0) :=
    hzero 0 false
  have hequal :
      (fun n => (approximating n 0 false).toReal) =
        (fun n => lower n 0 false) :=
    funext hfalseEq
  rw [hequal] at htarget
  have : (1 : ℝ) = 0 := tendsto_nhds_unique htarget hlower
  norm_num at this

end GameTheory.Analysis.TremblingHandTest
