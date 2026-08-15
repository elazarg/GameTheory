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
    (fairPennies who).FullSupport := by
  intro action
  rw [← FinDist.prob_pos_iff, TableGame.toMixed_prob]
  norm_num [uniformPennies]

/-- The fair mixed Nash profile carries an explicit positive, vanishing
perturbation certificate through the general theorem. -/
theorem fairPennies_isTremblingHandPerfect :
    matchingPennies.toForm.IsTremblingHandPerfect
      (euPreference matchingPennies.utility) fairPennies :=
  fairPennies_isNash.isTremblingHandPerfect_of_fullSupport
    matchingPennies.toForm fairPennies_fullSupport

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
  play profile := FinDist.pure profile

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

/-- Player zero's mixed payoff is the product of the two `true` masses. -/
theorem dominated_expectedUtility_zero
    (mixedProfile : Profile dominatedForm.sig.mixed) :
    expectedUtility dominatedUtility 0
        (dominatedForm.mixed.play mixedProfile) =
      (mixedProfile 0).prob true * (mixedProfile 1).prob true := by
  rw [GameForm.mixed_play, expectedUtility_bind, FinDist.expect_eq_sum,
    boolProfiles, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [dominatedForm, dominatedUtility, bitsTT, bitsTF, bitsFT, bitsFF,
    FinDist.prob_pi, Fin.prod_univ_two]

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
    norm_num [dominatedForm, dominatedUtility, weakProfile, expectedUtility,
      Profile.update]

theorem weakMixedProfile_isNash :
    IsNash dominatedForm.mixed (euPreference dominatedUtility)
      weakMixedProfile :=
  weakProfile_isNash.purify

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
    have hsum := FinDist.sum_prob (approximating n 0)
    rw [Fintype.sum_bool] at hsum
    have hfalse := (hequilibria n).2.1 0 false
    have htrue := (hequilibria n).2.1 0 true
    linarith
  let shiftedWeight : ℕ → Bool → ℝ := fun n action =>
    if action then 1 - lower n 0 false else lower n 0 false
  have hshiftedNonneg (n : ℕ) (action : Bool) :
      0 ≤ shiftedWeight n action := by
    cases action <;> simp only [shiftedWeight, Bool.false_eq_true,
      if_false, if_true]
    · exact (hequilibria n).1 0 false |>.le
    · linarith [hmassLe n, (hequilibria n).1 0 true]
  have hshiftedSum (n : ℕ) : ∑ action, shiftedWeight n action = 1 := by
    rw [Fintype.sum_bool]
    simp [shiftedWeight]
  let shifted : ℕ → FinDist Bool := fun n =>
    FinDist.ofWeights (shiftedWeight n) (hshiftedNonneg n) (hshiftedSum n)
  have hshiftedRespects (n : ℕ) :
      dominatedForm.StrategyRespectsPerturbation (lower n 0) (shifted n) := by
    intro action
    rw [show (shifted n).prob action = shiftedWeight n action by
      exact FinDist.prob_ofWeights ..]
    cases action <;> simp only [shiftedWeight, Bool.false_eq_true,
      if_false, if_true]
    · exact le_rfl
    · linarith [hmassLe n]
  have hfalseEq (n : ℕ) :
      (approximating n 0).prob false = lower n 0 false := by
    have hpref :=
      ((dominatedForm.isPerturbedEq_iff (euPreference dominatedUtility)
        (lower n) (approximating n)).mp (hequilibria n).2).2
        0 (shifted n) (hshiftedRespects n)
    rw [euPreference_apply, dominated_expectedUtility_zero,
      dominated_expectedUtility_zero] at hpref
    have hopponentPos : 0 < (approximating n 1).prob true :=
      lt_of_lt_of_le ((hequilibria n).1 1 true)
        ((hequilibria n).2.1 1 true)
    have hsum := FinDist.sum_prob (approximating n 0)
    rw [Fintype.sum_bool] at hsum
    have hfalseLower := (hequilibria n).2.1 0 false
    have hshiftedTrue : (shifted n).prob true = 1 - lower n 0 false := by
      rw [show (shifted n).prob true = shiftedWeight n true by
        exact FinDist.prob_ofWeights ..]
      simp [shiftedWeight]
    simp only [Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)] at hpref
    rw [hshiftedTrue] at hpref
    nlinarith
  have htarget :
      Tendsto (fun n => (approximating n 0).prob false) atTop (nhds 1) := by
    simpa [weakMixedProfile, weakProfile, GameForm.purify] using
      hconverges 0 false
  have hlower :
      Tendsto (fun n => lower n 0 false) atTop (nhds 0) :=
    hzero 0 false
  have hequal :
      (fun n => (approximating n 0).prob false) =
        (fun n => lower n 0 false) :=
    funext hfalseEq
  rw [hequal] at htarget
  have : (1 : ℝ) = 0 := tendsto_nhds_unique htarget hlower
  norm_num at this

end GameTheory.Analysis.TremblingHandTest
