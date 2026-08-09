/-
Hostile correlated-dominance fixture.

Against player one's surviving action `false`, player zero's `true` strictly
dominates `false`.  The dominance is deliberately only relative: when player
one plays the eliminated action `true`, the comparison reverses.  The pure
Nash/CE law at `(true, false)` therefore exercises support-aware dominance
without accidentally proving global strict dominance.
-/

import GameTheory.Core.CorrelatedDominance

noncomputable section

namespace GameTheory.Tests.CorrelatedDominance

open Probability

@[reducible]
def boolForm : GameForm Bool where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Bool → Bool }
  play profile := FinDist.pure profile

def trueFalse : Profile boolForm.sig :=
  fun player => !player

def bothTrue : Profile boolForm.sig := fun _ => true

def utility : boolForm.sig.Outcome → Bool → ℝ :=
  fun outcome player =>
    if player then if outcome player then 0 else 1
    else if outcome false ≠ outcome true then 1 else 0

def allowed : ∀ player, Set (boolForm.sig.Strategy player) :=
  fun player => if player then {false} else Set.univ

def law : FinDist (Profile boolForm.sig) := FinDist.pure trueFalse

theorem trueFalse_isNash :
    IsNash boolForm (euPreference utility) trueFalse := by
  rw [isNash_iff]
  intro player replacement
  cases player <;> cases replacement <;>
    norm_num [boolForm, utility, trueFalse, Profile.update]

theorem law_isCorrelatedEq : IsCorrelatedEq boolForm (euPreference utility) law :=
  trueFalse_isNash.isCorrelatedEq

theorem trueRecommended :
    ∃ profile : Profile boolForm.sig,
      profile ∈ {candidate | candidate false = true} ∧ profile ∈ law.support :=
  ⟨trueFalse, by simp [trueFalse], by simp [law]⟩

theorem law_conditional_obedience_true :
    (law.condOn {profile | profile false = true} trueRecommended).expect
        (fun profile => expectedUtility utility false (boolForm.play profile)) ≥
      (law.condOn {profile | profile false = true} trueRecommended).expect
        (fun profile => expectedUtility utility false
          (boolForm.play (Profile.update profile false false))) :=
  law_isCorrelatedEq.conditional_obedience false true false trueRecommended

theorem law_support_subset_allowed :
    ∀ profile ∈ law.support, ∀ player, profile player ∈ allowed player := by
  intro profile hprofile player
  have heq : profile = trueFalse := by
    simpa [law] using hprofile
  subst profile
  cases player <;> simp [allowed, trueFalse]

theorem true_strictlyDominates_false_on_allowed :
    StrictlyDominatesOn boolForm (euPreference utility) false allowed true false := by
  intro profile hallowed
  rw [euPreference_strict_iff]
  have hopponent : profile true = false := hallowed true
  norm_num [boolForm, utility, Profile.update, hopponent]

theorem law_support_avoids_false :
    ∀ profile ∈ law.support, profile false ≠ false :=
  law_isCorrelatedEq.support_avoids_strictlyDominatedOn allowed
    law_support_subset_allowed false true_strictlyDominates_false_on_allowed

theorem true_not_globally_strictlyDominates_false :
    ¬ StrictlyDominates boolForm (euPreference utility) false true false := by
  intro hdom
  have h := hdom bothTrue (fun _ => Set.mem_univ _)
  rw [euPreference_strict_iff] at h
  norm_num [boolForm, utility, bothTrue, Profile.update] at h

end GameTheory.Tests.CorrelatedDominance
