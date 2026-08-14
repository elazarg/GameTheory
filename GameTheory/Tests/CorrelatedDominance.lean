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

/-! ## Local obedience is sufficient -/

def bothFalse : Profile boolForm.sig := fun _ => false

def crossed : Profile boolForm.sig := fun player => player

def coordinationUtility : boolForm.sig.Outcome → Bool → ℝ :=
  fun outcome _ => if outcome false = outcome true then 1 else 0

/-- A genuinely correlated recommendation: the two players receive the same
fair Boolean, so both diagonal profiles occur and neither crossed profile does.
-/
def diagonalLaw : FinDist (Profile boolForm.sig) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure bothFalse) (FinDist.pure bothTrue)

theorem mem_support_diagonalLaw_iff {profile : Profile boolForm.sig} :
    profile ∈ diagonalLaw.support ↔ profile = bothFalse ∨ profile = bothTrue := by
  exact FinDist.mem_support_mix_pure_iff
    (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      bothFalse bothTrue profile

theorem both_diagonal_profiles_supported :
    bothFalse ∈ diagonalLaw.support ∧ bothTrue ∈ diagonalLaw.support := by
  constructor <;> rw [mem_support_diagonalLaw_iff]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem crossed_not_supported : crossed ∉ diagonalLaw.support := by
  rw [mem_support_diagonalLaw_iff]
  intro hmem
  rcases hmem with heq | heq
  ·
    have := congrFun heq true
    simp [crossed, bothFalse] at this
  ·
    have := congrFun heq false
    simp [crossed, bothTrue] at this

theorem diagonalLaw_local_obedience :
    ∀ who recommended replacement,
      ∀ hrecommended :
          ∃ profile : Profile boolForm.sig,
            profile ∈ {candidate | candidate who = recommended} ∧
              profile ∈ diagonalLaw.support,
        (diagonalLaw.condOn {profile | profile who = recommended} hrecommended).expect
              (fun profile =>
                expectedUtility coordinationUtility who (boolForm.play profile)) ≥
          (diagonalLaw.condOn {profile | profile who = recommended} hrecommended).expect
              (fun profile => expectedUtility coordinationUtility who
                (boolForm.play (Profile.update profile who replacement))) := by
  intro who recommended replacement hrecommended
  apply FinDist.expect_mono
  intro profile hprofile
  have hbase := FinDist.support_condOn diagonalLaw
    {profile | profile who = recommended} hrecommended hprofile
  have hdiagonal := hbase.2
  rw [mem_support_diagonalLaw_iff] at hdiagonal
  rcases hdiagonal with rfl | rfl <;>
    cases who <;> cases recommended <;> cases replacement <;>
      norm_num [boolForm, coordinationUtility, bothFalse, bothTrue, Profile.update]

/-- The fair diagonal recommendation is certified as a correlated equilibrium
from the two local obedience families, without enumerating arbitrary response
functions. -/
theorem diagonalLaw_isCorrelatedEq :
    IsCorrelatedEq boolForm (euPreference coordinationUtility) diagonalLaw :=
  (isCorrelatedEq_iff_conditional_obedience diagonalLaw).2
    diagonalLaw_local_obedience

theorem crossedRecommendedFalse :
    ∃ profile : Profile boolForm.sig,
      profile ∈ {candidate | candidate false = false} ∧
        profile ∈ (FinDist.pure crossed).support := by
  exact ⟨crossed, rfl, by simp⟩

/-- The local interface also exposes a failed recommendation directly: at the
crossed profile, player `false` profitably switches from `false` to `true`. -/
theorem pure_crossed_not_isCorrelatedEq :
    ¬ IsCorrelatedEq boolForm (euPreference coordinationUtility)
      (FinDist.pure crossed) := by
  rw [isCorrelatedEq_iff_conditional_obedience]
  intro hobedient
  have hbad := hobedient false false true crossedRecommendedFalse
  rw [FinDist.condOn_pure] at hbad
  norm_num [boolForm, coordinationUtility, crossed, Profile.update] at hbad

end GameTheory.Tests.CorrelatedDominance
