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

open GameTheory.Math.Probability

@[reducible]
def boolForm : GameForm Bool where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Bool → Bool }
  play profile := PMF.pure profile

def trueFalse : Profile boolForm.sig :=
  fun player => !player

def bothTrue : Profile boolForm.sig := fun _ => true

def bothFalse : Profile boolForm.sig := fun _ => false

def utility : boolForm.sig.Outcome → Bool → ℝ :=
  fun outcome player =>
    if player then if outcome player then 0 else 1
    else if outcome false ≠ outcome true then 1 else 0

def allowed : ∀ player, Set (boolForm.sig.Strategy player) :=
  fun player => if player then {false} else Set.univ

def law : PMF (Profile boolForm.sig) := PMF.pure trueFalse

theorem trueFalse_isNash :
    IsNash boolForm (euPreference utility) trueFalse := by
  rw [isNash_iff]
  intro player replacement
  have hle : utility (Profile.update trueFalse player replacement) player ≤
      utility trueFalse player := by
    cases player <;> cases replacement <;>
      norm_num [utility, trueFalse, Profile.update_same, Profile.update_of_ne]
  simpa [boolForm] using
    (euPreference_pure_iff utility player trueFalse
      (Profile.update trueFalse player replacement)).2 hle

theorem law_isCorrelatedEq : IsCorrelatedEq boolForm (euPreference utility) law :=
  trueFalse_isNash.isCorrelatedEq

theorem trueRecommended :
    ∃ profile : Profile boolForm.sig,
      profile ∈ {candidate | candidate false = true} ∧ profile ∈ law.support :=
  ⟨trueFalse, by simp [trueFalse], by simp [law]⟩

theorem true_recommended_supported :
    true ∈ (law.map fun profile => profile false).support := by
  rw [PMF.mem_support_map_iff]
  exact ⟨trueFalse, by simp [law], by simp [trueFalse]⟩

theorem law_conditional_obedience_true :
    euPreference utility false
      (boolForm.outcomeLaw (fiberPosterior law (fun profile => profile false) true
        true_recommended_supported))
      ((fiberPosterior law (fun profile => profile false) true
        true_recommended_supported).bind fun profile =>
          boolForm.play (Profile.update profile false false)) :=
  law_isCorrelatedEq.conditional_obedience false true false true_recommended_supported

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
  have hpreferred := payoffIntegrable_pure (Profile.update profile false true)
    (fun outcome => utility outcome false)
  have halternative := payoffIntegrable_pure (Profile.update profile false false)
    (fun outcome => utility outcome false)
  apply (euPreference_strict_iff utility false
    (PMF.pure (Profile.update profile false true))
    (PMF.pure (Profile.update profile false false)) hpreferred halternative).mpr
  have hopponent : profile true = false := hallowed true
  norm_num [expectedUtility_pure, utility, hopponent, Profile.update_same,
    Profile.update_of_ne]

theorem law_support_avoids_false :
    ∀ profile ∈ law.support, profile false ≠ false :=
  law_isCorrelatedEq.support_avoids_strictlyDominatedOn allowed
    law_support_subset_allowed false true_strictlyDominates_false_on_allowed

theorem true_not_globally_strictlyDominates_false :
    ¬ StrictlyDominates boolForm (euPreference utility) false true false := by
  intro hdom
  have h := hdom bothTrue (fun _ => Set.mem_univ _)
  have hval := (euPreference_strict_iff utility false
    (PMF.pure (Profile.update bothTrue false true))
    (PMF.pure (Profile.update bothTrue false false))
    (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)).mp h
  norm_num [expectedUtility_pure, utility, bothTrue, Profile.update_same,
    Profile.update_of_ne] at hval

/-! ## Local obedience is sufficient -/

def crossed : Profile boolForm.sig := fun player => player

def coordinationUtility : boolForm.sig.Outcome → Bool → ℝ :=
  fun outcome _ => if outcome false = outcome true then 1 else 0

theorem bothFalse_isNash :
    IsNash boolForm (euPreference coordinationUtility) bothFalse := by
  rw [isNash_iff]
  intro who replacement
  have hle : coordinationUtility (Profile.update bothFalse who replacement) who ≤
      coordinationUtility bothFalse who := by
    cases who <;> cases replacement <;>
      norm_num [coordinationUtility, bothFalse, Profile.update_same,
        Profile.update_of_ne]
  simpa [boolForm] using
    (euPreference_pure_iff coordinationUtility who bothFalse
      (Profile.update bothFalse who replacement)).2 hle

theorem bothTrue_isNash :
    IsNash boolForm (euPreference coordinationUtility) bothTrue := by
  rw [isNash_iff]
  intro who replacement
  have hle : coordinationUtility (Profile.update bothTrue who replacement) who ≤
      coordinationUtility bothTrue who := by
    cases who <;> cases replacement <;>
      norm_num [coordinationUtility, bothTrue, Profile.update_same,
        Profile.update_of_ne]
  simpa [boolForm] using
    (euPreference_pure_iff coordinationUtility who bothTrue
      (Profile.update bothTrue who replacement)).2 hle

theorem bothFalse_isCorrelatedEq :
    IsCorrelatedEq boolForm (euPreference coordinationUtility) (PMF.pure bothFalse) :=
  bothFalse_isNash.isCorrelatedEq

theorem bothTrue_isCorrelatedEq :
    IsCorrelatedEq boolForm (euPreference coordinationUtility) (PMF.pure bothTrue) :=
  bothTrue_isNash.isCorrelatedEq

/-- A genuinely correlated recommendation: the two players receive the same
fair Boolean, so both diagonal profiles occur and neither crossed profile does.
-/
def diagonalLaw : PMF (Profile boolForm.sig) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure bothFalse) (PMF.pure bothTrue)

theorem mem_support_diagonalLaw_iff {profile : Profile boolForm.sig} :
    profile ∈ diagonalLaw.support ↔ profile = bothFalse ∨ profile = bothTrue := by
  constructor
  · intro hsupport
    by_contra hnot
    have hfalse : profile ≠ bothFalse := fun heq => hnot (Or.inl heq)
    have htrue : profile ≠ bothTrue := fun heq => hnot (Or.inr heq)
    have hzero : diagonalLaw profile = 0 := by
      simp [diagonalLaw, mix_apply, PMF.pure_apply, hfalse, htrue]
    exact ((PMF.mem_support_iff diagonalLaw profile).mp hsupport) hzero
  · rintro (rfl | rfl) <;> rw [PMF.mem_support_iff]
    · norm_num [diagonalLaw, mix_apply, PMF.pure_apply]
    · norm_num [diagonalLaw, mix_apply, PMF.pure_apply]

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

/-- The fair diagonal recommendation is a mixture of two pure equilibria. -/
theorem diagonalLaw_isCorrelatedEq :
    IsCorrelatedEq boolForm (euPreference coordinationUtility) diagonalLaw :=
  by
    simpa [diagonalLaw] using
      (IsCorrelatedEq.mix (euPreference_convex coordinationUtility)
        bothFalse_isCorrelatedEq bothTrue_isCorrelatedEq
        (1 / 2) (by norm_num) (by norm_num))

theorem diagonalLaw_local_obedience :
    ∀ who recommended replacement,
      ∀ hrecommended : recommended ∈
        (diagonalLaw.map fun profile => profile who).support,
        euPreference coordinationUtility who
          (boolForm.outcomeLaw (fiberPosterior diagonalLaw (fun profile => profile who)
            recommended hrecommended))
          ((fiberPosterior diagonalLaw (fun profile => profile who)
            recommended hrecommended).bind fun profile =>
              boolForm.play (Profile.update profile who replacement)) := by
  intro who recommended replacement hrecommended
  exact diagonalLaw_isCorrelatedEq.conditional_obedience who recommended replacement
    hrecommended
theorem crossedRecommendedFalse :
    ∃ profile : Profile boolForm.sig,
      profile ∈ {candidate | candidate false = false} ∧
        profile ∈ (PMF.pure crossed).support := by
  exact ⟨crossed, rfl, by simp⟩

/-- The local interface also exposes a failed recommendation directly: at the
crossed profile, player `false` profitably switches from `false` to `true`. -/
theorem pure_crossed_not_isCorrelatedEq :
    ¬ IsCorrelatedEq boolForm (euPreference coordinationUtility)
      (PMF.pure crossed) := by
  intro hce
  have hrecommended : false ∈
      ((PMF.pure crossed).map fun profile => profile false).support := by
    simp [crossed]
  have hposterior :
      fiberPosterior (PMF.pure crossed) (fun profile => profile false)
        false hrecommended = PMF.pure crossed := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro profile hprofile
    rw [fiberPosterior_support] at hprofile
    apply Set.mem_singleton_iff.mpr
    simpa [crossed] using hprofile.2
  have hpref := hce.conditional_obedience false false true hrecommended
  rw [hposterior] at hpref
  have hpref' : euPreference coordinationUtility false (PMF.pure crossed)
      (PMF.pure (Profile.update crossed false true)) := by
    simpa [boolForm, GameForm.outcomeLaw] using hpref
  have hle : coordinationUtility (Profile.update crossed false true) false ≤
      coordinationUtility crossed false := by
    exact (euPreference_pure_iff coordinationUtility false crossed
      (Profile.update crossed false true)).mp hpref'
  norm_num [coordinationUtility, crossed, Profile.update] at hle

end GameTheory.Tests.CorrelatedDominance
