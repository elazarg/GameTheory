/-
# Correlation and strict dominance

Correlated equilibrium has an operational reading after a recommendation is
observed: conditional on receiving an action of positive probability, obeying
is at least as good as replacing it.  That conditional statement is the bridge
from correlation to the canonical relative-dominance predicate in `Response`.

The results are specialized to expected utility.  They introduce neither a
second equilibrium predicate nor a second conditioning interface, and they do
not require finite strategy carriers.

Primary reference: R. J. Aumann, “Subjectivity and Correlation in Randomized
Strategies,” *Journal of Mathematical Economics* 1 (1974).
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι

variable {ι : Type uι} [DecidableEq ι]
variable {F : GameForm ι} {utility : F.sig.Outcome → ι → ℝ}

/-- Conditional obedience: after a positive-probability recommendation,
following it weakly beats every fixed replacement in conditional expected
utility. -/
theorem IsCorrelatedEq.conditional_obedience
    {law : FinDist (Profile F.sig)}
    (hce : IsCorrelatedEq F (euPreference utility) law)
    (who : ι) (recommended replacement : F.sig.Strategy who)
    (hrecommended :
      ∃ profile : Profile F.sig,
        profile ∈ {candidate | candidate who = recommended} ∧ profile ∈ law.support) :
    (law.condOn {profile | profile who = recommended} hrecommended).expect
        (fun profile => expectedUtility utility who (F.play profile)) ≥
      (law.condOn {profile | profile who = recommended} hrecommended).expect
        (fun profile => expectedUtility utility who
          (F.play (Profile.update profile who replacement))) := by
  classical
  let respond : F.sig.Strategy who → F.sig.Strategy who :=
    fun action => if action = recommended then replacement else action
  have hglobal := (isCorrelatedEq_iff law).mp hce who respond
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind] at hglobal
  have hconditional := FinDist.expect_condOn_le_of_expect_le_of_eq_off law
    (S := {profile | profile who = recommended})
    (f := fun profile => expectedUtility utility who
      (F.play (Profile.update profile who (respond (profile who)))))
    (g := fun profile => expectedUtility utility who (F.play profile))
    hrecommended hglobal (by
      intro profile _ hnot
      have hne : profile who ≠ recommended := by
        simpa only [Set.mem_setOf_eq] using hnot
      simp [respond, hne, Profile.update_eq_self])
  have hdeviation :
      (law.condOn {profile | profile who = recommended} hrecommended).expect
          (fun profile => expectedUtility utility who
            (F.play (Profile.update profile who (respond (profile who))))) =
        (law.condOn {profile | profile who = recommended} hrecommended).expect
          (fun profile => expectedUtility utility who
            (F.play (Profile.update profile who replacement))) := by
    apply FinDist.expect_congr
    intro profile hprofile
    have hreco :=
      (FinDist.support_condOn law {profile | profile who = recommended}
        hrecommended hprofile).1
    have hreco' : profile who = recommended := by
      simpa only [Set.mem_setOf_eq] using hreco
    simp [respond, hreco']
  rwa [hdeviation] at hconditional

/-- A correlated equilibrium never recommends an action that is strictly
dominated on a product set carrying the whole support.  The relative form is
the one needed by iterated elimination: the product set may shrink between
rounds. -/
theorem IsCorrelatedEq.support_avoids_strictlyDominatedOn
    {law : FinDist (Profile F.sig)}
    (hce : IsCorrelatedEq F (euPreference utility) law)
    (allowed : ∀ j, Set (F.sig.Strategy j))
    (hsupport : ∀ profile ∈ law.support, ∀ j, profile j ∈ allowed j)
    (who : ι) {preferred dominated : F.sig.Strategy who}
    (hdom : StrictlyDominatesOn F (euPreference utility) who allowed preferred dominated) :
    ∀ profile ∈ law.support, profile who ≠ dominated := by
  intro witness hwitness heq
  have hrecommended :
      ∃ profile : Profile F.sig,
        profile ∈ {candidate | candidate who = dominated} ∧ profile ∈ law.support :=
    ⟨witness, heq, hwitness⟩
  have hobey := hce.conditional_obedience who dominated preferred hrecommended
  let conditional := law.condOn {profile | profile who = dominated} hrecommended
  let gain : Profile F.sig → ℝ := fun profile =>
    expectedUtility utility who (F.play profile) -
      expectedUtility utility who (F.play (Profile.update profile who preferred))
  have hnonpos : ∀ profile ∈ conditional.support, gain profile ≤ 0 := by
    intro profile hprofile
    have hbase := FinDist.support_condOn law
      {profile | profile who = dominated} hrecommended hprofile
    have hstrict := hdom profile (hsupport profile hbase.2)
    have hself : Profile.update profile who dominated = profile := by
      rw [← hbase.1]
      exact Profile.update_eq_self profile who
    simp only [Preference.strict] at hstrict
    rw [hself] at hstrict
    exact sub_nonpos.mpr hstrict.1
  have hwitnessConditional : witness ∈ conditional.support :=
    FinDist.mem_support_condOn law {profile | profile who = dominated}
      hrecommended heq hwitness
  have hstrictWitness : gain witness < 0 := by
    have hstrict := hdom witness (hsupport witness hwitness)
    have hself : Profile.update witness who dominated = witness := by
      rw [← heq]
      exact Profile.update_eq_self witness who
    simp only [Preference.strict] at hstrict
    rw [hself] at hstrict
    exact sub_neg.mpr (lt_of_le_of_ne hstrict.1 fun h => hstrict.2 h.symm.le)
  have hnegative : conditional.expect gain < 0 :=
    FinDist.expect_lt_of_mem_support conditional gain 0 hnonpos
      hwitnessConditional hstrictWitness
  have haccounting : conditional.expect gain =
      conditional.expect (fun profile => expectedUtility utility who (F.play profile)) -
        conditional.expect (fun profile => expectedUtility utility who
          (F.play (Profile.update profile who preferred))) :=
    FinDist.expect_sub ..
  rw [haccounting] at hnegative
  linarith

/-- A coarse correlated equilibrium supported at a profile of strictly
dominant actions is concentrated coordinatewise at those actions. -/
theorem IsCoarseCorrelatedEq.support_plays_strictDominant
    {law : FinDist (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law)
    (who : ι) (dominant : F.sig.Strategy who)
    (hdom : IsStrictDominant F (euPreference utility) who dominant) :
    ∀ profile ∈ law.support, profile who = dominant := by
  intro witness hwitness
  by_contra hne
  let gain : Profile F.sig → ℝ := fun profile =>
    expectedUtility utility who (F.play profile) -
      expectedUtility utility who (F.play (Profile.update profile who dominant))
  have hnonpos : ∀ profile ∈ law.support, gain profile ≤ 0 := by
    intro profile _
    by_cases heq : profile who = dominant
    · simp [gain, ← heq, Profile.update_eq_self]
    · have hstrict := hdom (profile who) heq profile (fun _ => Set.mem_univ _)
      have hself : Profile.update profile who (profile who) = profile :=
        Profile.update_eq_self profile who
      simp only [Preference.strict] at hstrict
      rw [hself] at hstrict
      exact sub_nonpos.mpr hstrict.1
  have hstrictWitness : gain witness < 0 := by
    have hstrict := hdom (witness who) hne witness (fun _ => Set.mem_univ _)
    have hself : Profile.update witness who (witness who) = witness :=
      Profile.update_eq_self witness who
    simp only [Preference.strict] at hstrict
    rw [hself] at hstrict
    exact sub_neg.mpr (lt_of_le_of_ne hstrict.1 fun h => hstrict.2 h.symm.le)
  have hnegative : law.expect gain < 0 :=
    FinDist.expect_lt_of_mem_support law gain 0 hnonpos hwitness hstrictWitness
  have hdeviation := (isCoarseCorrelatedEq_iff law).mp hcce who dominant
  rw [euPreference_apply, expectedUtility_outcomeLaw, expectedUtility_bind] at hdeviation
  have haccounting : law.expect gain =
      law.expect (fun profile => expectedUtility utility who (F.play profile)) -
        law.expect (fun profile => expectedUtility utility who
          (F.play (Profile.update profile who dominant))) :=
    FinDist.expect_sub ..
  rw [haccounting] at hnegative
  linarith

/-- If every coordinate of a profile is strictly dominant, that profile's
point mass is the unique coarse correlated equilibrium. -/
theorem strictDominant_isCoarseCorrelatedEq_iff
    {profile : Profile F.sig}
    (hdom : ∀ who, IsStrictDominant F (euPreference utility) who (profile who))
    {law : FinDist (Profile F.sig)} :
    IsCoarseCorrelatedEq F (euPreference utility) law ↔ law = FinDist.pure profile := by
  constructor
  · intro hcce
    apply FinDist.eq_pure_of_support_subset_singleton
    intro candidate hcandidate
    apply Set.mem_singleton_iff.mpr
    funext who
    exact hcce.support_plays_strictDominant who (profile who) (hdom who)
      candidate hcandidate
  · rintro rfl
    exact (isNash_of_forall_isStrictDominant (euPreference_reflexive utility) hdom).isCorrelatedEq
      |>.isCoarseCorrelatedEq

/-- Strictly dominant actions also pin the unique correlated equilibrium, as
an immediate consequence of the coarse result. -/
theorem strictDominant_isCorrelatedEq_iff
    {profile : Profile F.sig}
    (hdom : ∀ who, IsStrictDominant F (euPreference utility) who (profile who))
    {law : FinDist (Profile F.sig)} :
    IsCorrelatedEq F (euPreference utility) law ↔ law = FinDist.pure profile := by
  constructor
  · intro hce
    exact (strictDominant_isCoarseCorrelatedEq_iff hdom).mp hce.isCoarseCorrelatedEq
  · rintro rfl
    exact (isNash_of_forall_isStrictDominant (euPreference_reflexive utility) hdom).isCorrelatedEq

end GameTheory
