/-
# Mixed cheap talk as public randomization

Independent mixed play of observable one-stage cheap talk induces a finite law
over base action profiles. Exact commutation with recommendation-dependent
deviations turns mixed Nash of the extension into correlated equilibrium of the
base form without introducing a communication-specific solution concept.
-/

import GameTheory.Core.CheapTalk

noncomputable section

namespace GameTheory

open Probability

universe uι us uo um

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

namespace GameForm

/-- Mapping one coordinate of an independent profile law is the independent
product with that marginal mapped. -/
theorem pi_map_recommendation (sig : GameSignature ι)
    (mixedProfile : Profile sig.mixed) (who : ι)
    (respond : sig.Strategy who → sig.Strategy who) :
    (FinDist.pi mixedProfile).map
        (fun profile =>
          Profile.update profile who (respond (profile who))) =
      FinDist.pi
        (Profile.update mixedProfile who
          ((mixedProfile who).map respond)) := by
  rw [FinDist.pi_eq_map_product who mixedProfile, FinDist.map_comp]
  rw [FinDist.pi_eq_map_product who
    (Profile.update mixedProfile who ((mixedProfile who).map respond))]
  rw [Profile.update_same]
  have hrest :
      (fun j : {j // j ≠ who} =>
        (Profile.update mixedProfile who
          ((mixedProfile who).map respond)) j.1) =
        fun j : {j // j ≠ who} => mixedProfile j.1 := by
    funext j
    rw [Profile.update_of_ne _ _ j.2]
  rw [hrest]
  have hproduct :
      FinDist.product ((mixedProfile who).map respond)
          (FinDist.pi fun j : {j // j ≠ who} => mixedProfile j.1) =
        (FinDist.product (mixedProfile who)
          (FinDist.pi fun j : {j // j ≠ who} => mixedProfile j.1)).map
            (Prod.map respond id) := by
    rw [FinDist.map_product]
    simp
  rw [hproduct, FinDist.map_comp]
  congr 1
  funext pair
  apply (Equiv.piSplitAt who sig.Strategy).injective
  apply Prod.ext
  · simp
  · funext j
    simp [Profile.update_of_ne _ _ j.2]
    split
    · rename_i h
      exact False.elim (j.2 h)
    · rfl

namespace CheapTalkExtension

variable {F : GameForm.{uι, us, uo} ι}
  (C : F.CheapTalkExtension.{uι, us, uo, um})

/-- The base action-profile law induced by independent mixed cheap-talk
strategies. -/
def mixedActionLaw (mixedProfile : Profile C.signature.mixed) :
    FinDist (Profile F.sig) :=
  (FinDist.pi mixedProfile).map C.actionProfile

/-- Lift a base recommendation-reading deviation by retaining the message and
applying the deviation to every contingent base action. -/
def liftActionDeviation (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who)
    (strategy : C.Strategy who) : C.Strategy who :=
  (strategy.1, fun messages => respond (strategy.2 messages))

omit [Fintype ι] in
/-- Realized actions commute with the lifted recommendation deviation. -/
theorem actionProfile_update_liftActionDeviation
    (profile : Profile C.signature) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    C.actionProfile
        (Profile.update profile who
          (C.liftActionDeviation who respond (profile who))) =
      Profile.update (C.actionProfile profile) who
        (respond (C.actionProfile profile who)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp only [actionProfile, Profile.update_same, liftActionDeviation]
    rw [C.messageProfile_update_sameMessage]
  · simp only [actionProfile, Profile.update_of_ne _ _ hi,
      liftActionDeviation]
    rw [C.messageProfile_update_sameMessage]

/-- Mapping the deviator's mixed cheap-talk strategy through the lifted
deviation commutes with the induced base action-profile law. -/
theorem mixedActionLaw_update_map_liftActionDeviation
    (mixedProfile : Profile C.signature.mixed) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    C.mixedActionLaw
        (Profile.update mixedProfile who
          ((mixedProfile who).map (C.liftActionDeviation who respond))) =
      (C.mixedActionLaw mixedProfile).map
        (fun profile =>
          Profile.update profile who (respond (profile who))) := by
  unfold mixedActionLaw
  rw [← pi_map_recommendation C.signature mixedProfile who
    (C.liftActionDeviation who respond)]
  rw [FinDist.map_comp, FinDist.map_comp]
  congr 1
  funext profile
  exact C.actionProfile_update_liftActionDeviation profile who respond

omit [DecidableEq ι] in
/-- Mixed play of the extension is base play averaged over its induced action
law. -/
theorem mixed_play_eq_outcomeLaw_mixedActionLaw
    (mixedProfile : Profile C.signature.mixed) :
    C.form.mixed.play mixedProfile =
      F.outcomeLaw (C.mixedActionLaw mixedProfile) := by
  unfold mixedActionLaw GameForm.outcomeLaw
  rw [FinDist.bind_map]

/-- The mixed-extension deviation law is exactly the base correlated-deviation
outcome law after lifting the response. -/
theorem mixed_play_update_map_liftActionDeviation
    (mixedProfile : Profile C.signature.mixed) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    C.form.mixed.play
        (Profile.update mixedProfile who
          ((mixedProfile who).map (C.liftActionDeviation who respond))) =
      (C.mixedActionLaw mixedProfile).bind fun profile =>
        F.play
          (Profile.update profile who (respond (profile who))) := by
  rw [C.mixed_play_eq_outcomeLaw_mixedActionLaw,
    C.mixedActionLaw_update_map_liftActionDeviation]
  unfold GameForm.outcomeLaw
  rw [FinDist.bind_map]

/-- A mixed Nash profile of observable static cheap talk induces a correlated
equilibrium of the base form. The result is preference-parametric because the
proof preserves complete finite outcome laws. -/
theorem mixedNash_mixedActionLaw_isCorrelatedEq
    (preference : WeakPreference ι F.sig.Outcome)
    (mixedProfile : Profile C.signature.mixed)
    (hnash : IsNash C.form.mixed preference mixedProfile) :
    IsCorrelatedEq F preference (C.mixedActionLaw mixedProfile) := by
  rw [isNash_iff] at hnash
  rw [isCorrelatedEq_iff]
  intro who respond
  have hdeviation :=
    hnash who
      ((mixedProfile who).map (C.liftActionDeviation who respond))
  rw [C.mixed_play_eq_outcomeLaw_mixedActionLaw,
    C.mixed_play_update_map_liftActionDeviation] at hdeviation
  exact hdeviation

/-- The induced action law is consequently a coarse correlated equilibrium. -/
theorem mixedNash_mixedActionLaw_isCoarseCorrelatedEq
    (preference : WeakPreference ι F.sig.Outcome)
    (mixedProfile : Profile C.signature.mixed)
    (hnash : IsNash C.form.mixed preference mixedProfile) :
    IsCoarseCorrelatedEq F preference (C.mixedActionLaw mixedProfile) :=
  (C.mixedNash_mixedActionLaw_isCorrelatedEq preference mixedProfile
    hnash).isCoarseCorrelatedEq

end CheapTalkExtension
end GameForm
end GameTheory
