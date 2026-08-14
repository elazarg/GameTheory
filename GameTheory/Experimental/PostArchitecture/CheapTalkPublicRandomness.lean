/-
# EXP-047: mixed cheap talk as public randomization

The experiment pushes independent mixed play of the static cheap-talk
extension through its realized action profile. Its hostile consumer lifts an
arbitrary recommendation-reading base deviation and proves that a mixed Nash
profile induces a base correlated equilibrium.
-/

import GameTheory.Core.CheapTalk

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.CheapTalkPublicRandomness

open GameTheory GameTheory.Probability

universe uι us uo um

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Mapping one coordinate of an independent profile law is the independent
product with that marginal mapped. This is the probability identity behind the
public-randomness bridge. -/
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

namespace CheapTalk

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
          (liftActionDeviation C who respond (profile who))) =
      Profile.update (C.actionProfile profile) who
        (respond (C.actionProfile profile who)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp only [GameTheory.GameForm.CheapTalkExtension.actionProfile,
      Profile.update_same, liftActionDeviation]
    rw [C.messageProfile_update_sameMessage]
  · simp only [GameTheory.GameForm.CheapTalkExtension.actionProfile,
      Profile.update_of_ne _ _ hi,
      liftActionDeviation]
    rw [C.messageProfile_update_sameMessage]

/-- Mapping the deviator's mixed cheap-talk strategy through the lifted
deviation commutes with the induced base action-profile law. -/
theorem mixedActionLaw_update_map_liftActionDeviation
    (mixedProfile : Profile C.signature.mixed) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    mixedActionLaw C
        (Profile.update mixedProfile who
          ((mixedProfile who).map (liftActionDeviation C who respond))) =
      (mixedActionLaw C mixedProfile).map
        (fun profile =>
          Profile.update profile who (respond (profile who))) := by
  unfold mixedActionLaw
  rw [← pi_map_recommendation C.signature mixedProfile who
    (liftActionDeviation C who respond)]
  rw [FinDist.map_comp, FinDist.map_comp]
  congr 1
  funext profile
  exact actionProfile_update_liftActionDeviation C profile who respond

omit [DecidableEq ι] in
/-- Mixed play of the extension is base play averaged over its induced action
law. -/
theorem mixed_play_eq_outcomeLaw_mixedActionLaw
    (mixedProfile : Profile C.signature.mixed) :
    C.form.mixed.play mixedProfile =
      F.outcomeLaw (mixedActionLaw C mixedProfile) := by
  unfold mixedActionLaw GameTheory.GameForm.outcomeLaw
  rw [FinDist.bind_map]

/-- The mixed-extension deviation law is exactly the base correlated-deviation
outcome law after lifting the response. -/
theorem mixed_play_update_map_liftActionDeviation
    (mixedProfile : Profile C.signature.mixed) (who : ι)
    (respond : F.sig.Strategy who → F.sig.Strategy who) :
    C.form.mixed.play
        (Profile.update mixedProfile who
          ((mixedProfile who).map (liftActionDeviation C who respond))) =
      (mixedActionLaw C mixedProfile).bind fun profile =>
        F.play
          (Profile.update profile who (respond (profile who))) := by
  rw [mixed_play_eq_outcomeLaw_mixedActionLaw C,
    mixedActionLaw_update_map_liftActionDeviation C]
  unfold GameTheory.GameForm.outcomeLaw
  rw [FinDist.bind_map]

/-- A mixed Nash profile of observable static cheap talk induces a correlated
equilibrium of the base form. No intermediate communication state is needed,
and the result is preference-parametric. -/
theorem mixedNash_mixedActionLaw_isCorrelatedEq
    (preference : WeakPreference ι F.sig.Outcome)
    (mixedProfile : Profile C.signature.mixed)
    (hnash : IsNash C.form.mixed preference mixedProfile) :
    IsCorrelatedEq F preference (mixedActionLaw C mixedProfile) := by
  rw [isNash_iff] at hnash
  rw [isCorrelatedEq_iff]
  intro who respond
  have hdeviation :=
    hnash who
      ((mixedProfile who).map (liftActionDeviation C who respond))
  rw [mixed_play_eq_outcomeLaw_mixedActionLaw C,
    mixed_play_update_map_liftActionDeviation C] at hdeviation
  exact hdeviation

end CheapTalk

end GameTheory.Experimental.PostArchitecture.CheapTalkPublicRandomness
