/-
# EXP-047: mixed cheap talk as public randomization

This experiment is a consumer of the canonical recommendation-law and
cheap-talk randomization results.
-/

import GameTheory.Core.CheapTalkRandomization

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.CheapTalkPublicRandomness

open GameTheory

universe uι us uo um

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Coordinate recommendation responses commute with the canonical
independent-profile law. -/
theorem recommendation_law_response (sig : GameSignature ι)
    (mixedProfile : Profile sig.mixed) (who : ι)
    (respond : sig.Strategy who → sig.Strategy who) :
    (GameTheory.Math.Probability.independentProduct mixedProfile).map
        (fun profile => Profile.update profile who (respond (profile who))) =
      GameTheory.Math.Probability.independentProduct
        (Profile.update mixedProfile who ((mixedProfile who).map respond)) :=
  GameForm.pi_map_recommendation sig mixedProfile who respond

namespace CheapTalk

variable {F : GameForm.{uι, us, uo} ι}
  (C : F.CheapTalkExtension.{uι, us, uo, um})

/-- Mixed Nash cheap talk induces correlated equilibrium through the canonical
action-profile law and lifted deviation. -/
theorem mixedNash_induces_correlatedEq
    (preference : WeakPreference ι F.sig.Outcome)
    (mixedProfile : Profile C.signature.mixed)
    (hnash : IsNash C.form.mixed preference mixedProfile) :
    IsCorrelatedEq F preference (C.mixedActionLaw mixedProfile) :=
  C.mixedNash_mixedActionLaw_isCorrelatedEq preference mixedProfile hnash

end CheapTalk

end GameTheory.Experimental.PostArchitecture.CheapTalkPublicRandomness
