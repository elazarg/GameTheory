/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkPublicResponse
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticStageBranchStabilization

/-!
# Analytic stage-response dichotomy

Equal continuation data remove the transition term from the Fink obstruction
mass. Consequently, the stabilized obstruction branch selects one fixed
actual action whose stage gain is positive with a power-law margin.

This packages the analytic algebra into the exact operational dichotomy used
by a public-response construction: moving harmonic adjustment, or a fixed
player-owned stage response.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticForwardFinkPublicResponse

omit [DecidableEq G.State] in
/-- With equal continuation data, the selected positive Fink mass is itself
the selected action's stage gain. -/
def toStageOfSameContinuation
    {germ : G.AnalyticBellmanGerm}
    {H : G.State → Payoff ι}
    (response : AnalyticForwardFinkPublicResponse germ H H) :
    AnalyticFinkStagePublicResponse germ response.response where
  order := response.chargeOrder
  margin := response.chargeMargin
  margin_pos := response.chargeMargin_pos
  eventual := by
    filter_upwards [response.eventual_charge] with t ht
    have hmass :
        germ.rawFinkObstructionMass response.supported H H t
            (Sum.inr response.response) =
          germ.rawPureDeviationStageGainCurve
            t response.response.2.1 response.response.1
              response.response.2.2 := by
      rw [
        germ.rawFinkObstructionMass_sameContinuation_action
          response.supported H t response.response,
        ht.2.1
      ]
      simp
    refine ⟨ht.1, ?_⟩
    rw [← hmass]
    exact ht.2.2

end AnalyticForwardFinkPublicResponse

namespace AnalyticBellmanGerm

omit [DecidableEq G.State] in
/-- The stabilized equal-continuation branch is either moving harmonic or
one fixed actual action with an eventually positive power-law stage margin. -/
theorem stageHarmonicAdjustment_or_analyticStagePublicResponse
    [Nonempty G.State] [Nonempty ι] [∀ i, Nonempty (G.Act i)]
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          ∃ A : G.State → Payoff ι,
            G.finkContinuationResidualVector A
                (germ.finkPointAt ht) = 0 ∧
              ∀ s who (d : G.Act who),
                G.finkProfile
                    (germ.finkPointAt ht) s who d ≠ 0 →
                  G.finkContinuationGain A
                      (germ.finkPointAt ht) s who d =
                    G.finkStageGain
                      (germ.finkPointAt ht) s who d) ∨
      ∃ response : Σ who : ι, G.State × G.Act who,
        Nonempty (AnalyticFinkStagePublicResponse germ response) := by
  rcases germ.stageResponseBranch_eventually_stabilizes H with
    hAdjustment | hObstruction
  · exact Or.inl hAdjustment
  · obtain ⟨response⟩ :=
      exists_analyticForwardFinkPublicResponse germ H H
        (hObstruction.mono fun _ ht => ht.2)
    exact Or.inr
      ⟨response.response, ⟨response.toStageOfSameContinuation⟩⟩

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
