/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralScaledPotential

/-!
# Approximate Moving Combined Biases

A punctured player-neutral correction controls exactly the actions which
are continuation-neutral at the analytic endpoint.  Adding a nonnegative
multiple of the endpoint value can absorb the other actions, provided they
retain a strict moving continuation loss.  The same multiple also magnifies
the generally nonzero moving continuation gain of an endpoint-neutral
action.  Consequently the honest fixed-parameter conclusion has an error
term `c * ε`.

This file records only that finite-dimensional implication.  It makes no
claim that the error tends to zero along a parameter schedule.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Embed a scalar correction in one player's payoff coordinate. -/
def ownerCorrection
    (who : ι) (C : G.State → ℝ) :
    G.State → Payoff ι :=
  fun state owner => if owner = who then C state else 0

/-- The part of the moving corrected Bellman defect left after subtracting
the prescribed drift of the correction. -/
def playerNeutralCorrectedDefectAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ)
    (source : G.State) (action : G.Act who) : ℝ :=
  G.finkStageGain (germ.finkPointAt ht) source who action +
      G.finkContinuationGain
        (B - ownerCorrection who C)
        (germ.finkPointAt ht) source who action -
    G.finkContinuationResidual
      (ownerCorrection who C)
      (germ.finkPointAt ht) source who

/-- Add a multiple of the endpoint value to the moving corrected defect. -/
def playerNeutralCombinedDefectAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ) (c : ℝ)
    (source : G.State) (action : G.Act who) : ℝ :=
  germ.playerNeutralCorrectedDefectAt B ht who C source action +
    c * G.finkContinuationGain germ.endpointValue
      (germ.finkPointAt ht) source who action

omit [DecidableEq G.State] in
/-- The combined defect is the semantic corrected Bellman defect for
`B - C + c • endpointValue`. -/
theorem playerNeutralCombinedDefectAt_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ) (c : ℝ)
    (source : G.State) (action : G.Act who) :
    germ.playerNeutralCombinedDefectAt
        B ht who C c source action =
      G.finkStageGain (germ.finkPointAt ht) source who action +
          G.finkContinuationGain
            ((B - ownerCorrection who C) +
              c • germ.endpointValue)
            (germ.finkPointAt ht) source who action -
        G.finkContinuationResidual
          (ownerCorrection who C)
          (germ.finkPointAt ht) source who := by
  unfold playerNeutralCombinedDefectAt
    playerNeutralCorrectedDefectAt
  rw [G.finkContinuationGain_add,
    G.finkContinuationGain_smul]
  ring

omit [DecidableEq G.State] in
/-- **Sharp fixed-parameter moving combined-bias bound.**

Endpoint-neutral actions inherit a nonpositive corrected defect from the
scaled-potential correction, but their moving endpoint-value gain may be as
large as `ε`.  Every other action is assumed to have corrected defect at
most `M` and endpoint-value gain at most `-δ`.  If `M ≤ c * δ`, adding
`c • endpointValue` controls every pure action up to `c * ε`. -/
theorem playerNeutralCombinedDefectAt_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ)
    (hcorrection :
      germ.IsPlayerNeutralBiasCorrectionAt B who ht C)
    (δ M ε c : ℝ)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (hM : M ≤ c * δ)
    (hstrict :
      ∀ source (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
              (germ.finkPointAt ht) source who action ≤ -δ ∧
            germ.playerNeutralCorrectedDefectAt
              B ht who C source action ≤ M)
    (hneutralGain :
      ∀ source (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action = 0 →
          G.finkContinuationGain germ.endpointValue
              (germ.finkPointAt ht) source who action ≤ ε) :
    ∀ source (action : G.Act who),
      germ.playerNeutralCombinedDefectAt
          B ht who C c source action ≤ c * ε := by
  intro source action
  by_cases neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0
  · let response : germ.ContinuationNeutralAction who :=
      ⟨(source, action), neutral⟩
    have corrected := hcorrection.2 response
    have defect_nonpos :
        germ.playerNeutralCorrectedDefectAt
          B ht who C source action ≤ 0 := by
      change
        G.finkStageGain (germ.finkPointAt ht) source who action +
            G.finkContinuationGain
              (B - ownerCorrection who C)
              (germ.finkPointAt ht) source who action ≤
          G.finkContinuationResidual
            (ownerCorrection who C)
            (germ.finkPointAt ht) source who
        at corrected
      unfold playerNeutralCorrectedDefectAt ownerCorrection
      exact sub_nonpos.mpr corrected
    have gain_le := hneutralGain source action neutral
    unfold playerNeutralCombinedDefectAt
    nlinarith
  · obtain ⟨gain_le, defect_le⟩ :=
      hstrict source action neutral
    have error_nonneg : 0 ≤ c * ε :=
      mul_nonneg hc hε
    unfold playerNeutralCombinedDefectAt
    nlinarith

omit [DecidableEq G.State] in
/-- The pure-action bound extends to every behavioral mixture by taking
expectation. -/
theorem expect_playerNeutralCombinedDefectAt_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (who : ι) (C : G.State → ℝ)
    (hcorrection :
      germ.IsPlayerNeutralBiasCorrectionAt B who ht C)
    (δ M ε c : ℝ)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (hM : M ≤ c * δ)
    (hstrict :
      ∀ source (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
              (germ.finkPointAt ht) source who action ≤ -δ ∧
            germ.playerNeutralCorrectedDefectAt
              B ht who C source action ≤ M)
    (hneutralGain :
      ∀ source (action : G.Act who),
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action = 0 →
          G.finkContinuationGain germ.endpointValue
              (germ.finkPointAt ht) source who action ≤ ε)
    (source : G.State) (deviation : PMF (G.Act who)) :
    expect deviation
        (germ.playerNeutralCombinedDefectAt
          B ht who C c source) ≤
      c * ε := by
  calc
    expect deviation
        (germ.playerNeutralCombinedDefectAt
          B ht who C c source) ≤
        expect deviation (fun _ => c * ε) := by
      apply expect_mono
      exact germ.playerNeutralCombinedDefectAt_le
        B ht who C hcorrection δ M ε c hc hε hM
          hstrict hneutralGain source
    _ = c * ε := expect_const deviation _

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
