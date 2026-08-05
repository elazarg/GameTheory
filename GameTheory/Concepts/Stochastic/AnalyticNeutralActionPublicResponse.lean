/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticFinkPublicResponse
import GameTheory.Concepts.Stochastic.PlayerNeutralBiasAlternative

/-!
# Analytic public responses from a positive endpoint neutral action

A continuation-neutral action with positive endpoint bias charge is already
an operational public response at the endpoint.  Analyticity makes this
response persistent: the same actual action has positive total Bellman charge
on a punctured neighborhood, with a power-law margin.

Moreover, one of two fixed operational branches persists.  If the endpoint
stage gain is positive, the same stage response remains positive.  Otherwise
the endpoint continuation gain is positive, and the endpoint coordinate
monitor extracted from that gain keeps positive forward drift.  Thus no
time-dependent action, sign, or monitor is selected.

Continuation neutrality itself is only an endpoint condition.  This theorem
does not claim that the continuation gain against the endpoint value remains
zero away from the endpoint.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Package a continuation-neutral action as the actual forward response
index used by the analytic public-response API. -/
def ContinuationNeutralAction.forwardResponse
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.ContinuationNeutralAction who) :
    Σ owner : ι, G.State × G.Act owner :=
  ⟨who, response.source, response.1.2⟩

omit [DecidableEq G.State] in
/-- A fixed continuation-neutral action with positive endpoint bias charge
lifts to one fixed analytic forward public response on a punctured
neighborhood.

The returned `AnalyticForwardFinkPublicResponse germ B 0` records both a
power-law lower bound for the action's total `B`-charge and a stabilized
stage-or-transition response. -/
theorem exists_analyticForwardFinkPublicResponse_of_neutralActionCharge_pos
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (response : germ.ContinuationNeutralAction who)
    (hpositive : 0 < germ.neutralActionCharge B who response) :
    Nonempty (AnalyticForwardFinkPublicResponse germ B 0) := by
  classical
  let forward := response.forwardResponse
  let supported :
      (Σ owner : ι, G.State × G.Act owner) → Bool :=
    fun _ => true
  let charge : ℝ → ℝ := fun t =>
    germ.rawFinkObstructionMass supported B 0 t (Sum.inr forward)
  have hchargeAnalytic : AnalyticAt ℝ charge 0 := by
    exact germ.analytic_rawFinkObstructionMass
      supported B 0 (Sum.inr forward)
  have hchargeZero :
      charge 0 = germ.neutralActionCharge B who response := by
    simp only [charge, AnalyticBellmanGerm.rawFinkObstructionMass,
      supported, if_true, forward, ContinuationNeutralAction.forwardResponse]
    rw [germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint]
    rw [germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint]
    simp only [sub_zero, neutralActionCharge]
  have hchargePositive :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < charge t := by
    have hnear : ∀ᶠ t in nhds 0, 0 < charge t :=
      hchargeAnalytic.continuousAt.tendsto.eventually_const_lt
        (hchargeZero ▸ hpositive)
    exact hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨chargeOrder, chargeMargin, hchargeMargin, hchargePower⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      hchargeAnalytic hchargePositive
  have heventualCharge :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          supported forward = true ∧
          chargeMargin * t ^ chargeOrder ≤
            germ.rawFinkObstructionMass supported B 0 t
              (Sum.inr forward) ∧
          0 <
            germ.rawFinkObstructionMass supported B 0 t
              (Sum.inr forward) := by
    filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
      hchargePower, hchargePositive] with t ht hpower hpos
    refine ⟨ht, ?_⟩
    refine ⟨rfl, ?_⟩
    change
      chargeMargin * t ^ chargeOrder ≤ charge t ∧ 0 < charge t
    simpa only [sub_zero] using And.intro hpower hpos
  by_cases hstage :
      0 <
        G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2
  · let stage : ℝ → ℝ := fun t =>
      germ.rawPureDeviationStageGainCurve
        t response.source who response.1.2
    have hstageAnalytic : AnalyticAt ℝ stage 0 := by
      exact
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStageGainCurve
              response.source) who) response.1.2)
    have hstageZero :
        stage 0 =
          G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 := by
      exact germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint
        response.source who response.1.2
    have hstagePositive :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < stage t := by
      have hnear : ∀ᶠ t in nhds 0, 0 < stage t :=
        hstageAnalytic.continuousAt.tendsto.eventually_const_lt
          (hstageZero ▸ hstage)
      exact hnear.filter_mono nhdsWithin_le_nhds
    obtain ⟨order, margin, hmargin, hpower⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        hstageAnalytic hstagePositive
    have heventualStage :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            margin * t ^ order ≤
              germ.rawPureDeviationStageGainCurve
                t forward.2.1 forward.1 forward.2.2 ∧
            0 <
              germ.rawPureDeviationStageGainCurve
                t forward.2.1 forward.1 forward.2.2 := by
      filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
        hpower, hstagePositive] with t ht hp hpos
      simpa only [sub_zero, stage, forward,
        ContinuationNeutralAction.forwardResponse] using
          And.intro ht (And.intro hp hpos)
    exact ⟨{
      supported := supported
      response := forward
      chargeOrder := chargeOrder
      chargeMargin := chargeMargin
      chargeMargin_pos := hchargeMargin
      eventual_charge := heventualCharge
      branch := Sum.inl {
        order := order
        margin := margin
        margin_pos := hmargin
        eventual := heventualStage } }⟩
  · have hcontinuation :
        0 <
          G.finkContinuationGain B germ.endpointFinkPoint
            response.source who response.1.2 := by
      dsimp only [neutralActionCharge] at hpositive
      linarith
    let endpointCharge :=
      G.finkPublicTransitionChargeOfContinuationGainPos
        germ.endpointFinkPoint B response.source who
          response.1.2 hcontinuation
    let monitor : PMFCoordinateMonitor G.State :=
      endpointCharge.monitor
    let drift : ℝ → ℝ := fun t =>
      analyticFinkMonitorDrift germ forward monitor t
    have hdriftAnalytic : AnalyticAt ℝ drift 0 := by
      have hdifference :
          AnalyticAt ℝ
            (fun t =>
              germ.rawPureDeviationStateKernelCurve
                  t response.source who response.1.2 monitor.1 -
                germ.rawStateKernelCurve t response.source monitor.1) 0 :=
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStateKernelCurve
                response.source) who) response.1.2)
          monitor.1).sub
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawStateKernelCurve response.source)
              monitor.1)
      convert
        (hdifference.const_smul
          (c := responseOrientation monitor.2)) using 1
      ext t
      simp only [drift, analyticFinkMonitorDrift, forward,
        ContinuationNeutralAction.forwardResponse,
        Pi.smul_apply, smul_eq_mul]
    have hdriftZero : 0 < drift 0 := by
      have hforward := endpointCharge.forward_positive
      rw [expect_pmfCoordinateTestScore] at hforward
      simpa only [drift, analyticFinkMonitorDrift, forward,
        ContinuationNeutralAction.forwardResponse, monitor,
        responseOrientation,
        germ.rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint,
        germ.rawStateKernelCurve_zero_eq_finkStateKernel] using hforward
    have hdriftPositive :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < drift t := by
      have hnear : ∀ᶠ t in nhds 0, 0 < drift t :=
        hdriftAnalytic.continuousAt.tendsto.eventually_const_lt
          hdriftZero
      exact hnear.filter_mono nhdsWithin_le_nhds
    obtain ⟨order, margin, hmargin, hpower⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        hdriftAnalytic hdriftPositive
    have heventualTransition :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            margin * t ^ order ≤
              analyticFinkMonitorDrift germ forward monitor t ∧
            0 < analyticFinkMonitorDrift germ forward monitor t := by
      filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
        hpower, hdriftPositive] with t ht hp hpos
      simpa only [sub_zero, drift] using
        And.intro ht (And.intro hp hpos)
    exact ⟨{
      supported := supported
      response := forward
      chargeOrder := chargeOrder
      chargeMargin := chargeMargin
      chargeMargin_pos := hchargeMargin
      eventual_charge := heventualCharge
      branch := Sum.inr {
        monitor := monitor
        order := order
        margin := margin
        margin_pos := hmargin
        eventual := heventualTransition } }⟩

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
