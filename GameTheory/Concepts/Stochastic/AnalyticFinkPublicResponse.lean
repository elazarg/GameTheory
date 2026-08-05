/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkActionWeightRepair
import GameTheory.Concepts.Stochastic.FinkConstraintPublicResponse

/-!
# Forward public responses from analytic Fink obstructions

The signed analytic obstruction may orient a statistical contrast in either
direction, so its selected signed coordinate is not automatically a
profitable forward deviation. The support-preserving analytic action repair
removes this ambiguity: every supported forward action has positive weight,
while the total Bellman target remains positive.

Consequently one fixed actual action has a positive Bellman gain on a
punctured neighborhood. Analyticity upgrades this to a power-law margin.
The gain then stabilizes into either a stage-payoff response or a
continuation response. In the latter case a fixed successor-state coordinate
gives a bounded, baseline-centered public monitor with its own power-law
margin.

The selected raw Fink mass is exactly stage gain plus continuation gain
against `H - K`. It becomes a generic continuation-constraint deficit only
after supplying the semantic equation recorded by
`FinkDeviationConstraintSemantics`; no such identification is inferred here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A fixed selected action whose stage gain is eventually positive with a
power-law margin. -/
structure AnalyticFinkStagePublicResponse
    (germ : G.AnalyticBellmanGerm)
    (response : Σ who : ι, G.State × G.Act who) where
  order : ℕ
  margin : ℝ
  margin_pos : 0 < margin
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        margin * t ^ order ≤
          germ.rawPureDeviationStageGainCurve
            t response.2.1 response.1 response.2.2 ∧
        0 <
          germ.rawPureDeviationStageGainCurve
            t response.2.1 response.1 response.2.2

/-- Oriented coordinate drift of one fixed public monitor along an analytic
forward-deviation branch. -/
def analyticFinkMonitorDrift
    (germ : G.AnalyticBellmanGerm)
    (response : Σ who : ι, G.State × G.Act who)
    (monitor : PMFCoordinateMonitor G.State)
    (t : ℝ) : ℝ :=
  responseOrientation monitor.2 *
    (germ.rawPureDeviationStateKernelCurve
        t response.2.1 response.1 response.2.2 monitor.1 -
      germ.rawStateKernelCurve t response.2.1 monitor.1)

/-- A fixed selected action and fixed public coordinate monitor whose
forward expected score is eventually positive with a power-law margin. -/
structure AnalyticFinkTransitionPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (response : Σ who : ι, G.State × G.Act who) where
  monitor : PMFCoordinateMonitor G.State
  order : ℕ
  margin : ℝ
  margin_pos : 0 < margin
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        margin * t ^ order ≤
          analyticFinkMonitorDrift germ response monitor t ∧
        0 < analyticFinkMonitorDrift germ response monitor t

/-- One fixed actual forward action extracted from an analytic obstruction.
Its Bellman charge is positive with a power-law margin and it has stabilized
to either a stage response or a fixed public transition monitor. -/
structure AnalyticForwardFinkPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι) where
  supported :
    (Σ who : ι, G.State × G.Act who) → Bool
  response : Σ who : ι, G.State × G.Act who
  chargeOrder : ℕ
  chargeMargin : ℝ
  chargeMargin_pos : 0 < chargeMargin
  eventual_charge :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        supported response = true ∧
        chargeMargin * t ^ chargeOrder ≤
          germ.rawFinkObstructionMass supported H K t
            (Sum.inr response) ∧
        0 <
          germ.rawFinkObstructionMass supported H K t
            (Sum.inr response)
  branch :
    AnalyticFinkStagePublicResponse germ response ⊕
      AnalyticFinkTransitionPublicResponse germ response

namespace AnalyticFinkStagePublicResponse

omit [DecidableEq G.State] in
/-- The raw stage margin is exactly a semantic stage-gain margin at every
valid positive parameter. -/
theorem eventually_semanticMargin
    {germ : G.AnalyticBellmanGerm}
    {response : Σ who : ι, G.State × G.Act who}
    (R : AnalyticFinkStagePublicResponse germ response) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        R.margin * t ^ R.order ≤
            G.finkStageGain (germ.finkPointAt ht)
              response.2.1 response.1 response.2.2 ∧
          0 <
            G.finkStageGain (germ.finkPointAt ht)
              response.2.1 response.1 response.2.2 := by
  filter_upwards [R.eventual] with t hresponse
  intro ht
  rw [← germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
  exact hresponse.2

end AnalyticFinkStagePublicResponse

namespace AnalyticFinkTransitionPublicResponse

/-- At every valid positive parameter where its drift is positive, the
analytic transition response is a concrete operational Fink monitor. -/
noncomputable def toFinkPublicTransitionChargeAt
    {germ : G.AnalyticBellmanGerm}
    {response : Σ who : ι, G.State × G.Act who}
    (R : AnalyticFinkTransitionPublicResponse germ response)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hpositive :
      0 < analyticFinkMonitorDrift germ response R.monitor t) :
    G.FinkPublicTransitionCharge
      (germ.finkPointAt ht)
      response.2.1 response.1 response.2.2 := by
  let baseline :=
    G.finkStateKernel (germ.finkPointAt ht) response.2.1
  let forward :=
    G.finkPureDeviationStateKernel
      (germ.finkPointAt ht)
      response.2.1 response.1 response.2.2
  have hdrift :
      0 <
        responseOrientation R.monitor.2 *
          ((forward R.monitor.1).toReal -
            (baseline R.monitor.1).toReal) := by
    simpa only [analyticFinkMonitorDrift, baseline, forward,
      germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
        ht response.2.1 response.1 response.2.2 R.monitor.1,
      germ.rawStateKernelCurve_eq_finkStateKernel
        ht response.2.1 R.monitor.1] using hpositive
  refine {
    monitor := R.monitor
    baseline_centered := ?_
    forward_positive := ?_
    score_bounded := ?_ }
  · exact expect_pmfCoordinateTestScore_baseline
      baseline R.monitor.1 R.monitor.2
  · rw [expect_pmfCoordinateTestScore]
    simpa only [baseline, forward, responseOrientation] using hdrift
  · intro destination
    exact abs_pmfCoordinateTestScore_le_one
      baseline R.monitor.1 R.monitor.2 destination

/-- The raw analytic monitor margin is exactly the expected public score
margin under the actual forward deviation. -/
theorem eventually_semanticMargin
    {germ : G.AnalyticBellmanGerm}
    {response : Σ who : ι, G.State × G.Act who}
    (R : AnalyticFinkTransitionPublicResponse germ response) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        R.margin * t ^ R.order ≤
            expect
              (G.finkPureDeviationStateKernel
                (germ.finkPointAt ht)
                response.2.1 response.1 response.2.2)
              (pmfCoordinateTestScore
                (G.finkStateKernel
                  (germ.finkPointAt ht) response.2.1)
                R.monitor.1 R.monitor.2) ∧
          0 <
            expect
              (G.finkPureDeviationStateKernel
                (germ.finkPointAt ht)
                response.2.1 response.1 response.2.2)
              (pmfCoordinateTestScore
                (G.finkStateKernel
                  (germ.finkPointAt ht) response.2.1)
                R.monitor.1 R.monitor.2) := by
  filter_upwards [R.eventual] with t hresponse
  intro ht
  rw [expect_pmfCoordinateTestScore]
  simpa only [analyticFinkMonitorDrift,
    germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
      ht response.2.1 response.1 response.2.2 R.monitor.1,
    germ.rawStateKernelCurve_eq_finkStateKernel
      ht response.2.1 R.monitor.1,
    responseOrientation] using hresponse.2

end AnalyticFinkTransitionPublicResponse

namespace AnalyticForwardFinkPublicResponse

omit [DecidableEq G.State] in
/-- On the stabilized support, the selected raw target coordinate is exactly
the actual forward action's stage-plus-continuation Bellman gain. -/
theorem eventual_charge_eq_actualBellmanGain
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticForwardFinkPublicResponse germ H K) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        germ.rawFinkObstructionMass C.supported H K t
            (Sum.inr C.response) =
          G.finkStageGain (germ.finkPointAt ht)
              C.response.2.1 C.response.1 C.response.2.2 +
            G.finkContinuationGain (H - K)
              (germ.finkPointAt ht)
              C.response.2.1 C.response.1 C.response.2.2 := by
  filter_upwards [C.eventual_charge] with t hcharge
  intro ht
  simp only [AnalyticBellmanGerm.rawFinkObstructionMass,
    hcharge.2.1, if_true]
  rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
  rw [germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt
    (H - K) ht]

/-- Eventually the analytic response supplies the concrete public-response
object used by `FinkConstraintPublicResponse` at every valid parameter. -/
theorem eventually_finkPublicConstraintResponseAt
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticForwardFinkPublicResponse germ H K) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        Nonempty
          (G.FinkPublicConstraintResponse
            (germ.finkPointAt ht) (H - K)
            C.response.2.1 C.response.1 C.response.2.2) := by
  cases C.branch with
  | inl stage =>
      filter_upwards [stage.eventual] with t hstage
      intro ht
      have hpositive :
          0 <
            G.finkStageGain (germ.finkPointAt ht)
              C.response.2.1 C.response.1 C.response.2.2 := by
        rw [← germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
        exact hstage.2.2
      exact ⟨FinkPublicConstraintResponse.stage hpositive⟩
  | inr transition =>
      filter_upwards [transition.eventual] with t htransition
      intro ht
      exact
        ⟨FinkPublicConstraintResponse.transition
          (transition.toFinkPublicTransitionChargeAt
            ht htransition.2.2)⟩

end AnalyticForwardFinkPublicResponse

omit [DecidableEq G.State] in
/-- The action-repaired analytic obstruction yields one fixed actual forward
response with an unoriented positive Bellman charge.

This is stronger operational information than selecting a signed obstruction
coordinate: positivity of the repaired supported weights prevents the
selected Bellman charge from being sign-reversed. -/
theorem exists_analyticForwardFinkPublicResponse
    [Nonempty G.State] [Nonempty ι] [∀ i, Nonempty (G.Act i)]
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    Nonempty (AnalyticForwardFinkPublicResponse germ H K) := by
  classical
  let E := Σ who : ι, G.State × G.Act who
  letI : Nonempty E := by
    let owner : ι := Classical.choice (inferInstance : Nonempty ι)
    let source : G.State :=
      Classical.choice (inferInstance : Nonempty G.State)
    let action : G.Act owner :=
      Classical.choice (inferInstance : Nonempty (G.Act owner))
    exact ⟨⟨owner, source, action⟩⟩
  obtain ⟨supported, poleOrder, repaired, hrepaired, hrepairedFlow⟩ :=
    germ.exists_analytic_actionRepaired_eventual_finkObstructionFlow
      H K hflow
  let term : E → ℝ → ℝ := fun response t =>
    germ.rawFinkObstructionMass supported H K t
        (Sum.inr response) *
      repaired t (Sum.inr response)
  have hterm : ∀ response, AnalyticAt ℝ (term response) 0 := by
    intro response
    exact
      (germ.analytic_rawFinkObstructionMass
        supported H K (Sum.inr response)).mul
          (analyticAt_pi_iff.mp hrepaired (Sum.inr response))
  obtain ⟨response, havg⟩ :=
    exists_fixed_analytic_average_charge term hterm
  have hcard : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast Fintype.card_pos
  have htermPositive :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        0 < term response t := by
    filter_upwards [hrepairedFlow, havg] with t ht havg_t
    have hsum :
        (∑ edge : E, term edge t) =
          germ.rawFinkSupportProduct supported t *
            t ^ poleOrder := by
      have htarget := ht.2.2.2.1
      rw [Fintype.sum_sum_type] at htarget
      simpa only [AnalyticBellmanGerm.rawFinkObstructionMass, zero_mul,
        Finset.sum_const_zero, zero_add, term] using htarget
    have havgPositive :
        0 <
          (Fintype.card E : ℝ)⁻¹ *
            ∑ edge : E, term edge t := by
      rw [hsum]
      exact mul_pos (inv_pos.mpr hcard) ht.2.2.2.2.2
    exact havgPositive.trans_le havg_t
  have hsupported : supported response = true := by
    obtain ⟨t, hpositive⟩ := htermPositive.exists
    by_contra hnot
    have hfalse : supported response = false :=
      Bool.eq_false_of_not_eq_true hnot
    have hmass :
        germ.rawFinkObstructionMass supported H K t
            (Sum.inr response) = 0 := by
      simp [AnalyticBellmanGerm.rawFinkObstructionMass, hfalse]
    simp only [term, hmass, zero_mul] at hpositive
    exact (lt_irrefl 0) hpositive
  have hmassPositive :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        0 <
          germ.rawFinkObstructionMass supported H K t
            (Sum.inr response) := by
    filter_upwards [hrepairedFlow, htermPositive] with
        t ht hterm_t
    have hweight :
        0 < repaired t (Sum.inr response) :=
      ht.2.2.2.2.1 response hsupported
    rcases mul_pos_iff.mp hterm_t with hpositive | hnegative
    · exact hpositive.1
    · exact False.elim ((not_lt_of_ge hweight.le) hnegative.2)
  obtain ⟨chargeOrder, chargeMargin, hchargeMargin, hchargePower⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      (germ.analytic_rawFinkObstructionMass
        supported H K (Sum.inr response))
      hmassPositive
  have heventualCharge :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          supported response = true ∧
          chargeMargin * t ^ chargeOrder ≤
            germ.rawFinkObstructionMass supported H K t
              (Sum.inr response) ∧
          0 <
            germ.rawFinkObstructionMass supported H K t
              (Sum.inr response) := by
    filter_upwards [hrepairedFlow,
      hchargePower, hmassPositive] with t ht hp hpos
    simpa only [sub_zero] using
      And.intro ht.1 (And.intro hsupported (And.intro hp hpos))
  let stage : ℝ → ℝ := fun t =>
    germ.rawPureDeviationStageGainCurve
      t response.2.1 response.1 response.2.2
  let continuation : ℝ → ℝ := fun t =>
    germ.rawPureDeviationContinuationGainCurve
      (H - K) t response.2.1 response.1 response.2.2
  have hstage : AnalyticAt ℝ stage 0 := by
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve
            response.2.1) response.1) response.2.2)
  have hcontinuation : AnalyticAt ℝ continuation 0 := by
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (germ.analytic_rawPureDeviationContinuationGainCurve
              (H - K)) response.2.1) response.1)
        response.2.2)
  have htotal :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        chargeMargin * t ^ chargeOrder ≤
          stage t + continuation t := by
    filter_upwards [heventualCharge] with t ht
    simpa only [stage, continuation,
      AnalyticBellmanGerm.rawFinkObstructionMass,
      ht.2.1, if_true] using ht.2.2.1
  rcases analytic_sum_powerCharge_left_or_right
      hstage hcontinuation htotal with hstagePower | hcontinuationPower
  · have hstageEventual :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (chargeMargin / 2) * t ^ chargeOrder ≤ stage t ∧
            0 < stage t := by
      filter_upwards [hrepairedFlow, hstagePower,
        self_mem_nhdsWithin] with t ht hp htpos
      have hlower :
          0 < (chargeMargin / 2) * t ^ chargeOrder :=
        mul_pos (div_pos hchargeMargin (by norm_num))
          (pow_pos htpos chargeOrder)
      exact ⟨ht.1, hp, hlower.trans_le hp⟩
    exact ⟨{
      supported := supported
      response := response
      chargeOrder := chargeOrder
      chargeMargin := chargeMargin
      chargeMargin_pos := hchargeMargin
      eventual_charge := heventualCharge
      branch := Sum.inl {
        order := chargeOrder
        margin := chargeMargin / 2
        margin_pos := div_pos hchargeMargin (by norm_num)
        eventual := by
          simpa only [stage] using hstageEventual } }⟩
  · have hcontinuationPositive :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          0 < continuation t := by
      filter_upwards [hcontinuationPower,
        self_mem_nhdsWithin] with t hp htpos
      have hlower :
          0 < (chargeMargin / 2) * t ^ chargeOrder :=
        mul_pos (div_pos hchargeMargin (by norm_num))
          (pow_pos htpos chargeOrder)
      exact hlower.trans_le hp
    let difference : G.State → ℝ → ℝ := fun destination t =>
      germ.rawPureDeviationStateKernelCurve
          t response.2.1 response.1 response.2.2 destination -
        germ.rawStateKernelCurve t response.2.1 destination
    have hdifference :
        ∀ destination, AnalyticAt ℝ (difference destination) 0 := by
      intro destination
      exact
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStateKernelCurve
                response.2.1) response.1) response.2.2)
          destination).sub
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve response.2.1)
          destination)
    have hsum :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∑ destination, difference destination t = 0 := by
      filter_upwards [hrepairedFlow] with t ht
      have hpure :=
        pmf_toReal_sum_one
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht.1)
            response.2.1 response.1 response.2.2)
      have hbase :=
        pmf_toReal_sum_one
          (G.finkStateKernel
            (germ.finkPointAt ht.1) response.2.1)
      simp_rw [difference, Finset.sum_sub_distrib]
      rw [show
          (∑ destination,
            germ.rawPureDeviationStateKernelCurve
              t response.2.1 response.1 response.2.2 destination) = 1 by
            simpa only [
              germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
                ht.1 response.2.1 response.1 response.2.2] using hpure]
      rw [show
          (∑ destination,
            germ.rawStateKernelCurve
              t response.2.1 destination) = 1 by
            simpa only [
              germ.rawStateKernelCurve_eq_finkStateKernel
                ht.1 response.2.1] using hbase]
      exact sub_self 1
    have hnonzero :
        ¬∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∀ destination, difference destination t = 0 := by
      intro hzero
      obtain ⟨t, hpositive, hzero_t⟩ :=
        (hcontinuationPositive.and hzero).exists
      have hvanish : continuation t = 0 := by
        simp only [continuation,
          AnalyticBellmanGerm.rawPureDeviationContinuationGainCurve]
        apply Finset.sum_eq_zero
        intro destination _
        change difference destination t *
          ((H - K) destination response.1) = 0
        rw [hzero_t destination, zero_mul]
      rw [hvanish] at hpositive
      exact (lt_irrefl 0) hpositive
    obtain ⟨destination, monitorOrder, monitorMargin,
        hmonitorMargin, hmonitorPower⟩ :=
      exists_coordinate_powerCharge_of_analytic_zeroSum
        difference hdifference hsum hnonzero
    let monitor : PMFCoordinateMonitor G.State := (destination, true)
    have hmonitorEventual :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            monitorMargin * t ^ monitorOrder ≤
              analyticFinkMonitorDrift germ response monitor t ∧
            0 <
              analyticFinkMonitorDrift germ response monitor t := by
      filter_upwards [hrepairedFlow, hmonitorPower] with t ht hp
      simpa only [analyticFinkMonitorDrift, monitor,
        responseOrientation_true, one_mul, difference] using
          And.intro ht.1 hp
    exact ⟨{
      supported := supported
      response := response
      chargeOrder := chargeOrder
      chargeMargin := chargeMargin
      chargeMargin_pos := hchargeMargin
      eventual_charge := heventualCharge
      branch := Sum.inr {
        monitor := monitor
        order := monitorOrder
        margin := monitorMargin
        margin_pos := hmonitorMargin
        eventual := hmonitorEventual } }⟩

end StochasticGame
end GameTheory
