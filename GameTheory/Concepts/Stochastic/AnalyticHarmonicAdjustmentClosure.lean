/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticHarmonicAdjustmentSelection
import GameTheory.Concepts.Stochastic.FinkLimit

/-!
# Strategic content of a coherent analytic harmonic adjustment

A coherent moving adjustment has a precise endpoint consequence: its
endpoint value is harmonic for the limiting on-profile kernel, and its
pure-deviation continuation gain equals the stage gain on every analytically
visible action. This includes rare actions whose endpoint probability is
zero but whose mixing-coordinate germ is not identically zero.

This removes the stage term from the visible-action bias inequalities. It
does not produce the independent Poisson correction, nor does it control
the action-specific discount-scale drift of analytically invisible actions.
The final theorem below states the resulting stationary closure with exactly
those residual hypotheses exposed.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Set Topology

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

omit [DecidableEq G.State] in
/-- Endpoint version of the raw pure-deviation joint-mass identity. -/
theorem rawPureDeviationProfileWeight_zero_eq_endpointProfile
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who)
    (a : G.JointAct) :
    germ.rawPureDeviationProfileWeight 0 s who d a =
      (Math.PMFProduct.pmfPi
        (Function.update
          (germ.endpointProfile s) who (PMF.pure d))
        a).toReal := by
  rw [Math.PMFProduct.pmfPi_apply_update_family,
    ENNReal.toReal_mul, ENNReal.toReal_prod, PMF.pure_apply]
  unfold rawPureDeviationProfileWeight endpointProfile
  by_cases had : a who = d
  · rw [if_pos had, if_pos had]
    simp only [ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro other _
    simpa [endpoint] using
      (G.bellmanDecodeProfile_apply_toReal
        germ.endpoint_isPolynomialBellmanSolution
        s other (a other)).symm
  · rw [if_neg had, if_neg had]
    simp

omit [DecidableEq G.State] in
/-- The raw pure-deviation kernel at zero is the semantic endpoint kernel. -/
theorem rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who)
    (destination : G.State) :
    germ.rawPureDeviationStateKernelCurve
        0 s who d destination =
      (G.finkPureDeviationStateKernel
        germ.endpointFinkPoint s who d destination).toReal := by
  unfold rawPureDeviationStateKernelCurve
    finkPureDeviationStateKernel
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawPureDeviationProfileWeight_zero_eq_endpointProfile]
  rw [germ.finkProfile_endpointFinkPoint]

omit [DecidableEq G.State] in
/-- The raw stage-gain curve at zero is the endpoint Fink stage gain. -/
theorem rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawPureDeviationStageGainCurve 0 s who d =
      G.finkStageGain germ.endpointFinkPoint s who d := by
  unfold rawPureDeviationStageGainCurve finkStageGain mixedStageEU
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [germ.rawPureDeviationProfileWeight_zero_eq_endpointProfile]
    rw [germ.finkProfile_endpointFinkPoint]
  · apply Finset.sum_congr rfl
    intro a _
    rw [germ.rawProfileWeight_zero_eq_pmfPi_endpointProfile,
      germ.finkProfile_endpointFinkPoint]

omit [DecidableEq G.State] in
/-- The raw continuation-gain curve at zero is the endpoint semantic gain. -/
theorem
    rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawPureDeviationContinuationGainCurve W 0 s who d =
      G.finkContinuationGain W
        germ.endpointFinkPoint s who d := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  unfold rawPureDeviationContinuationGainCurve
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro destination _
  rw [
    germ.rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint,
    germ.rawStateKernelCurve_zero_eq_finkStateKernel]
  ring

/-- Pure-deviation continuation gain when the continued payoff itself moves
analytically with the Bellman parameter. -/
def rawMovingPureDeviationContinuationGainCurve
    (germ : G.AnalyticBellmanGerm)
    (adjustment : ℝ → G.State → Payoff ι) :
    ℝ → G.State → ∀ who : ι, G.Act who → ℝ :=
  fun t s who d =>
    ∑ destination,
      (germ.rawPureDeviationStateKernelCurve
          t s who d destination -
        germ.rawStateKernelCurve t s destination) *
          adjustment t destination who

omit [DecidableEq G.State] in
/-- The moving pure-deviation gain is analytic through the endpoint. -/
theorem analytic_rawMovingPureDeviationContinuationGainCurve
    (germ : G.AnalyticBellmanGerm)
    (adjustment : ℝ → G.State → Payoff ι)
    (hadjustment : AnalyticAt ℝ adjustment 0) :
    AnalyticAt ℝ
      (germ.rawMovingPureDeviationContinuationGainCurve
        adjustment) 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  rw [analyticAt_pi_iff]
  intro d
  apply Finset.univ.analyticAt_fun_sum
  intro destination _
  have hkernel :
      AnalyticAt ℝ
        (fun t =>
          germ.rawPureDeviationStateKernelCurve
              t s who d destination -
            germ.rawStateKernelCurve t s destination) 0 :=
    ((analyticAt_pi_iff.mp
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStateKernelCurve) s))
              who)) d)) destination).sub
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelCurve) s)) destination)
  exact hkernel.mul
    ((analyticAt_pi_iff.mp
      ((analyticAt_pi_iff.mp hadjustment) destination)) who)

omit [DecidableEq G.State] in
/-- At a positive germ point the moving raw gain is the semantic gain of the
current adjustment. -/
theorem rawMovingPureDeviationContinuationGainCurve_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (adjustment : ℝ → G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawMovingPureDeviationContinuationGainCurve
        adjustment t s who d =
      G.finkContinuationGain (adjustment t)
        (germ.finkPointAt ht) s who d := by
  change
    germ.rawPureDeviationContinuationGainCurve
        (adjustment t) t s who d =
      G.finkContinuationGain (adjustment t)
        (germ.finkPointAt ht) s who d
  exact
    germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt
      (adjustment t) ht s who d

omit [DecidableEq G.State] in
/-- At zero the moving raw gain is the semantic endpoint gain. -/
theorem
    rawMovingPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm)
    (adjustment : ℝ → G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawMovingPureDeviationContinuationGainCurve
        adjustment 0 s who d =
      G.finkContinuationGain (adjustment 0)
        germ.endpointFinkPoint s who d := by
  change
    germ.rawPureDeviationContinuationGainCurve
        (adjustment 0) 0 s who d =
      G.finkContinuationGain (adjustment 0)
        germ.endpointFinkPoint s who d
  exact
    germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
      (adjustment 0) s who d

/-- An analytic right germ which is eventually zero also vanishes at its
endpoint. -/
theorem analyticAt_eq_zero_of_eventuallyEq_zero_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [T2Space E] (f : ℝ → E)
    (hf : AnalyticAt ℝ f 0)
    (heventual : ∀ᶠ t in nhdsWithin 0 (Ioi 0), f t = 0) :
    f 0 = 0 := by
  have hleft :
      Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0)) :=
    hf.continuousAt.tendsto.mono_left inf_le_left
  have hright :
      Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_const_nhds.congr'
      (heventual.mono fun _ ht => ht.symm)
  exact tendsto_nhds_unique hleft hright

/-- An action is analytically visible when its Bellman mixing-coordinate
germ is not identically zero on the positive side. This includes rare
actions whose endpoint probability is zero but whose positive-parameter
probability is nonzero. -/
def IsAnalyticallyVisibleAction
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who) : Prop :=
  ¬∀ᶠ t in nhdsWithin 0 (Ioi 0),
    germ.assignment t (BellmanVar.mix s who d) = 0

/-- Static endpoint datum extracted from a coherent moving adjustment. -/
structure EndpointStageHarmonicAdjustment
    (germ : G.AnalyticBellmanGerm) where
  adjustment : G.State → Payoff ι
  harmonic :
    G.finkContinuationResidualVector
      adjustment germ.endpointFinkPoint = 0
  supported_stage_eq : ∀ s who (d : G.Act who),
    G.finkProfile germ.endpointFinkPoint s who d ≠ 0 →
      G.finkContinuationGain adjustment
          germ.endpointFinkPoint s who d =
        G.finkStageGain germ.endpointFinkPoint s who d
  visible_stage_eq : ∀ s who (d : G.Act who),
    germ.IsAnalyticallyVisibleAction s who d →
      G.finkContinuationGain adjustment
          germ.endpointFinkPoint s who d =
        G.finkStageGain germ.endpointFinkPoint s who d

namespace CoherentAnalyticStageHarmonicAdjustment

omit [DecidableEq G.State] in
/-- An analytically visible action is supported throughout a sufficiently
small positive tail. The impossible negative-sign branch is excluded by
the simplex nonnegativity of every valid Bellman solution. -/
theorem eventually_analyticallyVisibleAction_ne_zero
    {germ : G.AnalyticBellmanGerm}
    (response : germ.CoherentAnalyticStageHarmonicAdjustment)
    (s : G.State) (who : ι) (d : G.Act who)
    (hvisible : germ.IsAnalyticallyVisibleAction s who d) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        G.finkProfile
          (germ.finkPointAt ht) s who d ≠ 0 := by
  let coordinate : ℝ → ℝ := fun t =>
    germ.assignment t (BellmanVar.mix s who d)
  rcases
      Math.analyticAt_eventually_eq_or_lt_or_gt
        (germ.analytic_coordinate (BellmanVar.mix s who d))
        (analyticAt_const :
          AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0) with
    hzero | hnegative | hpositive
  · exact False.elim (hvisible hzero)
  · exfalso
    have hnonnegative :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 ≤ coordinate t := by
      filter_upwards [response.realizes_stage] with t ht
      have hreal :
          coordinate t =
            (G.bellmanDecodeProfile
              (germ.solution t ht.1) s who d).toReal :=
        (G.bellmanDecodeProfile_apply_toReal
          (germ.solution t ht.1) s who d).symm
      rw [hreal]
      exact ENNReal.toReal_nonneg
    obtain ⟨t, htnegative, htnonnegative⟩ :=
      (hnegative.and hnonnegative).exists
    exact (not_lt_of_ge htnonnegative htnegative)
  · filter_upwards [hpositive] with t htpositive
    intro ht
    have hreal :
        coordinate t =
          (G.bellmanDecodeProfile
            (germ.solution t ht) s who d).toReal :=
      (G.bellmanDecodeProfile_apply_toReal
        (germ.solution t ht) s who d).symm
    rw [germ.finkProfile_finkPointAt]
    intro hzero
    have hcoordinateZero : coordinate t = 0 := by
      rw [hreal, hzero]
      simp
    linarith

omit [DecidableEq G.State] in
/-- Every endpoint-supported action remains supported along a sufficiently
small positive tail of the analytic Bellman germ. -/
theorem eventually_endpointSupportedAction_ne_zero
    {germ : G.AnalyticBellmanGerm}
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos :
      G.finkProfile germ.endpointFinkPoint s who d ≠ 0) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        G.finkProfile
          (germ.finkPointAt ht) s who d ≠ 0 := by
  let coordinate : ℝ → ℝ := fun t =>
    germ.assignment t (BellmanVar.mix s who d)
  have hcoordinateZero : coordinate 0 ≠ 0 := by
    have hreal :=
      G.bellmanDecodeProfile_apply_toReal
        germ.endpoint_isPolynomialBellmanSolution s who d
    have htoReal :
        (germ.endpointProfile s who d).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr
        ⟨by
          simpa [germ.finkProfile_endpointFinkPoint] using hpos,
          PMF.apply_ne_top _ _⟩
    intro hzero
    apply htoReal
    have hreal' :
        (germ.endpointProfile s who d).toReal =
          coordinate 0 := by
      simpa only [endpointProfile, coordinate, endpoint] using
        hreal
    rw [hreal', hzero]
  have hcoordinate_ne :
      ∀ᶠ t in nhds 0, coordinate t ≠ 0 :=
    (germ.analytic_coordinate
      (BellmanVar.mix s who d)).continuousAt.eventually_ne
        hcoordinateZero
  filter_upwards
      [hcoordinate_ne.filter_mono inf_le_left] with t htne
  intro ht
  have hreal :
      coordinate t =
        (G.bellmanDecodeProfile
          (germ.solution t ht) s who d).toReal :=
    (G.bellmanDecodeProfile_apply_toReal
      (germ.solution t ht) s who d).symm
  rw [germ.finkProfile_finkPointAt]
  intro hzero
  apply htne
  rw [hreal, hzero]
  simp

omit [DecidableEq G.State] in
/-- Eventual support of one action is enough to extend its coherent
stage/continuation equality through the analytic endpoint. -/
theorem endpoint_stage_eq_of_eventually_action_ne_zero
    {germ : G.AnalyticBellmanGerm}
    (response : germ.CoherentAnalyticStageHarmonicAdjustment)
    (s : G.State) (who : ι) (d : G.Act who)
    (hsupported :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          G.finkProfile
            (germ.finkPointAt ht) s who d ≠ 0) :
    G.finkContinuationGain (response.adjustment 0)
          germ.endpointFinkPoint s who d =
      G.finkStageGain germ.endpointFinkPoint s who d := by
  let difference : ℝ → ℝ := fun t =>
    germ.rawMovingPureDeviationContinuationGainCurve
        response.adjustment t s who d -
      germ.rawPureDeviationStageGainCurve t s who d
  have hdifferenceAnalytic :
      AnalyticAt ℝ difference 0 :=
    (((analyticAt_pi_iff.mp
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          (germ.analytic_rawMovingPureDeviationContinuationGainCurve
            response.adjustment
            response.analytic_adjustment)) s)) who)) d).sub
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve) s))
              who)) d))
  have hdifferenceZero :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), difference t = 0 := by
    filter_upwards [response.realizes_stage,
      hsupported] with t ht hsupportAt
    have hgain :=
      (ht.2 ht.1).2 s who d (hsupportAt ht.1)
    change
      germ.rawMovingPureDeviationContinuationGainCurve
            response.adjustment t s who d -
          germ.rawPureDeviationStageGainCurve t s who d =
        0
    rw [
      germ.rawMovingPureDeviationContinuationGainCurve_eq_finkPointAt
        response.adjustment ht.1,
      germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht.1,
      hgain, sub_self]
  have hzero :=
    analyticAt_eq_zero_of_eventuallyEq_zero_right
      difference hdifferenceAnalytic hdifferenceZero
  change
    germ.rawMovingPureDeviationContinuationGainCurve
          response.adjustment 0 s who d -
        germ.rawPureDeviationStageGainCurve 0 s who d =
      0 at hzero
  rw [
    germ.rawMovingPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint,
    germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint]
    at hzero
  exact sub_eq_zero.mp hzero

/-- A coherent analytic adjustment has an endpoint-harmonic limit and
represents every endpoint-supported stage gain. -/
def endpoint
    {germ : G.AnalyticBellmanGerm}
    (response : germ.CoherentAnalyticStageHarmonicAdjustment) :
    germ.EndpointStageHarmonicAdjustment where
  adjustment := response.adjustment 0
  harmonic := by
    let residual : ℝ → G.State → Payoff ι := fun t =>
      germ.rawContinuationCurve response.adjustment t -
        response.adjustment t
    have hresidualAnalytic : AnalyticAt ℝ residual 0 :=
      (germ.analytic_rawContinuationCurve
        response.analytic_adjustment).sub
          response.analytic_adjustment
    have hresidualZero :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), residual t = 0 := by
      filter_upwards [response.realizes_stage] with t ht
      funext s who
      have hsemantic :=
        congrFun
          (congrFun ((ht.2 ht.1).1) s) who
      have hcontinuation :=
        congrFun
          (congrFun
            (germ.rawContinuationCurve_eq_finkContinuationEU
              response.adjustment ht.1) s) who
      simp only [residual, Pi.sub_apply]
      rw [hcontinuation]
      simpa [finkContinuationResidualVector,
        finkContinuationResidual] using hsemantic
    have hzero :=
      analyticAt_eq_zero_of_eventuallyEq_zero_right
        residual hresidualAnalytic hresidualZero
    funext s who
    have hcoordinate := congrFun (congrFun hzero s) who
    have hcontinuation :=
      congrFun
        (congrFun
          (germ.rawContinuationCurve_zero_eq_finkContinuationEU
            response.adjustment) s) who
    change
      germ.rawContinuationCurve response.adjustment 0 s who -
          response.adjustment 0 s who =
        0 at hcoordinate
    rw [hcontinuation] at hcoordinate
    simpa [residual, finkContinuationResidualVector,
      finkContinuationResidual] using hcoordinate
  supported_stage_eq := by
    intro s who d hpos
    exact
      response.endpoint_stage_eq_of_eventually_action_ne_zero
        s who d
        (eventually_endpointSupportedAction_ne_zero
          (germ := germ) s who d hpos)
  visible_stage_eq := by
    intro s who d hvisible
    exact
      response.endpoint_stage_eq_of_eventually_action_ne_zero
        s who d
        (response.eventually_analyticallyVisibleAction_ne_zero
          s who d hvisible)

end CoherentAnalyticStageHarmonicAdjustment

namespace EndpointStageHarmonicAdjustment

omit [DecidableEq G.State] in
/-- Adding the coherent endpoint adjustment to a harmonic correction removes
the stage term from every endpoint-supported bias inequality. -/
theorem supported_bias_eq_remainingContinuationGain
    {germ : G.AnalyticBellmanGerm}
    (response : germ.EndpointStageHarmonicAdjustment)
    (H K A : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos :
      G.finkProfile germ.endpointFinkPoint s who d ≠ 0) :
    G.finkStageGain germ.endpointFinkPoint s who d +
          G.finkContinuationGain
            (H - (K + (A + response.adjustment)))
            germ.endpointFinkPoint s who d =
      G.finkContinuationGain (H - (K + A))
        germ.endpointFinkPoint s who d := by
  have hstage := response.supported_stage_eq s who d hpos
  rw [← hstage]
  simp only [G.finkContinuationGain_sub,
    G.finkContinuationGain_add]
  ring

omit [DecidableEq G.State] in
/-- Adding the coherent endpoint adjustment removes the stage term from
every analytically visible action, including rare actions with zero endpoint
probability. -/
theorem visible_bias_eq_remainingContinuationGain
    {germ : G.AnalyticBellmanGerm}
    (response : germ.EndpointStageHarmonicAdjustment)
    (H K A : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hvisible : germ.IsAnalyticallyVisibleAction s who d) :
    G.finkStageGain germ.endpointFinkPoint s who d +
          G.finkContinuationGain
            (H - (K + (A + response.adjustment)))
            germ.endpointFinkPoint s who d =
      G.finkContinuationGain (H - (K + A))
        germ.endpointFinkPoint s who d := by
  have hstage := response.visible_stage_eq s who d hvisible
  rw [← hstage]
  simp only [G.finkContinuationGain_sub,
    G.finkContinuationGain_add]
  ring

end EndpointStageHarmonicAdjustment

omit [DecidableEq G.State] in
/-- Exact stationary closure of the coherent-adjustment branch.

The coherent endpoint adjustment removes the stage term on every analytically
visible action, including rare actions whose endpoint probability is zero.
Two logically separate requirements remain:

* a Poisson correction for the on-profile Bellman forcing;
* bias inequalities for continuation-neutral actions whose mixing-coordinate
  germ is identically zero.

An additional endpoint-harmonic adjustment `C` may be used to satisfy the
remaining visible continuation inequalities. -/
theorem
    isUniformEquilibriumPayoff_of_finiteBias_coherentStageAdjustment
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (response : germ.CoherentAnalyticStageHarmonicAdjustment)
    (K C : G.State → Payoff ι)
    (s₀ : G.State)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint)
    (hCharmonic :
      G.finkContinuationResidualVector
        C germ.endpointFinkPoint = 0)
    (hremainingVisible :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) =
            germ.endpointValue s who →
          germ.IsAnalyticallyVisibleAction s who d →
          G.finkContinuationGain
              (seed.H - (K + C))
              germ.endpointFinkPoint s who d ≤ 0)
    (hinvisibleNeutral :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) =
            germ.endpointValue s who →
          ¬ germ.IsAnalyticallyVisibleAction s who d →
            G.finkStageGain germ.endpointFinkPoint s who d +
                G.finkContinuationGain
                  (seed.H -
                    (K + (C + response.endpoint.adjustment)))
                  germ.endpointFinkPoint s who d ≤ 0) :
    G.IsUniformEquilibriumPayoff
      s₀ (germ.endpointValue s₀) := by
  let endpointAdjustment := response.endpoint
  let D : G.State → Payoff ι :=
    C + endpointAdjustment.adjustment
  let bias : G.State → Payoff ι :=
    seed.H - (K + D)
  have hDharmonic :
      G.finkContinuationResidualVector
        D germ.endpointFinkPoint = 0 := by
    dsimp only [D]
    rw [G.finkContinuationResidualVector_add,
      hCharmonic, endpointAdjustment.harmonic, add_zero]
  have hharmonic :
      ∀ s who,
        germ.endpointValue s who =
          Math.Probability.expect
            (Math.PMFProduct.pmfPi (germ.endpointProfile s))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) := by
    intro s who
    have hzero :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero
          s) who
    have hcontinuation :
        G.finkContinuationEU germ.endpointValue
            germ.endpointFinkPoint s who =
          germ.endpointValue s who :=
      sub_eq_zero.mp
        (by
          simpa [finkContinuationResidualVector,
            finkContinuationResidual] using hzero)
    simpa [finkContinuationEU,
      germ.finkProfile_endpointFinkPoint] using
        hcontinuation.symm
  have hexcessive :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) ≤
          germ.endpointValue s who := by
    intro s who d
    have hgain :=
      germ.finkContinuationGain_endpointValue_nonpos
        s who d
    unfold finkContinuationGain at hgain
    rw [germ.finkProfile_endpointFinkPoint] at hgain
    linarith [hharmonic s who]
  have honProfileBase :
      ∀ s who,
        germ.endpointValue s who +
            (seed.H - K) s who =
          G.mixedStageEU s (germ.endpointProfile s) who +
            Math.Probability.expect
              (Math.PMFProduct.pmfPi
                (germ.endpointProfile s))
              (fun a =>
                Math.Probability.expect (G.transition s a)
                  (fun s' => (seed.H - K) s' who)) := by
    intro s who
    have hcoordinate :=
      congrFun (congrFun hPoisson s) who
    unfold finkBellmanForcingVector
      finkContinuationResidualVector
      finkContinuationResidual at hcoordinate
    change
      germ.endpointValue s who + seed.H s who -
            G.finkStageEU germ.endpointFinkPoint s who -
            G.finkContinuationEU seed.H
              germ.endpointFinkPoint s who =
        -(G.finkContinuationEU K
            germ.endpointFinkPoint s who - K s who)
      at hcoordinate
    rw [← germ.finkProfile_endpointFinkPoint]
    change
      germ.endpointValue s who + (seed.H - K) s who =
        G.finkStageEU germ.endpointFinkPoint s who +
          G.finkContinuationEU
            (seed.H - K) germ.endpointFinkPoint s who
    rw [G.finkContinuationEU_sub]
    simp only [Pi.sub_apply] at hcoordinate ⊢
    linarith
  have honProfile :
      ∀ s who,
        germ.endpointValue s who + bias s who =
          G.mixedStageEU s (germ.endpointProfile s) who +
            Math.Probability.expect
              (Math.PMFProduct.pmfPi
                (germ.endpointProfile s))
              (fun a =>
                Math.Probability.expect (G.transition s a)
                  (fun s' => bias s' who)) := by
    intro s who
    have hDcoordinate :=
      congrFun (congrFun hDharmonic s) who
    have hDonProfile :
        G.finkContinuationEU D
            germ.endpointFinkPoint s who = D s who :=
      sub_eq_zero.mp
        (by
          simpa [finkContinuationResidualVector,
            finkContinuationResidual] using hDcoordinate)
    change
      germ.endpointValue s who +
            (seed.H - (K + D)) s who =
        G.mixedStageEU s (germ.endpointProfile s) who +
          Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (germ.endpointProfile s))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => (seed.H - (K + D)) s' who))
    rw [← germ.finkProfile_endpointFinkPoint]
    change
      germ.endpointValue s who +
            (seed.H - (K + D)) s who =
        G.finkStageEU germ.endpointFinkPoint s who +
          G.finkContinuationEU
            (seed.H - (K + D))
              germ.endpointFinkPoint s who
    rw [G.finkContinuationEU_sub,
      G.finkContinuationEU_add, hDonProfile]
    have hbase := honProfileBase s who
    rw [← germ.finkProfile_endpointFinkPoint] at hbase
    change
      germ.endpointValue s who + (seed.H - K) s who =
        G.finkStageEU germ.endpointFinkPoint s who +
          G.finkContinuationEU
            (seed.H - K) germ.endpointFinkPoint s who
      at hbase
    rw [G.finkContinuationEU_sub] at hbase
    simp only [Pi.sub_apply, Pi.add_apply] at hbase ⊢
    linarith
  apply
    G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral
      s₀ germ.endpointProfile germ.endpointValue bias
      hharmonic hexcessive honProfile
  intro s who d hneutral
  have hbaseline :
      G.mixedStageEU s (germ.endpointProfile s) who +
          Math.Probability.expect
            (Math.PMFProduct.pmfPi (germ.endpointProfile s))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => bias s' who)) =
        germ.endpointValue s who + bias s who :=
    (honProfile s who).symm
  have himprovement :
      G.mixedStageEU s
            (Function.update
              (germ.endpointProfile s) who (PMF.pure d)) who +
          Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => bias s' who)) -
          (germ.endpointValue s who + bias s who) =
        G.finkStageGain germ.endpointFinkPoint s who d +
          G.finkContinuationGain bias
            germ.endpointFinkPoint s who d := by
    unfold finkStageGain finkContinuationGain
    rw [germ.finkProfile_endpointFinkPoint]
    linarith
  by_cases hvisible :
      germ.IsAnalyticallyVisibleAction s who d
  · have hreduce :=
      endpointAdjustment.visible_bias_eq_remainingContinuationGain
        seed.H K C s who d hvisible
    have hnonpos :=
      hremainingVisible s who d hneutral hvisible
    change
      G.mixedStageEU s
            (Function.update
              (germ.endpointProfile s) who (PMF.pure d)) who +
          Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => bias s' who)) ≤
        germ.endpointValue s who + bias s who
    have hnonposBias :
        G.finkStageGain germ.endpointFinkPoint s who d +
            G.finkContinuationGain bias
              germ.endpointFinkPoint s who d ≤ 0 := by
      dsimp only [bias, D]
      rw [hreduce]
      exact hnonpos
    linarith
  · have hnonpos :=
      hinvisibleNeutral s who d hneutral hvisible
    change
      G.mixedStageEU s
            (Function.update
              (germ.endpointProfile s) who (PMF.pure d)) who +
          Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => bias s' who)) ≤
        germ.endpointValue s who + bias s who
    dsimp only [bias, D, endpointAdjustment]
    linarith

omit [DecidableEq G.State] in
/-- Zero-extra-harmonic specialization. It exposes the two exact missing
conditions most directly: `H - K` must have nonpositive continuation gain
on analytically visible continuation-neutral actions, and every neutral
analytically invisible action must satisfy its full static bias inequality. -/
theorem
    isUniformEquilibriumPayoff_of_finiteBias_coherentStageAdjustment_zero
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (response : germ.CoherentAnalyticStageHarmonicAdjustment)
    (K : G.State → Payoff ι)
    (s₀ : G.State)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint)
    (hremainingVisible :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) =
            germ.endpointValue s who →
          germ.IsAnalyticallyVisibleAction s who d →
          G.finkContinuationGain
              (seed.H - K)
              germ.endpointFinkPoint s who d ≤ 0)
    (hinvisibleNeutral :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) =
            germ.endpointValue s who →
          ¬ germ.IsAnalyticallyVisibleAction s who d →
            G.finkStageGain germ.endpointFinkPoint s who d +
                G.finkContinuationGain
                  (seed.H -
                    (K + response.endpoint.adjustment))
                  germ.endpointFinkPoint s who d ≤ 0) :
    G.IsUniformEquilibriumPayoff
      s₀ (germ.endpointValue s₀) := by
  apply
    germ.isUniformEquilibriumPayoff_of_finiteBias_coherentStageAdjustment
      seed response K 0 s₀ hPoisson
  · funext s who
    simp [finkContinuationResidualVector,
      finkContinuationResidual, finkContinuationEU]
  · intro s who d hneutral hvisible
    simpa using hremainingVisible s who d hneutral hvisible
  · simpa using hinvisibleNeutral

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
