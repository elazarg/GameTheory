/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BellmanGermFinkBridge
import Math.AlgebraicSelection
import Mathlib.Analysis.Analytic.Order

/-!
# Canonical first hierarchy datum of an analytic Bellman germ

Let `q` be the ramification exponent of an analytic Bellman germ and let
`V(t)` be its decoded value curve.  The average-reward relative-bias scale is

`((1 - t ^ q) / t ^ q) • (V(t) - V(0))`.

There is a canonical analytic-order dichotomy.  If `V(t) - V(0)` vanishes to
order at least `q`, the relative bias has an analytic extension through zero
and therefore a fixed limit `H`.  Otherwise the analytic order is a unique
natural number `n < q`, and the corresponding nonzero leading vector is the
next lower hierarchy coefficient.

This file performs only that standard analytic extraction.  Proving that a
lower-order coefficient forces a harmonic/rank response, and recursively
assembling those responses along public histories, belongs to the global
game-theoretic invariant.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

omit [DecidableEq G.State] in
/-- The endpoint of an analytic Bellman germ remains in the closed
polynomial Bellman solution set. -/
theorem endpoint_isPolynomialBellmanSolution
    (germ : G.AnalyticBellmanGerm) :
    G.IsPolynomialBellmanSolution germ.endpoint := by
  let source := 𝓝[Set.Ioo (0 : ℝ) germ.radius] 0
  haveI : NeBot source :=
    left_nhdsWithin_Ioo_neBot germ.radius_pos
  have htend :
      Tendsto germ.assignment source (𝓝 germ.endpoint) := by
    exact germ.analytic_assignment.continuousAt.mono_left inf_le_left
  have hclosure :
      germ.endpoint ∈ closure G.polynomialBellmanSolutionSet := by
    apply mem_closure_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact germ.solution t ht
  change germ.endpoint ∈ G.polynomialBellmanSolutionSet
  rw [← G.isClosed_polynomialBellmanSolutionSet.closure_eq]
  exact hclosure

omit [DecidableEq G.State] in
/-- The endpoint discount-complement coordinate is zero. -/
theorem endpoint_discountCoordinate_eq_zero
    (germ : G.AnalyticBellmanGerm) :
    germ.endpoint BellmanVar.disc = 0 := by
  let source := 𝓝[Set.Ioo (0 : ℝ) germ.radius] 0
  haveI : NeBot source :=
    left_nhdsWithin_Ioo_neBot germ.radius_pos
  have hcoordinate :
      Tendsto (fun t => germ.assignment t BellmanVar.disc) source
        (𝓝 (germ.endpoint BellmanVar.disc)) := by
    exact
      (germ.analytic_coordinate BellmanVar.disc).continuousAt.mono_left
        inf_le_left
  have hpower :
      Tendsto (fun t : ℝ => t ^ germ.ramification) source (𝓝 0) := by
    have hramification_ne : germ.ramification ≠ 0 :=
      Nat.ne_of_gt germ.ramification_pos
    have hcontinuous :
        ContinuousAt (fun t : ℝ => t ^ germ.ramification) 0 :=
      continuousAt_id.pow germ.ramification
    simpa [source, nhdsWithin, hramification_ne] using
      (hcontinuous.mono_left inf_le_left)
  have heq :
      ∀ᶠ t in source,
        t ^ germ.ramification =
          germ.assignment t BellmanVar.disc := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (germ.discountCoordinate t ht).symm
  exact tendsto_nhds_unique hcoordinate (hpower.congr' heq)

/-- The stationary profile decoded at the endpoint. -/
def endpointProfile (germ : G.AnalyticBellmanGerm) :
    G.StationaryMixedProfile :=
  G.bellmanDecodeProfile germ.endpoint_isPolynomialBellmanSolution

/-- The decoded value curve carried by an analytic Bellman germ. -/
def valueCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t => G.bellmanDecodeValue (germ.assignment t)

/-- The endpoint value of the analytic Bellman germ. -/
def endpointValue (germ : G.AnalyticBellmanGerm) :
    G.State → Payoff ι :=
  germ.valueCurve 0

omit [DecidableEq G.State] in
/-- The endpoint profile and value solve the undiscounted stationary Bellman
system. -/
theorem isDiscountedStationaryBellmanEq_endpoint
    (germ : G.AnalyticBellmanGerm) :
    G.IsDiscountedStationaryBellmanEq
      1 germ.endpointProfile germ.endpointValue := by
  have h :=
    G.isDiscountedStationaryBellmanEq_bellmanDecode
      germ.endpoint_isPolynomialBellmanSolution
  rw [bellmanDecodeDiscount,
    germ.endpoint_discountCoordinate_eq_zero, sub_zero] at h
  simpa [endpointProfile, endpointValue, valueCurve, endpoint] using h

/-- The canonical Fink-domain point represented by the endpoint profile and
value. -/
def endpointFinkPoint (germ : G.AnalyticBellmanGerm) :
    G.finkDomain (germ.finkBoundAt 0) :=
  G.finkPointOfProfileValue
    germ.endpointProfile germ.endpointValue
    (fun s who => by
      simpa [endpointValue, valueCurve, endpoint] using
        germ.bellmanDecodeValue_abs_le_finkBoundAt 0 s who)

omit [DecidableEq G.State] in
@[simp]
theorem finkProfile_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm) :
    G.finkProfile germ.endpointFinkPoint = germ.endpointProfile :=
  G.finkProfile_finkPointOfProfileValue _ _ _

omit [DecidableEq G.State] in
@[simp]
theorem finkValue_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm) :
    G.finkValue germ.endpointFinkPoint = germ.endpointValue :=
  G.finkValue_finkPointOfProfileValue _ _ _

omit [DecidableEq G.State] in
/-- The endpoint value is harmonic under the endpoint stationary state
kernel. -/
theorem finkContinuationResidualVector_endpointValue_eq_zero
    (germ : G.AnalyticBellmanGerm) :
    G.finkContinuationResidualVector
      germ.endpointValue germ.endpointFinkPoint = 0 := by
  ext s who
  have hvalue :=
    germ.isDiscountedStationaryBellmanEq_endpoint.2 s who
  rw [G.discountedAuxEU_eq] at hvalue
  simp only [sub_self, zero_mul, one_mul, zero_add] at hvalue
  unfold finkContinuationResidualVector finkContinuationResidual
    finkContinuationEU
  rw [germ.finkProfile_endpointFinkPoint]
  exact sub_eq_zero.mpr hvalue

omit [DecidableEq G.State] in
/-- No pure unilateral deviation has positive endpoint continuation gain. -/
theorem finkContinuationGain_endpointValue_nonpos
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint s who d ≤ 0 := by
  have hdeviation :=
    germ.isDiscountedStationaryBellmanEq_endpoint.1
      s who (PMF.pure d)
  rw [G.discountedAuxEU_eq, G.discountedAuxEU_eq] at hdeviation
  simp only [sub_self, zero_mul, one_mul, zero_add] at hdeviation
  unfold finkContinuationGain
  rw [germ.finkProfile_endpointFinkPoint]
  exact sub_nonpos.mpr hdeviation

omit [DecidableEq G.State] in
/-- Every pure action in the endpoint support preserves that player's
endpoint continuation value against the other players' endpoint mixtures. -/
theorem isContinuationNeutralOnSupport_endpoint
    (germ : G.AnalyticBellmanGerm) :
    G.IsContinuationNeutralOnSupport
      germ.endpointProfile germ.endpointValue := by
  have hharmonic :
      ∀ s who,
        germ.endpointValue s who =
          G.finkContinuationEU germ.endpointValue
            germ.endpointFinkPoint s who := by
    intro s who
    have hzero :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero s) who
    have heq :
        G.finkContinuationEU germ.endpointValue
            germ.endpointFinkPoint s who =
          germ.endpointValue s who :=
      sub_eq_zero.mp
        (by
          simpa [finkContinuationResidualVector,
            finkContinuationResidual] using hzero)
    exact heq.symm
  have hexcessive :
      ∀ s who (d : G.Act who),
        Math.Probability.expect
            (Math.PMFProduct.pmfPi
              (Function.update (germ.endpointProfile s) who (PMF.pure d)))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) ≤
          germ.endpointValue s who := by
    intro s who d
    have hgain :=
      germ.finkContinuationGain_endpointValue_nonpos s who d
    have hbase :
        Math.Probability.expect
            (Math.PMFProduct.pmfPi (germ.endpointProfile s))
            (fun a =>
              Math.Probability.expect (G.transition s a)
                (fun s' => germ.endpointValue s' who)) =
          germ.endpointValue s who := by
      simpa [finkContinuationEU,
        germ.finkProfile_endpointFinkPoint] using (hharmonic s who).symm
    unfold finkContinuationGain at hgain
    rw [germ.finkProfile_endpointFinkPoint, hbase] at hgain
    exact sub_nonpos.mp hgain
  have hneutral :=
    G.isContinuationNeutralOnSupport_of_harmonic_excessive
      germ.endpointFinkPoint germ.endpointValue hharmonic
        (fun s who d => by
          simpa [germ.finkProfile_endpointFinkPoint] using
            hexcessive s who d)
  simpa [germ.finkProfile_endpointFinkPoint] using hneutral

/-- The value increment relative to the endpoint. -/
def valueIncrement (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t => germ.valueCurve t - germ.endpointValue

omit [DecidableEq G.State] in
theorem analytic_valueCurve (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.valueCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  exact germ.analytic_coordinate (BellmanVar.val s who)

omit [DecidableEq G.State] in
theorem analytic_valueIncrement (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.valueIncrement 0 := by
  exact germ.analytic_valueCurve.sub analyticAt_const

/-- The product of the raw analytic mixing coordinates at one state and joint
action. This is defined at the endpoint without first constructing a PMF. -/
def rawProfileWeight (germ : G.AnalyticBellmanGerm)
    (t : ℝ) (s : G.State) (a : G.JointAct) : ℝ :=
  ∏ who, germ.assignment t (BellmanVar.mix s who (a who))

/-- Expected stage payoff written directly in the analytic mixing
coordinates. -/
def rawStageCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t s who =>
    ∑ a, germ.rawProfileWeight t s a * G.stagePayoff s a who

/-- Expected continuation of an analytic state-payoff curve, written directly
in the analytic mixing coordinates. -/
def rawContinuationCurve (germ : G.AnalyticBellmanGerm)
    (H : ℝ → G.State → Payoff ι) :
    ℝ → G.State → Payoff ι :=
  fun t s who =>
    ∑ a, germ.rawProfileWeight t s a *
      ∑ s', (G.transition s a s').toReal * H t s' who

/-- The on-profile state kernel written directly in the analytic mixing
coordinates. -/
def rawStateKernelCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → G.State → ℝ :=
  fun t s destination =>
    ∑ a, germ.rawProfileWeight t s a *
      (G.transition s a destination).toReal

/-- Change of the analytic on-profile state kernel from its endpoint. -/
def rawStateKernelDriftCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → G.State → ℝ :=
  fun t s destination =>
    germ.rawStateKernelCurve t s destination -
      germ.rawStateKernelCurve 0 s destination

/-- One fixed public transition monitor carried by an analytic Bellman
branch, together with a quantitative lower bound on its current-profile
expectation. -/
structure StateKernelMonitorPowerCharge
    (germ : G.AnalyticBellmanGerm) where
  source : G.State
  destination : G.State
  positive : Bool
  order : ℕ
  margin : ℝ
  margin_pos : 0 < margin
  baseline_centered :
    Math.Probability.expect
        (G.finkStateKernel germ.endpointFinkPoint source)
        (pmfCoordinateTestScore
          (G.finkStateKernel germ.endpointFinkPoint source)
          destination positive) = 0
  increment_bound : ∀ observation,
    |pmfCoordinateTestScore
        (G.finkStateKernel germ.endpointFinkPoint source)
        destination positive observation| ≤ 1
  signal :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          margin * t ^ order ≤
              Math.Probability.expect
                (G.finkStateKernel (germ.finkPointAt ht) source)
                (pmfCoordinateTestScore
                  (G.finkStateKernel germ.endpointFinkPoint source)
                  destination positive) ∧
            0 <
              Math.Probability.expect
                (G.finkStateKernel (germ.finkPointAt ht) source)
                (pmfCoordinateTestScore
                  (G.finkStateKernel germ.endpointFinkPoint source)
                  destination positive)

/-- Endpoint continuation residual as a linear endomorphism of state-payoff
vectors. -/
noncomputable def endpointContinuationResidualLinearMap
    (germ : G.AnalyticBellmanGerm) :
    (G.State → Payoff ι) →ₗ[ℝ] (G.State → Payoff ι) where
  toFun H :=
    G.finkContinuationResidualVector H germ.endpointFinkPoint
  map_add' H K :=
    G.finkContinuationResidualVector_add
      H K germ.endpointFinkPoint
  map_smul' c H :=
    G.finkContinuationResidualVector_smul
      c H germ.endpointFinkPoint

/-- Finite-dimensional space of payoff vectors harmonic under the endpoint
state kernel. -/
noncomputable def endpointHarmonicSubmodule
    (germ : G.AnalyticBellmanGerm) :
    Submodule ℝ (G.State → Payoff ι) :=
  LinearMap.ker germ.endpointContinuationResidualLinearMap

omit [DecidableEq G.State] in
@[simp]
theorem mem_endpointHarmonicSubmodule_iff
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι) :
    H ∈ germ.endpointHarmonicSubmodule ↔
      G.finkContinuationResidualVector
        H germ.endpointFinkPoint = 0 := by
  rfl

/-- Span of the genuinely informative endpoint-harmonic jets already
processed by a local-response recursion. -/
structure EndpointHarmonicJetSpan
    (germ : G.AnalyticBellmanGerm) where
  carrier : Submodule ℝ (G.State → Payoff ι)
  carrier_le : carrier ≤ germ.endpointHarmonicSubmodule

namespace EndpointHarmonicJetSpan

/-- Remaining harmonic dimension.  It is the well-founded rank spent by
linearly new harmonic jets. -/
noncomputable def rank {germ : G.AnalyticBellmanGerm}
    (span : germ.EndpointHarmonicJetSpan) : ℕ :=
  Module.finrank ℝ germ.endpointHarmonicSubmodule -
    Module.finrank ℝ span.carrier

/-- Adjoin one endpoint-harmonic jet to the processed span. -/
noncomputable def extend {germ : G.AnalyticBellmanGerm}
    (span : germ.EndpointHarmonicJetSpan)
    (H : G.State → Payoff ι)
    (hH : H ∈ germ.endpointHarmonicSubmodule) :
    germ.EndpointHarmonicJetSpan where
  carrier := span.carrier ⊔ Submodule.span ℝ {H}
  carrier_le := by
    apply sup_le span.carrier_le
    apply Submodule.span_le.mpr
    intro K hK
    rcases Set.mem_singleton_iff.mp hK with rfl
    exact hH

omit [DecidableEq G.State] in
/-- A genuinely new harmonic jet strictly enlarges the processed span. -/
theorem carrier_lt_extend {germ : G.AnalyticBellmanGerm}
    (span : germ.EndpointHarmonicJetSpan)
    (H : G.State → Payoff ι)
    (hH : H ∈ germ.endpointHarmonicSubmodule)
    (hnew : H ∉ span.carrier) :
    span.carrier < (span.extend H hH).carrier := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply hnew
  rw [heq]
  change H ∈ span.carrier ⊔ Submodule.span ℝ {H}
  exact (show Submodule.span ℝ {H} ≤
      span.carrier ⊔ Submodule.span ℝ {H} from le_sup_right)
    (Submodule.subset_span (R := ℝ) (Set.mem_singleton H))

omit [DecidableEq G.State] in
/-- Extending by a genuinely new harmonic jet strictly decreases the
remaining-dimension rank. -/
theorem rank_extend_lt {germ : G.AnalyticBellmanGerm}
    (span : germ.EndpointHarmonicJetSpan)
    (H : G.State → Payoff ι)
    (hH : H ∈ germ.endpointHarmonicSubmodule)
    (hnew : H ∉ span.carrier) :
    (span.extend H hH).rank < span.rank := by
  have hstrict :
      Module.finrank ℝ span.carrier <
        Module.finrank ℝ (span.extend H hH).carrier :=
    Submodule.finrank_lt_finrank_of_lt
      (span.carrier_lt_extend H hH hnew)
  have hnext_le :
      Module.finrank ℝ (span.extend H hH).carrier ≤
        Module.finrank ℝ germ.endpointHarmonicSubmodule :=
    Submodule.finrank_mono (span.extend H hH).carrier_le
  simp only [rank]
  omega

end EndpointHarmonicJetSpan

omit [DecidableEq G.State] in
theorem analytic_rawProfileWeight
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (a : G.JointAct) :
    AnalyticAt ℝ (fun t => germ.rawProfileWeight t s a) 0 := by
  exact Finset.univ.analyticAt_fun_prod fun who _ =>
    germ.analytic_coordinate (BellmanVar.mix s who (a who))

omit [DecidableEq G.State] in
theorem analytic_rawStageCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.rawStageCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  exact Finset.univ.analyticAt_fun_sum fun a _ =>
    (germ.analytic_rawProfileWeight s a).mul analyticAt_const

omit [DecidableEq G.State] in
theorem analytic_rawContinuationCurve
    (germ : G.AnalyticBellmanGerm)
    {H : ℝ → G.State → Payoff ι}
    (hH : AnalyticAt ℝ H 0) :
    AnalyticAt ℝ (germ.rawContinuationCurve H) 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  apply Finset.univ.analyticAt_fun_sum
  intro a _
  apply (germ.analytic_rawProfileWeight s a).mul
  apply Finset.univ.analyticAt_fun_sum
  intro s' _
  exact analyticAt_const.mul
    ((analyticAt_pi_iff.mp ((analyticAt_pi_iff.mp hH) s')) who)

omit [DecidableEq G.State] in
theorem analytic_rawStateKernelCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.rawStateKernelCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro destination
  exact Finset.univ.analyticAt_fun_sum fun a _ =>
    (germ.analytic_rawProfileWeight s a).mul analyticAt_const

omit [DecidableEq G.State] in
theorem analytic_rawStateKernelDriftCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.rawStateKernelDriftCurve 0 := by
  exact germ.analytic_rawStateKernelCurve.sub analyticAt_const

omit [DecidableEq G.State] in
/-- At a positive germ point, the raw product of mixing coordinates is the
real mass of the decoded independent joint-action law. -/
theorem rawProfileWeight_eq_pmfPi_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (a : G.JointAct) :
    germ.rawProfileWeight t s a =
      (Math.PMFProduct.pmfPi
        (G.finkProfile (germ.finkPointAt ht) s) a).toReal := by
  rw [germ.finkProfile_finkPointAt]
  unfold rawProfileWeight
  rw [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro who _
  exact
    (G.bellmanDecodeProfile_apply_toReal
      (germ.solution t ht) s who (a who)).symm

omit [DecidableEq G.State] in
/-- At the endpoint, the raw mixing-coordinate product is the real mass of
the decoded endpoint joint-action law. -/
theorem rawProfileWeight_zero_eq_pmfPi_endpointProfile
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (a : G.JointAct) :
    germ.rawProfileWeight 0 s a =
      (Math.PMFProduct.pmfPi (germ.endpointProfile s) a).toReal := by
  unfold endpointProfile rawProfileWeight
  rw [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro who _
  simpa [endpoint] using
    (G.bellmanDecodeProfile_apply_toReal
      germ.endpoint_isPolynomialBellmanSolution s who (a who)).symm

omit [DecidableEq G.State] in
/-- At a positive germ point, the raw state-kernel coordinate is the real
probability assigned by the decoded Fink state kernel. -/
theorem rawStateKernelCurve_eq_finkStateKernel
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s destination : G.State) :
    germ.rawStateKernelCurve t s destination =
      (G.finkStateKernel (germ.finkPointAt ht) s destination).toReal := by
  unfold rawStateKernelCurve finkStateKernel
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawProfileWeight_eq_pmfPi_finkPointAt ht]

omit [DecidableEq G.State] in
/-- At the endpoint, the raw state-kernel coordinate is the probability
assigned by the decoded endpoint profile. -/
theorem rawStateKernelCurve_zero_eq_finkStateKernel
    (germ : G.AnalyticBellmanGerm)
    (s destination : G.State) :
    germ.rawStateKernelCurve 0 s destination =
      (G.finkStateKernel germ.endpointFinkPoint s destination).toReal := by
  unfold rawStateKernelCurve finkStateKernel
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawProfileWeight_zero_eq_pmfPi_endpointProfile,
    germ.finkProfile_endpointFinkPoint]

omit [DecidableEq G.State] in
/-- On the positive analytic branch, raw kernel drift is the coordinatewise
difference between the current and endpoint state kernels. -/
theorem rawStateKernelDriftCurve_eq_finkStateKernel_sub_endpoint
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s destination : G.State) :
    germ.rawStateKernelDriftCurve t s destination =
      (G.finkStateKernel (germ.finkPointAt ht) s destination).toReal -
        (G.finkStateKernel
          germ.endpointFinkPoint s destination).toReal := by
  rw [rawStateKernelDriftCurve,
    germ.rawStateKernelCurve_eq_finkStateKernel ht,
    germ.rawStateKernelCurve_zero_eq_finkStateKernel]

omit [DecidableEq G.State] in
/-- The raw analytic stage curve agrees with the semantic Fink expectation
at every positive germ point. -/
theorem rawStageCurve_eq_finkStageEU
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.rawStageCurve t =
      fun s who => G.finkStageEU (germ.finkPointAt ht) s who := by
  ext s who
  unfold rawStageCurve finkStageEU
  rw [Math.Probability.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawProfileWeight_eq_pmfPi_finkPointAt ht]

omit [DecidableEq G.State] in
/-- Raw analytic continuation agrees with the semantic Fink continuation at
every positive germ point. -/
theorem rawContinuationCurve_eq_finkContinuationEU
    (germ : G.AnalyticBellmanGerm)
    (H : ℝ → G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.rawContinuationCurve H t =
      fun s who =>
        G.finkContinuationEU (H t) (germ.finkPointAt ht) s who := by
  ext s who
  unfold rawContinuationCurve finkContinuationEU
  rw [Math.Probability.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawProfileWeight_eq_pmfPi_finkPointAt ht,
    Math.Probability.expect_eq_sum]

omit [DecidableEq G.State] in
/-- Raw continuation at the endpoint agrees with continuation under the
decoded endpoint Fink point. -/
theorem rawContinuationCurve_zero_eq_finkContinuationEU
    (germ : G.AnalyticBellmanGerm)
    (H : ℝ → G.State → Payoff ι) :
    germ.rawContinuationCurve H 0 =
      fun s who =>
        G.finkContinuationEU (H 0) germ.endpointFinkPoint s who := by
  ext s who
  unfold rawContinuationCurve finkContinuationEU
  rw [Math.Probability.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawProfileWeight_zero_eq_pmfPi_endpointProfile,
    germ.finkProfile_endpointFinkPoint,
    Math.Probability.expect_eq_sum]

omit [DecidableEq G.State] in
/-- Raw continuation is expectation against the raw analytic state kernel. -/
theorem rawContinuationCurve_eq_sum_rawStateKernel
    (germ : G.AnalyticBellmanGerm)
    (H : ℝ → G.State → Payoff ι)
    (t : ℝ) (s : G.State) (who : ι) :
    germ.rawContinuationCurve H t s who =
      ∑ destination,
        germ.rawStateKernelCurve t s destination *
          H t destination who := by
  unfold rawContinuationCurve rawStateKernelCurve
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro destination _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [DecidableEq G.State] in
/-- Raw continuation is additive in the continued state-payoff curve. -/
theorem rawContinuationCurve_add
    (germ : G.AnalyticBellmanGerm)
    (H K : ℝ → G.State → Payoff ι) :
    germ.rawContinuationCurve (H + K) =
      germ.rawContinuationCurve H +
        germ.rawContinuationCurve K := by
  ext t s who
  simp only [rawContinuationCurve, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

omit [DecidableEq G.State] in
/-- A scalar curve factors out of raw continuation. -/
theorem rawContinuationCurve_smul
    (germ : G.AnalyticBellmanGerm)
    (c : ℝ → ℝ) (H : ℝ → G.State → Payoff ι) :
    germ.rawContinuationCurve (fun t => c t • H t) =
      fun t => c t • germ.rawContinuationCurve H t := by
  ext t s who
  simp only [rawContinuationCurve, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hinner :
      (∑ s', (G.transition s a s').toReal *
          (c t * H t s' who)) =
        c t *
          ∑ s', (G.transition s a s').toReal *
            H t s' who := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  rw [hinner]
  ring

omit [DecidableEq G.State] in
/-- Raw continuation at one parameter depends only on the continued curve at
that parameter. -/
theorem rawContinuationCurve_congr_at
    (germ : G.AnalyticBellmanGerm)
    {H K : ℝ → G.State → Payoff ι} {t : ℝ}
    (h : H t = K t) :
    germ.rawContinuationCurve H t =
      germ.rawContinuationCurve K t := by
  unfold rawContinuationCurve
  rw [h]

omit [DecidableEq G.State] in
/-- The value curve is its endpoint plus its increment. -/
theorem valueCurve_eq_valueIncrement_add_endpoint
    (germ : G.AnalyticBellmanGerm) :
    germ.valueCurve =
      germ.valueIncrement + fun _ => germ.endpointValue := by
  ext t s who
  simp [valueIncrement, endpointValue]

omit [DecidableEq G.State] in
/-- Raw continuation of the value curve splits into continuation of its
increment and continuation of its fixed endpoint value. -/
theorem rawContinuationCurve_valueCurve_eq_add
    (germ : G.AnalyticBellmanGerm) :
    germ.rawContinuationCurve germ.valueCurve =
      germ.rawContinuationCurve germ.valueIncrement +
        germ.rawContinuationCurve (fun _ => germ.endpointValue) := by
  rw [germ.valueCurve_eq_valueIncrement_add_endpoint,
    germ.rawContinuationCurve_add]

/-- The analytic transition drift of the endpoint value under the moving
profile. -/
def endpointTransitionDriftCurve
    (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  germ.rawContinuationCurve (fun _ => germ.endpointValue) -
    fun _ => germ.endpointValue

omit [DecidableEq G.State] in
theorem analytic_endpointTransitionDriftCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.endpointTransitionDriftCurve 0 := by
  exact
    (germ.analytic_rawContinuationCurve analyticAt_const).sub
      analyticAt_const

omit [DecidableEq G.State] in
@[simp]
theorem endpointTransitionDriftCurve_zero
    (germ : G.AnalyticBellmanGerm) :
    germ.endpointTransitionDriftCurve 0 = 0 := by
  rw [endpointTransitionDriftCurve, Pi.sub_apply,
    germ.rawContinuationCurve_zero_eq_finkContinuationEU]
  exact germ.finkContinuationResidualVector_endpointValue_eq_zero

omit [DecidableEq G.State] in
/-- The endpoint-value transition drift is the endpoint value paired with
the raw state-kernel drift. -/
theorem endpointTransitionDriftCurve_eq_sum_stateKernelDrift
    (germ : G.AnalyticBellmanGerm)
    (t : ℝ) (s : G.State) (who : ι) :
    germ.endpointTransitionDriftCurve t s who =
      ∑ destination,
        germ.rawStateKernelDriftCurve t s destination *
          germ.endpointValue destination who := by
  have hzero :
      germ.rawContinuationCurve (fun _ => germ.endpointValue) 0 s who =
        germ.endpointValue s who := by
    rw [germ.rawContinuationCurve_zero_eq_finkContinuationEU]
    have hresidual :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero s) who
    exact sub_eq_zero.mp
      (by
        simpa [finkContinuationResidualVector,
          finkContinuationResidual] using hresidual)
  change
    germ.rawContinuationCurve (fun _ => germ.endpointValue) t s who -
        germ.endpointValue s who =
      ∑ destination,
        germ.rawStateKernelDriftCurve t s destination *
          germ.endpointValue destination who
  calc
    germ.rawContinuationCurve (fun _ => germ.endpointValue) t s who -
        germ.endpointValue s who =
      germ.rawContinuationCurve (fun _ => germ.endpointValue) t s who -
        germ.rawContinuationCurve (fun _ => germ.endpointValue) 0 s who := by
          rw [hzero]
    _ =
        (∑ destination,
          germ.rawStateKernelCurve t s destination *
            germ.endpointValue destination who) -
        ∑ destination,
          germ.rawStateKernelCurve 0 s destination *
            germ.endpointValue destination who := by
      rw [germ.rawContinuationCurve_eq_sum_rawStateKernel,
        germ.rawContinuationCurve_eq_sum_rawStateKernel]
    _ = ∑ destination,
        germ.rawStateKernelDriftCurve t s destination *
          germ.endpointValue destination who := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro destination _
      simp only [rawStateKernelDriftCurve]
      ring

omit [DecidableEq G.State] in
@[simp]
theorem valueIncrement_zero (germ : G.AnalyticBellmanGerm) :
    germ.valueIncrement 0 = 0 := by
  simp [valueIncrement, endpointValue]

omit [DecidableEq G.State] in
/-- Exact coupled Bellman identity for the value increment.

The second summand retains both continuation of the moving value increment
and the transition drift of the fixed endpoint value. Thus a lower value jet
cannot in general be treated as harmonic without controlling the transition
jet at the same order. -/
theorem valueIncrement_eq_coupledBellman
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.valueIncrement t =
      t ^ germ.ramification •
          (germ.rawStageCurve t - germ.endpointValue) +
        (1 - t ^ germ.ramification) •
          (germ.rawContinuationCurve germ.valueIncrement t +
            germ.endpointTransitionDriftCurve t) := by
  ext s who
  have hvalue :=
    (germ.isDiscountedStationaryBellmanEq_finkPointAt ht).2 s who
  rw [G.discountedAuxEU_eq, germ.finkValue_finkPointAt] at hvalue
  change
    (1 - (1 - t ^ germ.ramification)) *
        G.finkStageEU (germ.finkPointAt ht) s who +
      (1 - t ^ germ.ramification) *
        G.finkContinuationEU (germ.valueCurve t)
          (germ.finkPointAt ht) s who =
      germ.valueCurve t s who at hvalue
  have hstage :=
    congrFun (congrFun (germ.rawStageCurve_eq_finkStageEU ht) s) who
  have hcontinuation :=
    congrFun
      (congrFun
        (germ.rawContinuationCurve_eq_finkContinuationEU
          germ.valueCurve ht) s) who
  rw [← hstage, ← hcontinuation] at hvalue
  have hsplit :=
    congrFun
      (congrFun
        (congrFun
          germ.rawContinuationCurve_valueCurve_eq_add t) s) who
  rw [hsplit] at hvalue
  simp only [Pi.add_apply] at hvalue
  simp only [valueIncrement, endpointTransitionDriftCurve,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring_nf at hvalue ⊢
  linarith

/-- The raw relative-bias curve at the exact discount complement `t ^ q`.
It is used only away from `t = 0`. -/
def rawRelativeBiasCurve (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → Payoff ι :=
  fun t =>
    ((1 - t ^ germ.ramification) / t ^ germ.ramification) •
      germ.valueIncrement t

/-- Data certifying that the relative-bias curve extends analytically
through the singular discount endpoint. -/
structure FiniteBiasSeed (germ : G.AnalyticBellmanGerm) where
  factor : ℝ → G.State → Payoff ι
  analytic_factor : AnalyticAt ℝ factor 0
  valueIncrement_eq :
    ∀ᶠ t in 𝓝 0,
      germ.valueIncrement t = t ^ germ.ramification • factor t

namespace FiniteBiasSeed

/-- The analytic extension of the raw relative bias. -/
def extension {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    ℝ → G.State → Payoff ι :=
  fun t => (1 - t ^ germ.ramification) • seed.factor t

/-- The selected finite relative-bias coefficient. -/
def H {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    G.State → Payoff ι :=
  seed.extension 0

omit [DecidableEq G.State] in
theorem analytic_extension {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    AnalyticAt ℝ seed.extension 0 := by
  exact
    ((analyticAt_const.sub (analyticAt_id.pow germ.ramification)).smul
      seed.analytic_factor)

omit [DecidableEq G.State] in
theorem extension_zero {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    seed.extension 0 = seed.factor 0 := by
  have hq : germ.ramification ≠ 0 :=
    Nat.ne_of_gt germ.ramification_pos
  simp [extension, hq]

omit [DecidableEq G.State] in
theorem eventually_extension_eq_rawRelativeBiasCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    ∀ᶠ t in nhdsWithin 0 ({0}ᶜ),
      seed.extension t = germ.rawRelativeBiasCurve t := by
  filter_upwards
      [seed.valueIncrement_eq.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t htFactor ht
  have ht_ne : t ≠ 0 := by simpa using ht
  have hpow_ne : t ^ germ.ramification ≠ 0 :=
    pow_ne_zero _ ht_ne
  rw [rawRelativeBiasCurve, htFactor, extension]
  simp only [smul_smul]
  congr 1
  field_simp

omit [DecidableEq G.State] in
theorem tendsto_rawRelativeBiasCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed) :
    Tendsto germ.rawRelativeBiasCurve
      (nhdsWithin 0 ({0}ᶜ)) (nhds seed.H) := by
  exact Filter.Tendsto.congr'
    seed.eventually_extension_eq_rawRelativeBiasCurve
    seed.analytic_extension.continuousAt.continuousWithinAt

omit [DecidableEq G.State] in
/-- At every positive germ point, the finite-bias forcing either has a
Poisson correction `K`, or retains a nonzero harmonic obstruction.

This selects the second hierarchy coefficient exactly in the branch where
it exists.  The nonzero harmonic branch is intentionally returned to the
global rank/phase invariant rather than hidden as a failed linear solve. -/
theorem poissonCorrection_or_harmonicObstructionAt
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    (∃ K : G.State → Payoff ι,
      G.finkBellmanForcingVector germ.endpointValue seed.H
          (germ.finkPointAt ht) =
        -G.finkContinuationResidualVector K (germ.finkPointAt ht)) ∨
      ∃ O K : G.State → Payoff ι,
        G.finkContinuationResidualVector O (germ.finkPointAt ht) = 0 ∧
        O ≠ 0 ∧
        G.finkBellmanForcingVector germ.endpointValue seed.H
            (germ.finkPointAt ht) =
          O - G.finkContinuationResidualVector K (germ.finkPointAt ht) := by
  obtain ⟨O, K, hO, hforcing, _hcesaro⟩ :=
    G.exists_finkBellmanForcing_harmonicObstruction_decomposition
      (germ.finkPointAt ht) germ.endpointValue seed.H
  by_cases hOzero : O = 0
  · left
    refine ⟨-K, ?_⟩
    rw [hforcing, hOzero, zero_add,
      G.finkContinuationResidualVector_neg]
    simp
  · right
    refine ⟨O, -K, hO, hOzero, ?_⟩
    rw [hforcing, G.finkContinuationResidualVector_neg]
    abel

end FiniteBiasSeed

/-- A nonzero value jet appearing strictly below the discount scale. -/
structure LowerValueJet (germ : G.AnalyticBellmanGerm) where
  order : ℕ
  order_lt_ramification : order < germ.ramification
  factor : ℝ → G.State → Payoff ι
  analytic_factor : AnalyticAt ℝ factor 0
  leading_ne_zero : factor 0 ≠ 0
  valueIncrement_eq :
    ∀ᶠ t in 𝓝 0,
      germ.valueIncrement t = t ^ order • factor t

namespace LowerValueJet

/-- The analytic coefficient left in the moving-profile transition drift
after removing the order of a lower value jet.

The last term is the discounted stage contribution.  Its exponent is
positive because the jet occurs strictly below the discount scale. -/
def coupledTransitionFactor {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    ℝ → G.State → Payoff ι :=
  fun t =>
    (1 / (1 - t ^ germ.ramification)) • jet.factor t -
      germ.rawContinuationCurve jet.factor t -
      (t ^ (germ.ramification - jet.order) /
          (1 - t ^ germ.ramification)) •
        (germ.rawStageCurve t - germ.endpointValue)

omit [DecidableEq G.State] in
/-- The coupled transition coefficient is analytic through the singular
discount endpoint. -/
theorem analytic_coupledTransitionFactor
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    AnalyticAt ℝ jet.coupledTransitionFactor 0 := by
  have hden :
      AnalyticAt ℝ (fun t : ℝ => 1 - t ^ germ.ramification) 0 :=
    analyticAt_const.sub (analyticAt_id.pow germ.ramification)
  have hden_ne :
      1 - (0 : ℝ) ^ germ.ramification ≠ 0 := by
    simp [Nat.ne_of_gt germ.ramification_pos]
  have hone :
      AnalyticAt ℝ
        (fun t : ℝ => 1 / (1 - t ^ germ.ramification)) 0 :=
    analyticAt_const.div hden hden_ne
  have hstage :
      AnalyticAt ℝ
        (fun t : ℝ =>
          t ^ (germ.ramification - jet.order) /
            (1 - t ^ germ.ramification)) 0 :=
    (analyticAt_id.pow
      (germ.ramification - jet.order)).div hden hden_ne
  have hendpoint :
      AnalyticAt ℝ (fun _ : ℝ => germ.endpointValue) 0 :=
    analyticAt_const
  exact
    (hone.smul jet.analytic_factor).sub
      (germ.analytic_rawContinuationCurve jet.analytic_factor) |>.sub
        (hstage.smul
          (germ.analytic_rawStageCurve.sub hendpoint))

omit [DecidableEq G.State] in
/-- The leading transition drift is exactly the failure of the lower value
jet to be harmonic under the endpoint profile. -/
theorem coupledTransitionFactor_zero
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    jet.coupledTransitionFactor 0 =
      -G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint := by
  have hsub_ne :
      germ.ramification - jet.order ≠ 0 :=
    (Nat.sub_pos_of_lt jet.order_lt_ramification).ne'
  have hramification_ne : germ.ramification ≠ 0 :=
    Nat.ne_of_gt germ.ramification_pos
  ext s who
  simp only [coupledTransitionFactor, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [germ.rawContinuationCurve_zero_eq_finkContinuationEU]
  simp [hsub_ne, hramification_ne, finkContinuationResidualVector,
    finkContinuationResidual]

omit [DecidableEq G.State] in
/-- Pointwise factorization of the moving-profile transition drift by the
order of a lower value jet. -/
theorem endpointTransitionDriftCurve_eq_order_smul
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet)
    {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (ht_one : t < 1)
    (hfactor :
      germ.valueIncrement t = t ^ jet.order • jet.factor t) :
    germ.endpointTransitionDriftCurve t =
      t ^ jet.order • jet.coupledTransitionFactor t := by
  have hramification_ne : germ.ramification ≠ 0 :=
    Nat.ne_of_gt germ.ramification_pos
  have hpow_lt :
      t ^ germ.ramification < 1 :=
    pow_lt_one₀ ht.1.le ht_one hramification_ne
  have hden_ne :
      1 - t ^ germ.ramification ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpow_lt)
  have horder_le : jet.order ≤ germ.ramification :=
    Nat.le_of_lt jet.order_lt_ramification
  have hpow :
      t ^ germ.ramification =
        t ^ jet.order *
          t ^ (germ.ramification - jet.order) := by
    rw [← pow_add, Nat.add_sub_of_le horder_le]
  have hcontinuation :
      germ.rawContinuationCurve germ.valueIncrement t =
        t ^ jet.order •
          germ.rawContinuationCurve jet.factor t := by
    rw [germ.rawContinuationCurve_congr_at
      (K := fun u => u ^ jet.order • jet.factor u) hfactor]
    exact congrFun
      (germ.rawContinuationCurve_smul
        (fun u => u ^ jet.order) jet.factor) t
  have hbellman := germ.valueIncrement_eq_coupledBellman ht
  rw [hfactor, hcontinuation] at hbellman
  ext s who
  have hcoordinate :=
    congrFun (congrFun hbellman s) who
  simp only [coupledTransitionFactor, Pi.sub_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul] at hcoordinate ⊢
  rw [hpow] at hden_ne hcoordinate ⊢
  field_simp [hden_ne]
  ring_nf at hcoordinate ⊢
  linarith

omit [DecidableEq G.State] in
/-- The coupled transition factorization holds as a punctured positive germ.
The cutoff by `1` only keeps the Bellman denominator nonzero. -/
theorem eventually_endpointTransitionDriftCurve_eq_order_smul
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    ∀ᶠ t in 𝓝[Set.Ioo (0 : ℝ) (min germ.radius 1)] 0,
      germ.endpointTransitionDriftCurve t =
        t ^ jet.order • jet.coupledTransitionFactor t := by
  filter_upwards
      [jet.valueIncrement_eq.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t hfactor ht
  exact jet.endpointTransitionDriftCurve_eq_order_smul
    ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    (ht.2.trans_le (min_le_right _ _)) hfactor

omit [DecidableEq G.State] in
/-- Right-germ form of the coupled transition factorization. -/
theorem eventually_endpointTransitionDriftCurve_eq_order_smul_right
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      germ.endpointTransitionDriftCurve t =
        t ^ jet.order • jet.coupledTransitionFactor t := by
  have hcutoff :
      (0 : ℝ) < min germ.radius 1 :=
    lt_min germ.radius_pos zero_lt_one
  filter_upwards
      [Ioo_mem_nhdsGT hcutoff,
        jet.valueIncrement_eq.filter_mono nhdsWithin_le_nhds] with
      t ht hfactor
  exact jet.endpointTransitionDriftCurve_eq_order_smul
    ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    (ht.2.trans_le (min_le_right _ _)) hfactor

omit [DecidableEq G.State] in
/-- A lower value jet has an endpoint-harmonic leading coefficient exactly
when its coupled transition coefficient vanishes. -/
theorem coupledTransitionFactor_zero_eq_zero_iff
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    jet.coupledTransitionFactor 0 = 0 ↔
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint = 0 := by
  rw [jet.coupledTransitionFactor_zero]
  exact neg_eq_zero

omit [DecidableEq G.State] in
/-- If the lower jet is not endpoint-harmonic, at least one coordinate of
the analytic state-kernel drift is a nonzero right germ. -/
theorem exists_rawStateKernelDrift_not_eventually_zero
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet)
    (hnonharmonic :
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint ≠ 0) :
    ∃ index : G.State × G.State,
      ¬∀ᶠ t in 𝓝[>] (0 : ℝ),
        germ.rawStateKernelDriftCurve t index.1 index.2 = 0 := by
  have hcoupled_ne :
      jet.coupledTransitionFactor 0 ≠ 0 := by
    intro hzero
    exact hnonharmonic
      (jet.coupledTransitionFactor_zero_eq_zero_iff.mp hzero)
  obtain ⟨s, who, hcoordinate⟩ :
      ∃ s who, jet.coupledTransitionFactor 0 s who ≠ 0 := by
    by_contra hnot
    simp only [not_exists, not_not] at hnot
    apply hcoupled_ne
    funext s who
    exact hnot s who
  have hcoordinate_analytic :
      AnalyticAt ℝ
        (fun t => jet.coupledTransitionFactor t s who) 0 := by
    exact
      (analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          jet.analytic_coupledTransitionFactor) s)) who
  have hcoordinate_ne :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        jet.coupledTransitionFactor t s who ≠ 0 :=
    hcoordinate_analytic.continuousAt.eventually_ne hcoordinate
  have hdrift_ne :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        germ.endpointTransitionDriftCurve t s who ≠ 0 := by
    filter_upwards
        [jet.eventually_endpointTransitionDriftCurve_eq_order_smul_right,
          hcoordinate_ne.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with t hfactor hnonzero ht
    have hpow_ne : t ^ jet.order ≠ 0 :=
      pow_ne_zero _ (ne_of_gt ht)
    have hcomponent :=
      congrFun (congrFun hfactor s) who
    rw [hcomponent]
    exact mul_ne_zero hpow_ne hnonzero
  by_contra hnot
  simp only [not_exists, not_not] at hnot
  have hall :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ∀ destination,
          germ.rawStateKernelDriftCurve t s destination = 0 :=
    Filter.eventually_all.mpr fun destination =>
      hnot (s, destination)
  have hdrift_zero :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        germ.endpointTransitionDriftCurve t s who = 0 := by
    filter_upwards [hall] with t ht
    rw [germ.endpointTransitionDriftCurve_eq_sum_stateKernelDrift]
    simp [ht]
  obtain ⟨t, ht_ne, ht_zero⟩ := (hdrift_ne.and hdrift_zero).exists
  exact ht_ne ht_zero

omit [DecidableEq G.State] in
/-- A nonharmonic lower jet yields one fixed oriented public transition
coordinate with a positive power-law signal.  The sign orients the score;
the implemented transition law is never reversed. -/
theorem exists_fixed_oriented_stateKernelDrift_powerCharge
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet)
    (hnonharmonic :
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint ≠ 0) :
    ∃ s destination σ n c,
      (σ = -1 ∨ σ = 1) ∧
        0 < c ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          c * t ^ n ≤
              σ * germ.rawStateKernelDriftCurve t s destination ∧
            0 < σ * germ.rawStateKernelDriftCurve t s destination ∧
            ∀ s' destination',
              |germ.rawStateKernelDriftCurve t s' destination'| ≤
                σ * germ.rawStateKernelDriftCurve t s destination := by
  let f : G.State × G.State → ℝ → ℝ :=
    fun index t =>
      germ.rawStateKernelDriftCurve t index.1 index.2
  have hf : ∀ index, AnalyticAt ℝ (f index) 0 := by
    intro index
    exact
      (analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelDriftCurve) index.1)) index.2
  obtain ⟨index₀, hindex₀⟩ :=
    jet.exists_rawStateKernelDrift_not_eventually_zero hnonharmonic
  letI : Nonempty (G.State × G.State) := ⟨index₀⟩
  obtain ⟨index, σ, hσ, hmax⟩ :=
    Math.finite_analytic_family_eventually_fixed_oriented_abs_maximizer
      f hf ⟨index₀, hindex₀⟩
  have horiented_analytic :
      AnalyticAt ℝ (fun t => σ * f index t) 0 :=
    analyticAt_const.mul (hf index)
  have horiented_pos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < σ * f index t :=
    hmax.mono fun _ h => h.1
  obtain ⟨n, c, hc, hpower⟩ :=
    Math.analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      horiented_analytic horiented_pos
  refine ⟨index.1, index.2, σ, n, c, hσ, hc, ?_⟩
  filter_upwards [hmax, hpower] with t htmax htpower
  refine ⟨by simpa [f] using htpower, htmax.1, ?_⟩
  intro s' destination'
  exact htmax.2 (s', destination')

/-- Operational form of a nonharmonic lower jet: one fixed signed coordinate
monitor is centered under the endpoint kernel, bounded by one, and has a
positive power-law expectation under every sufficiently small current
on-profile kernel. -/
theorem exists_fixed_stateKernelMonitor_powerCharge
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet)
    (hnonharmonic :
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint ≠ 0) :
    ∃ s destination positive n c,
      0 < c ∧
        Math.Probability.expect
            (G.finkStateKernel germ.endpointFinkPoint s)
            (pmfCoordinateTestScore
              (G.finkStateKernel germ.endpointFinkPoint s)
              destination positive) = 0 ∧
        (∀ observation,
          |pmfCoordinateTestScore
              (G.finkStateKernel germ.endpointFinkPoint s)
              destination positive observation| ≤ 1) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              c * t ^ n ≤
                  Math.Probability.expect
                    (G.finkStateKernel (germ.finkPointAt ht) s)
                    (pmfCoordinateTestScore
                      (G.finkStateKernel germ.endpointFinkPoint s)
                      destination positive) ∧
                0 <
                  Math.Probability.expect
                    (G.finkStateKernel (germ.finkPointAt ht) s)
                    (pmfCoordinateTestScore
                      (G.finkStateKernel germ.endpointFinkPoint s)
                      destination positive) := by
  obtain ⟨s, destination, σ, n, c, hσ, hc, hcharge⟩ :=
    jet.exists_fixed_oriented_stateKernelDrift_powerCharge hnonharmonic
  have hcutoff :
      Ioo (0 : ℝ) germ.radius ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT germ.radius_pos
  rcases hσ with hσ | hσ
  · subst σ
    refine ⟨s, destination, false, n, c, hc,
      expect_pmfCoordinateTestScore_baseline _ _ _, ?_, ?_⟩
    · exact fun observation =>
        abs_pmfCoordinateTestScore_le_one _ _ _ observation
    · filter_upwards [hcharge, hcutoff] with t htcharge ht
      refine ⟨ht, fun ht' => ?_⟩
      rw [expect_pmfCoordinateTestScore]
      change
        c * t ^ n ≤
            (-1 : ℝ) *
              ((G.finkStateKernel
                    (germ.finkPointAt ht') s destination).toReal -
                (G.finkStateKernel
                    germ.endpointFinkPoint s destination).toReal) ∧
          0 <
            (-1 : ℝ) *
              ((G.finkStateKernel
                    (germ.finkPointAt ht') s destination).toReal -
                (G.finkStateKernel
                    germ.endpointFinkPoint s destination).toReal)
      rw [← germ.rawStateKernelDriftCurve_eq_finkStateKernel_sub_endpoint
        ht' s destination]
      exact ⟨htcharge.1, htcharge.2.1⟩
  · subst σ
    refine ⟨s, destination, true, n, c, hc,
      expect_pmfCoordinateTestScore_baseline _ _ _, ?_, ?_⟩
    · exact fun observation =>
        abs_pmfCoordinateTestScore_le_one _ _ _ observation
    · filter_upwards [hcharge, hcutoff] with t htcharge ht
      refine ⟨ht, fun ht' => ?_⟩
      rw [expect_pmfCoordinateTestScore]
      change
        c * t ^ n ≤
            (1 : ℝ) *
              ((G.finkStateKernel
                    (germ.finkPointAt ht') s destination).toReal -
                (G.finkStateKernel
                    germ.endpointFinkPoint s destination).toReal) ∧
          0 <
            (1 : ℝ) *
              ((G.finkStateKernel
                    (germ.finkPointAt ht') s destination).toReal -
                (G.finkStateKernel
                    germ.endpointFinkPoint s destination).toReal)
      rw [← germ.rawStateKernelDriftCurve_eq_finkStateKernel_sub_endpoint
        ht' s destination]
      exact ⟨htcharge.1, htcharge.2.1⟩

/-- Exact operational split for a lower value jet.  Either its leading
coefficient is harmonic under the endpoint profile, or a fixed bounded
public transition monitor detects the moving on-profile kernel with a
power-law margin. -/
theorem harmonic_or_stateKernelMonitorPowerCharge
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet) :
    G.finkContinuationResidualVector
          (jet.factor 0) germ.endpointFinkPoint = 0 ∨
      Nonempty germ.StateKernelMonitorPowerCharge := by
  by_cases hharmonic :
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint = 0
  · exact Or.inl hharmonic
  · right
    obtain ⟨s, destination, positive, n, c, hc,
        hcentered, hbound, hsignal⟩ :=
      jet.exists_fixed_stateKernelMonitor_powerCharge hharmonic
    exact ⟨
      { source := s
        destination := destination
        positive := positive
        order := n
        margin := c
        margin_pos := hc
        baseline_centered := hcentered
        increment_bound := hbound
        signal := hsignal }⟩

/-- Progress alternative relative to the endpoint-harmonic jets already
processed by a local-response recursion.

The leading coefficient is either already in the processed span, is a new
harmonic direction whose adjunction strictly lowers the remaining dimension,
or yields a fixed bounded transition monitor with a power-law charge. -/
theorem redundant_or_rankDecrease_or_stateKernelMonitorPowerCharge
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan) :
    jet.factor 0 ∈ span.carrier ∨
      (∃ hH : jet.factor 0 ∈ germ.endpointHarmonicSubmodule,
        (span.extend (jet.factor 0) hH).rank < span.rank) ∨
      Nonempty germ.StateKernelMonitorPowerCharge := by
  by_cases hharmonic :
      G.finkContinuationResidualVector
        (jet.factor 0) germ.endpointFinkPoint = 0
  · have hH : jet.factor 0 ∈ germ.endpointHarmonicSubmodule :=
      (germ.mem_endpointHarmonicSubmodule_iff (jet.factor 0)).2 hharmonic
    by_cases hprocessed : jet.factor 0 ∈ span.carrier
    · exact Or.inl hprocessed
    · exact Or.inr <| Or.inl
        ⟨hH, span.rank_extend_lt (jet.factor 0) hH hprocessed⟩
  · exact Or.inr <| Or.inr <|
      (jet.harmonic_or_stateKernelMonitorPowerCharge).resolve_left hharmonic

end LowerValueJet

/-- Exact analytic-order condition for a finite relative bias. -/
def HasFiniteBiasOrder (germ : G.AnalyticBellmanGerm) : Prop :=
  (germ.ramification : ℕ∞) ≤ analyticOrderAt germ.valueIncrement 0

omit [DecidableEq G.State] in
/-- If the value increment vanishes to at least the discount order, its
relative bias has an analytic extension. -/
theorem finiteBiasSeed_of_hasFiniteBiasOrder
    (germ : G.AnalyticBellmanGerm)
    (horder : germ.HasFiniteBiasOrder) :
    Nonempty germ.FiniteBiasSeed := by
  obtain ⟨factor, hfactorAnalytic, hfactor⟩ :=
    (natCast_le_analyticOrderAt germ.analytic_valueIncrement).mp horder
  exact ⟨
    { factor := factor
      analytic_factor := hfactorAnalytic
      valueIncrement_eq := by
        simpa only [sub_zero] using hfactor }⟩

omit [DecidableEq G.State] in
/-- If finite relative bias fails, analytic order produces one unique
nonzero lower-order hierarchy jet. -/
theorem lowerValueJet_of_not_hasFiniteBiasOrder
    (germ : G.AnalyticBellmanGerm)
    (horder : ¬germ.HasFiniteBiasOrder) :
    Nonempty germ.LowerValueJet := by
  have hlt :
      analyticOrderAt germ.valueIncrement 0 <
        (germ.ramification : ℕ∞) :=
    lt_of_not_ge horder
  have hneTop :
      analyticOrderAt germ.valueIncrement 0 ≠ ⊤ := by
    exact ne_top_of_lt hlt
  obtain ⟨factor, hfactorAnalytic, hfactorZero, hfactor⟩ :=
    (germ.analytic_valueIncrement.analyticOrderAt_ne_top.mp hneTop)
  let order := analyticOrderNatAt germ.valueIncrement 0
  have horderCast :
      (order : ℕ∞) = analyticOrderAt germ.valueIncrement 0 := by
    exact Nat.cast_analyticOrderNatAt hneTop
  have horderLt : order < germ.ramification := by
    exact_mod_cast horderCast.symm ▸ hlt
  exact ⟨
    { order := order
      order_lt_ramification := horderLt
      factor := factor
      analytic_factor := hfactorAnalytic
      leading_ne_zero := hfactorZero
      valueIncrement_eq := by
        filter_upwards [hfactor] with t ht
        simpa only [order, sub_zero] using ht }⟩

omit [DecidableEq G.State] in
/-- Canonical first-level hierarchy extraction.

The first branch supplies a finite relative-bias coefficient `H`.  The
second branch supplies the unique nonzero value jet below the discount
scale. -/
theorem finiteBiasSeed_or_lowerValueJet
    (germ : G.AnalyticBellmanGerm) :
    Nonempty germ.FiniteBiasSeed ∨ Nonempty germ.LowerValueJet := by
  by_cases horder : germ.HasFiniteBiasOrder
  · exact Or.inl (germ.finiteBiasSeed_of_hasFiniteBiasOrder horder)
  · exact Or.inr (germ.lowerValueJet_of_not_hasFiniteBiasOrder horder)

omit [DecidableEq G.State] in
/-- On a positive Bellman-germ point, the raw value formula agrees with
Fink's relative bias around the endpoint value. -/
theorem finkRelativeBias_finkPointAt_eq_rawRelativeBiasCurve
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.finkRelativeBias
        (1 - t ^ germ.ramification)
        germ.endpointValue (germ.finkPointAt ht) =
      germ.rawRelativeBiasCurve t := by
  ext s who
  unfold finkRelativeBias rawRelativeBiasCurve valueIncrement
    valueCurve endpointValue
  rw [germ.finkValue_finkPointAt ht]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hpow_ne : t ^ germ.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht.1)
  field_simp [hpow_ne]
  ring

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
