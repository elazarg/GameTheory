/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.InvisibleResponseCompatibility
import GameTheory.Concepts.Stochastic.PlayerInvisibleBiasAlternative
import GameTheory.Concepts.Stochastic.ProcessedHarmonicDeviationAccount

/-!
# Finite quotient alternative for processed invisible responses

Fix a player and a processed lower value jet.  Suppose every invisible
endpoint-neutral action lies in the high-order branch at the lower-jet
scale, with an analytic quotient.

Finite linear compatibility gives an exact operational alternative:

* one scalar state potential represents every quotient against the actual
  endpoint transition difference; adding its player-coordinate embedding to
  the processed jet makes every indexed continuation gain nonpositive; or
* one actual invisible action owned by the fixed player has a fixed bounded
  oriented transition-coordinate signal with a positive power-law margin.

The second branch is public statistical evidence.  Its Boolean orientation
does not reverse the action and does not assert that the action is a
profitable or credible punishment.  The first branch is an endpoint
absorption statement, not yet a bounded realized account: the new potential
need not be harmonic under the endpoint baseline kernel.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Filter Math Math.Probability Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- A simultaneous high-order quotient choice for all invisible neutral
actions of one player. -/
structure InvisibleNeutralQuotientFamily
    (jet : germ.LowerValueJet) (who : ι) where
  quotient : germ.InvisibleNeutralAction who → ℝ → ℝ
  analytic : ∀ response, AnalyticAt ℝ (quotient response) 0
  factorization : ∀ response,
    ∀ᶠ t in 𝓝 (0 : ℝ),
      endpointPureDeviationDriftCurve germ
          response.source who response.1.2 t =
        t ^ jet.order * quotient response t

/-- Common-potential branch.  The same scalar potential represents every
quotient and its player-coordinate embedding absorbs the quotient into the
processed leading continuation vector. -/
structure InvisibleQuotientCorrection
    (jet : germ.LowerValueJet) (who : ι)
    (family : jet.InvisibleNeutralQuotientFamily who) where
  potential : G.State → ℝ
  quotient_eq :
    ∀ response : germ.InvisibleNeutralAction who,
    family.quotient response 0 =
      G.finkContinuationGain
        (G.finkPlayerPotential who potential)
        germ.endpointFinkPoint
        response.source who response.1.2
  corrected_gain_nonpos :
    ∀ response : germ.InvisibleNeutralAction who,
    G.finkContinuationGain
        (jet.factor 0 + G.finkPlayerPotential who potential)
        germ.endpointFinkPoint
        response.source who response.1.2 ≤ 0
  account_coefficient_nonpos :
    ∀ response : germ.InvisibleNeutralAction who,
      family.quotient response 0 +
          expect
            (G.finkPureDeviationStateKernel
              germ.endpointFinkPoint
              response.source who response.1.2)
            (fun successor =>
              jet.endpointCoordinatePotential who successor -
                jet.endpointCoordinatePotential who response.source) ≤
        0

/-- Strong correction branch: the quotient potential is also harmonic under
the endpoint baseline kernel, so every represented quotient is an actual
bounded state-account increment, not merely a comparison-versus-baseline
pairing. -/
structure HarmonicInvisibleQuotientCorrection
    (jet : germ.LowerValueJet) (who : ι)
    (family : jet.InvisibleNeutralQuotientFamily who) where
  potential : G.State → ℝ
  harmonic : ∀ source,
    expect (G.finkStateKernel germ.endpointFinkPoint source) potential =
      potential source
  quotient_eq : ∀ response : germ.InvisibleNeutralAction who,
    family.quotient response 0 =
      G.finkContinuationGain
        (G.finkPlayerPotential who potential)
        germ.endpointFinkPoint
        response.source who response.1.2
  quotient_eq_expectedAccountIncrement :
    ∀ response : germ.InvisibleNeutralAction who,
      family.quotient response 0 =
        expect response.kernel
          (fun successor =>
            potential successor - potential response.source)
  corrected_gain_nonpos :
    ∀ response : germ.InvisibleNeutralAction who,
      G.finkContinuationGain
          (jet.factor 0 + G.finkPlayerPotential who potential)
          germ.endpointFinkPoint
          response.source who response.1.2 ≤
        0

/-- Owned statistical branch.  The response is an actual pure action of the
fixed player; only the public score is oriented. -/
structure OwnedInvisibleTransitionSignal
    (jet : germ.LowerValueJet) (who : ι)
    (family : jet.InvisibleNeutralQuotientFamily who) where
  response : germ.InvisibleNeutralAction who
  positive : Bool
  destination : G.State
  order : ℕ
  margin : ℝ
  margin_pos : 0 < margin
  quotient_oriented_pos :
    0 <
      responseOrientation positive *
        family.quotient response 0
  signal :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      margin * t ^ order ≤
          responseOrientation positive *
            (germ.rawPureDeviationStateKernelCurve
                t response.source who response.1.2 destination -
              germ.rawStateKernelCurve
                t response.source destination) ∧
        0 <
          responseOrientation positive *
            (germ.rawPureDeviationStateKernelCurve
                t response.source who response.1.2 destination -
              germ.rawStateKernelCurve
                t response.source destination)

/-- Owned low-order branch.  The actual action's endpoint-value transition
drift is negative with a fixed power-law margin before the lower-jet scale.
-/
structure OwnedInvisibleLowOrderDrift
    (jet : germ.LowerValueJet) (who : ι) where
  response : germ.InvisibleNeutralAction who
  order : ℕ
  factor : ℝ → ℝ
  margin : ℝ
  order_pos : 0 < order
  order_lt_jet : order < jet.order
  factor_analytic : AnalyticAt ℝ factor 0
  factor_zero_neg : factor 0 < 0
  margin_pos : 0 < margin
  factorization :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      endpointPureDeviationDriftCurve germ
          response.source who response.1.2 t =
        t ^ order * factor t
  signal :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      margin * t ^ order ≤
        -endpointPureDeviationDriftCurve germ
          response.source who response.1.2 t

omit [DecidableEq G.State] in
/-- The endpoint transition difference used by finite compatibility is
exactly the continuation gain of the embedded scalar potential. -/
theorem endpointResponseDifference_dotProduct_eq_finkContinuationGain
    (who : ι) (response : germ.InvisibleNeutralAction who)
    (potential : G.State → ℝ) :
    dotProduct
        (endpointResponseDifference
          (fun source t destination =>
            germ.rawStateKernelCurve t source destination)
          (fun action : germ.InvisibleNeutralAction who =>
            action.source)
          (fun action t destination =>
            germ.rawPureDeviationStateKernelCurve
              t action.source who action.1.2 destination)
          response)
        potential =
      G.finkContinuationGain
        (G.finkPlayerPotential who potential)
        germ.endpointFinkPoint
        response.source who response.1.2 := by
  rw [G.finkContinuationGain_playerPotential_self]
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum]
  change
    (∑ destination,
      (germ.rawPureDeviationStateKernelCurve
          0 response.source who response.1.2 destination -
        germ.rawStateKernelCurve
          0 response.source destination) *
        potential destination) =
      (∑ destination,
        (G.finkPureDeviationStateKernel
          germ.endpointFinkPoint
          response.source who response.1.2 destination).toReal *
            potential destination) -
        ∑ destination,
          (G.finkStateKernel
            germ.endpointFinkPoint
            response.source destination).toReal *
              potential destination
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro destination _
  rw [
    germ.rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint,
    germ.rawStateKernelCurve_zero_eq_finkStateKernel]
  ring

omit [DecidableEq G.State] in
/-- The raw moving baseline and pure-deviation laws have equal total mass on
a small positive interval. -/
theorem eventually_sum_rawInvisibleKernel_eq
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (response : germ.InvisibleNeutralAction who) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∑ destination,
          germ.rawPureDeviationStateKernelCurve
            t response.source who response.1.2 destination =
        ∑ destination,
          germ.rawStateKernelCurve
            t response.source destination := by
  filter_upwards
      [Ioo_mem_nhdsGT germ.radius_pos] with t ht
  calc
    (∑ destination,
        germ.rawPureDeviationStateKernelCurve
          t response.source who response.1.2 destination) =
        ∑ destination,
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.source who response.1.2 destination).toReal := by
      apply Finset.sum_congr rfl
      intro destination _
      rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht]
    _ = 1 := pmf_toReal_sum_one _
    _ =
        ∑ destination,
          (G.finkStateKernel
            (germ.finkPointAt ht)
            response.source destination).toReal := by
      rw [pmf_toReal_sum_one]
    _ =
        ∑ destination,
          germ.rawStateKernelCurve
            t response.source destination := by
      apply Finset.sum_congr rfl
      intro destination _
      rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]

omit [DecidableEq G.State] in
/-- Honest finite endpoint alternative for all high-order invisible
responses owned by one player. -/
theorem
    exists_invisibleQuotientCorrection_or_ownedTransitionSignal
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι)
    [Nonempty (germ.InvisibleNeutralAction who)]
    (family : jet.InvisibleNeutralQuotientFamily who) :
    Nonempty (jet.InvisibleQuotientCorrection who family) ∨
      Nonempty (jet.OwnedInvisibleTransitionSignal who family) := by
  let baseline : G.State → ℝ → G.State → ℝ :=
    fun source t destination =>
      germ.rawStateKernelCurve t source destination
  let source : germ.InvisibleNeutralAction who → G.State :=
    fun response => response.source
  let forward :
      germ.InvisibleNeutralAction who → ℝ → G.State → ℝ :=
    fun response t destination =>
      germ.rawPureDeviationStateKernelCurve
        t response.source who response.1.2 destination
  let endpoint : G.State → ℝ :=
    fun destination => germ.endpointValue destination who
  have baseline_analytic :
      ∀ state destination,
        AnalyticAt ℝ
          (fun t => baseline state t destination) 0 := by
    intro state destination
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelCurve state) destination)
  have forward_analytic :
      ∀ response destination,
        AnalyticAt ℝ
          (fun t => forward response t destination) 0 := by
    intro response destination
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStateKernelCurve
              response.source) who) response.1.2) destination)
  have mass_eq :
      ∀ response,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∑ destination, forward response t destination =
            ∑ destination,
              baseline (source response) t destination := by
    intro response
    exact eventually_sum_rawInvisibleKernel_eq germ who response
  have factorization :
      ∀ response,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          finiteStateTransitionDrift
              (baseline (source response))
              (forward response)
              (fun _ => endpoint) t =
            t ^ jet.order * family.quotient response t := by
    intro response
    filter_upwards
        [family.factorization response |>
          Filter.Eventually.filter_mono nhdsWithin_le_nhds] with
        t ht
    simpa only [finiteStateTransitionDrift, finiteStatePairing,
      endpointPureDeviationDriftCurve,
      rawPureDeviationContinuationGainCurve,
      baseline, source, forward, endpoint, mul_comm] using ht
  rcases
      exists_endpointPotential_or_owned_orientedResponse
        baseline source forward endpoint family.quotient
        baseline_analytic forward_analytic mass_eq family.analytic
        factorization with
    correction | signal
  · left
    obtain ⟨potential, represents⟩ := correction
    refine ⟨{
      potential := potential
      quotient_eq := ?_
      corrected_gain_nonpos := ?_
      account_coefficient_nonpos := ?_ }⟩
    · intro response
      rw [←
        endpointResponseDifference_dotProduct_eq_finkContinuationGain
          who response potential]
      exact (represents response).symm
    · intro response
      rw [G.finkContinuationGain_add]
      have coefficient_nonpos :=
        jet.quotient_add_leadingContinuationGain_nonpos
          response.source who response.1.2
          (family.quotient response)
          (family.analytic response)
          (family.factorization response)
      have quotient_eq :
          family.quotient response 0 =
            G.finkContinuationGain
              (G.finkPlayerPotential who potential)
              germ.endpointFinkPoint
              response.source who response.1.2 := by
        rw [←
          endpointResponseDifference_dotProduct_eq_finkContinuationGain
            who response potential]
        exact (represents response).symm
      linarith
    · intro response
      exact
        jet.quotient_add_expectedAccountIncrement_nonpos_of_processed
          span processed response.source who response.1.2
          (family.quotient response)
          (family.analytic response)
          (family.factorization response)
  · right
    obtain ⟨_coefficient, response, positive, destination,
      order, margin, _balance, _total, _weight_pos,
      quotient_pos, margin_pos, evidence⟩ := signal
    exact ⟨{
      response := response
      positive := positive
      destination := destination
      order := order
      margin := margin
      margin_pos := margin_pos
      quotient_oriented_pos := quotient_pos
      signal := by
        simpa only [baseline, source, forward] using evidence }⟩

omit [DecidableEq G.State] in
/-- Strengthened high-order alternative.  The common quotient correction is
forced harmonic by adjoining all endpoint baseline occupation equations.
Consequently its quotients are genuine bounded state-account increments.
If these extra equations are incompatible, one actual action of the fixed
player carries a public oriented transition signal. -/
theorem
    exists_harmonicInvisibleQuotientCorrection_or_ownedTransitionSignal
    (jet : germ.LowerValueJet)
    (who : ι)
    [Nonempty (germ.InvisibleNeutralAction who)]
    (family : jet.InvisibleNeutralQuotientFamily who) :
    Nonempty (jet.HarmonicInvisibleQuotientCorrection who family) ∨
      Nonempty (jet.OwnedInvisibleTransitionSignal who family) := by
  classical
  let Response := germ.InvisibleNeutralAction who
  let Index := G.State ⊕ Response
  let delta : Index → G.State → ℝ
    | .inl source => fun destination =>
        germ.rawStateKernelCurve 0 source destination -
          if destination = source then 1 else 0
    | .inr response =>
        endpointResponseDifference
          (fun source t destination =>
            germ.rawStateKernelCurve t source destination)
          (fun action : Response => action.source)
          (fun action t destination =>
            germ.rawPureDeviationStateKernelCurve
              t action.source who action.1.2 destination)
          response
  let level : Index → ℝ
    | .inl _ => 0
    | .inr response => family.quotient response 0
  rcases exists_potential_or_signed_incompatibility delta level with
      compatible | incompatible
  · left
    obtain ⟨potential, represents⟩ := compatible
    have harmonic :
        ∀ source,
          expect
              (G.finkStateKernel germ.endpointFinkPoint source)
              potential =
            potential source := by
      intro source
      have represented := represents (Sum.inl source)
      change
        dotProduct
            (fun destination =>
              germ.rawStateKernelCurve 0 source destination -
                if destination = source then 1 else 0)
            potential =
          0 at represented
      rw [Math.Probability.expect_eq_sum]
      calc
        (∑ destination,
            (G.finkStateKernel
              germ.endpointFinkPoint source destination).toReal *
                potential destination) =
            ∑ destination,
              germ.rawStateKernelCurve 0 source destination *
                potential destination := by
          apply Finset.sum_congr rfl
          intro destination _
          rw [germ.rawStateKernelCurve_zero_eq_finkStateKernel]
        _ = potential source := by
          unfold dotProduct at represented
          simp only [sub_mul, Finset.sum_sub_distrib] at represented
          have point_mass :
              (∑ destination,
                (if destination = source then 1 else 0) *
                  potential destination) =
                potential source := by simp
          rw [point_mass] at represented
          linarith
    have quotient_eq :
        ∀ response : Response,
          family.quotient response 0 =
            G.finkContinuationGain
              (G.finkPlayerPotential who potential)
              germ.endpointFinkPoint
              response.source who response.1.2 := by
      intro response
      have represented := represents (Sum.inr response)
      change
        dotProduct
            (endpointResponseDifference
              (fun source t destination =>
                germ.rawStateKernelCurve t source destination)
              (fun action : Response => action.source)
              (fun action t destination =>
                germ.rawPureDeviationStateKernelCurve
                  t action.source who action.1.2 destination)
              response)
            potential =
          family.quotient response 0 at represented
      rw [
        endpointResponseDifference_dotProduct_eq_finkContinuationGain
          who response potential] at represented
      exact represented.symm
    refine ⟨{
      potential := potential
      harmonic := harmonic
      quotient_eq := quotient_eq
      quotient_eq_expectedAccountIncrement := ?_
      corrected_gain_nonpos := ?_ }⟩
    · intro response
      rw [quotient_eq response]
      rw [G.finkContinuationGain_playerPotential_self]
      rw [harmonic response.source, expect_sub, expect_const]
      rfl
    · intro response
      rw [G.finkContinuationGain_add]
      have coefficient_nonpos :=
        jet.quotient_add_leadingContinuationGain_nonpos
          response.source who response.1.2
          (family.quotient response)
          (family.analytic response)
          (family.factorization response)
      rw [← quotient_eq response]
      linarith
  · right
    obtain ⟨coefficient, _balance, total_ne⟩ := incompatible
    let rawTotal : ℝ :=
      ∑ response : Response,
        coefficient (Sum.inr response) *
          family.quotient response 0
    have rawTotal_ne : rawTotal ≠ 0 := by
      have total_eq :
          (∑ index : Index,
              coefficient index * level index) =
            rawTotal := by
        rw [Fintype.sum_sum_type]
        simp [level, rawTotal]
      exact fun raw_zero =>
        total_ne (total_eq.trans raw_zero)
    let signedCoefficient : Response → ℝ :=
      if 0 < rawTotal then
        fun response => coefficient (Sum.inr response)
      else
        fun response => -coefficient (Sum.inr response)
    let total : ℝ :=
      ∑ response : Response,
        signedCoefficient response *
          family.quotient response 0
    have total_pos : 0 < total := by
      by_cases raw_pos : 0 < rawTotal
      · simp [total, signedCoefficient, raw_pos, rawTotal]
      · have raw_neg : rawTotal < 0 :=
          lt_of_le_of_ne (le_of_not_gt raw_pos) rawTotal_ne
        have neg_pos : 0 < -rawTotal := neg_pos.mpr raw_neg
        simpa [total, signedCoefficient, raw_pos, rawTotal,
          ← Finset.sum_neg_distrib] using neg_pos
    let baseline : G.State → ℝ → G.State → ℝ :=
      fun source t destination =>
        germ.rawStateKernelCurve t source destination
    let source : Response → G.State :=
      fun response => response.source
    let forward : Response → ℝ → G.State → ℝ :=
      fun response t destination =>
        germ.rawPureDeviationStateKernelCurve
          t response.source who response.1.2 destination
    let weight : Response → ℝ → ℝ :=
      fun response _ => signedCoefficient response
    let charge : Response → ℝ → ℝ :=
      fun response _ => family.quotient response 0
    have baseline_analytic :
        ∀ state destination,
          AnalyticAt ℝ
            (fun t => baseline state t destination) 0 := by
      intro state destination
      exact
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve state) destination)
    have forward_analytic :
        ∀ response destination,
          AnalyticAt ℝ
            (fun t => forward response t destination) 0 := by
      intro response destination
      exact
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStateKernelCurve
                response.source) who) response.1.2) destination)
    have mass_eq :
        ∀ response,
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            ∑ destination, forward response t destination =
              ∑ destination,
                baseline (source response) t destination := by
      intro response
      exact eventually_sum_rawInvisibleKernel_eq germ who response
    have weight_analytic :
        ∀ response, AnalyticAt ℝ (weight response) 0 :=
      fun _ => analyticAt_const
    have charge_analytic :
        ∀ response, AnalyticAt ℝ (charge response) 0 :=
      fun _ => analyticAt_const
    have total_signal :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          total * t ^ (0 : ℕ) ≤
            ∑ response,
              weight response t * charge response t := by
      simp [total, weight, charge]
    obtain ⟨response, positive, _factorOrder, factorMargin,
        factorMargin_pos, extraction, transition⟩ :=
      exists_fixed_oriented_analytic_stochastic_response_curve
        baseline source forward weight charge
        baseline_analytic forward_analytic mass_eq
        weight_analytic charge_analytic total_pos total_signal
    have quotient_oriented_pos :
        0 <
          responseOrientation positive *
            family.quotient response 0 := by
      obtain ⟨t, ht, t_pos⟩ :=
        (extraction.and self_mem_nhdsWithin).exists
      have lower_pos :
          0 < factorMargin * t ^ _factorOrder :=
        mul_pos factorMargin_pos
          (pow_pos (mem_Ioi.mp t_pos) _factorOrder)
      exact lower_pos.trans_le (by
        simpa only [charge] using ht.2.2)
    rcases transition with transition_same | transition_signal
    · have drift_zero :
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            endpointPureDeviationDriftCurve germ
                response.source who response.1.2 t =
              0 := by
        filter_upwards [transition_same] with t same
        unfold endpointPureDeviationDriftCurve
          rawPureDeviationContinuationGainCurve
        apply Finset.sum_eq_zero
        intro destination _
        have same' :
            germ.rawPureDeviationStateKernelCurve
                t response.source who response.1.2 destination =
              germ.rawStateKernelCurve
                t response.source destination := by
          simpa only [forward, baseline, source] using same destination
        rw [same', sub_self, zero_mul]
      have quotient_zero :
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            family.quotient response t = 0 := by
        filter_upwards [
            family.factorization response |>
              Filter.Eventually.filter_mono nhdsWithin_le_nhds,
            drift_zero, self_mem_nhdsWithin] with
            t factorization drift_eq t_pos
        rw [drift_eq] at factorization
        exact
          (mul_eq_zero.mp factorization.symm).resolve_left
            (pow_ne_zero _ (ne_of_gt (mem_Ioi.mp t_pos)))
      have quotient_at_zero :
          family.quotient response 0 = 0 := by
        have quotient_limit :
            Tendsto (family.quotient response)
              (nhdsWithin 0 (Ioi 0))
              (nhds (family.quotient response 0)) :=
          (family.analytic response).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds
        have zero_limit :
            Tendsto (family.quotient response)
              (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
          tendsto_const_nhds.congr'
            (quotient_zero.mono fun _ h => h.symm)
        exact tendsto_nhds_unique quotient_limit zero_limit
      rw [quotient_at_zero, mul_zero] at quotient_oriented_pos
      exact False.elim (lt_irrefl 0 quotient_oriented_pos)
    · obtain ⟨destination, order, margin, margin_pos, signal⟩ :=
        transition_signal
      exact ⟨{
        response := response
        positive := positive
        destination := destination
        order := order
        margin := margin
        margin_pos := margin_pos
        quotient_oriented_pos := quotient_oriented_pos
        signal := by
          simpa only [baseline, source, forward] using signal }⟩

omit [DecidableEq G.State] in
/-- Complete processed endpoint alternative for the finite invisible-action
family of one player.

There is no simultaneous high-order hypothesis: either one owned action has
a lower-order endpoint-value signal, or finite choice assembles all
high-order quotients and the harmonic-account/oriented-signal alternative
applies. -/
theorem
    exists_ownedLowOrderDrift_or_quotientResponse
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι)
    [Nonempty (germ.InvisibleNeutralAction who)] :
    Nonempty (jet.OwnedInvisibleLowOrderDrift who) ∨
      ∃ family : jet.InvisibleNeutralQuotientFamily who,
        Nonempty (jet.HarmonicInvisibleQuotientCorrection who family) ∨
          Nonempty (jet.OwnedInvisibleTransitionSignal who family) := by
  classical
  by_cases low_order :
      Nonempty (jet.OwnedInvisibleLowOrderDrift who)
  · exact Or.inl low_order
  · right
    have high_order :
        ∀ response : germ.InvisibleNeutralAction who,
          ∃ quotient : ℝ → ℝ,
            AnalyticAt ℝ quotient 0 ∧
            (∀ᶠ t in 𝓝 (0 : ℝ),
              endpointPureDeviationDriftCurve germ
                  response.source who response.1.2 t =
                t ^ jet.order * quotient t) := by
      intro response
      rcases
          jet.lowOrderEndpointDrift_or_quotientAccount_of_processed
            span processed response.source who response.1.2
            response.property.1 with
        lower | higher
      · exfalso
        apply low_order
        obtain ⟨order, factor, margin, order_pos, order_lt,
          factor_analytic, factor_neg, margin_pos,
          factorization, signal⟩ := lower
        exact ⟨{
          response := response
          order := order
          factor := factor
          margin := margin
          order_pos := order_pos
          order_lt_jet := order_lt
          factor_analytic := factor_analytic
          factor_zero_neg := factor_neg
          margin_pos := margin_pos
          factorization := factorization
          signal := signal }⟩
      · obtain ⟨quotient, analytic, factorization, _account⟩ := higher
        exact ⟨quotient, analytic, factorization⟩
    choose quotient analytic factorization using high_order
    let family : jet.InvisibleNeutralQuotientFamily who := {
      quotient := quotient
      analytic := analytic
      factorization := factorization }
    exact ⟨family,
      jet.exists_harmonicInvisibleQuotientCorrection_or_ownedTransitionSignal
        who family⟩

end LowerValueJet
end AnalyticBellmanGerm

namespace InvisibleQuotientCorrectionAccountCounterexample

open Math.Probability

/-- The smallest state space on which comparison-versus-baseline drift can
differ from the actual state-account increment. -/
def potential (state : Bool) : ℝ :=
  if state then 1 else 0

/-- The endpoint baseline moves from `false` to `true`. -/
def baseline : PMF Bool := PMF.pure true

/-- The comparison instead stays at `false`. -/
def comparison : PMF Bool := PMF.pure false

/-- The compatibility pairing represents the quotient `-1`. -/
theorem comparison_sub_baseline_eq_neg_one :
    expect comparison potential - expect baseline potential = -1 := by
  simp [comparison, baseline, potential]

/-- Along the actual comparison transition the state-potential account does
not move. -/
theorem comparison_accountIncrement_eq_zero :
    expect comparison
        (fun successor => potential successor - potential false) =
      0 := by
  simp [comparison, potential]

/-- The missing term is exactly the nonzero endpoint-baseline residual. -/
theorem baseline_residual_eq_one :
    expect baseline potential - potential false = 1 := by
  simp [baseline, potential]

/-- Therefore representing a quotient by an endpoint transition difference
does not by itself realize that quotient as a bounded state-account
increment.  Endpoint harmonicity, a Poisson correction, or an independent
budget for the baseline residual is necessary. -/
theorem representedQuotient_ne_accountIncrement :
    expect comparison potential - expect baseline potential ≠
      expect comparison
        (fun successor => potential successor - potential false) := by
  rw [comparison_sub_baseline_eq_neg_one,
    comparison_accountIncrement_eq_zero]
  norm_num

end InvisibleQuotientCorrectionAccountCounterexample

end StochasticGame
end GameTheory
