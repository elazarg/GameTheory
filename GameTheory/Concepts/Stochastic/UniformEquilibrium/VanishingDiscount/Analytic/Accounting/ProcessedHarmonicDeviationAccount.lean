/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticHarmonicAdjustmentClosure
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicStateAccount
import Math.InvisibleNeutralActionDrift

/-!
# Deviation charges carried by a processed harmonic state account

For an already-processed lower value jet, the continuation gain of an
actual pure deviation against the leading jet is exactly the conditional
mean of the corresponding bounded state-account increment.  This uses the
same state potential, with no coefficient change.

The discounted Bellman equation also shows the precise boundary of this
identification.  If the endpoint-value transition drift of a pure deviation
is divisible by the lower-jet scale, its quotient survives at the endpoint:

`quotient(0) + leading-jet continuation gain ≤ 0`.

Thus the genuine action-specific leading coefficient is the sum of the
bounded-account drift and an independent moving-kernel quotient.  Processed
span membership pays the former but does not make the latter vanish.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Filter Math.Probability Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- The endpoint-value transition drift of one actual pure deviation along
the moving Bellman profile. -/
def endpointPureDeviationDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι) (action : G.Act who) :
    ℝ → ℝ :=
  fun t =>
    germ.rawPureDeviationContinuationGainCurve
      germ.endpointValue t source who action

/-- The transition gain of a lower jet's moving analytic factor. -/
def pureDeviationLowerFactorCurve
    (jet : germ.LowerValueJet)
    (source : G.State) (who : ι) (action : G.Act who) :
    ℝ → ℝ :=
  fun t =>
    germ.rawMovingPureDeviationContinuationGainCurve
      jet.factor t source who action

omit [DecidableEq G.State] in
/-- A lower value jet has strictly positive order.  Order zero would make
its nonzero leading factor equal the zero value increment at the endpoint.
-/
theorem order_pos (jet : germ.LowerValueJet) :
    0 < jet.order := by
  by_contra order_not_pos
  have order_zero : jet.order = 0 :=
    Nat.eq_zero_of_not_pos order_not_pos
  have factor_at_zero := jet.valueIncrement_eq.self_of_nhds
  have factor_zero : jet.factor 0 = 0 := by
    simpa [germ.valueIncrement_zero, order_zero] using factor_at_zero.symm
  exact jet.leading_ne_zero factor_zero

omit [DecidableEq G.State] in
/-- The continuation gain of a processed harmonic jet against one actual
pure deviation is exactly the expected increment of its state account.
The potential in the strategic gain and in the realized account is
literally the same function. -/
theorem
    finkContinuationGain_eq_expect_endpointCoordinateIncrement_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (source : G.State) (who : ι) (action : G.Act who) :
    G.finkContinuationGain (jet.factor 0)
        germ.endpointFinkPoint source who action =
      expect
        (G.finkPureDeviationStateKernel
          germ.endpointFinkPoint source who action)
        (fun successor =>
          jet.endpointCoordinatePotential who successor -
            jet.endpointCoordinatePotential who source) := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  change
    expect
          (G.finkPureDeviationStateKernel
            germ.endpointFinkPoint source who action)
          (jet.endpointCoordinatePotential who) -
        expect
          (G.finkStateKernel germ.endpointFinkPoint source)
          (jet.endpointCoordinatePotential who) =
      expect
        (G.finkPureDeviationStateKernel
          germ.endpointFinkPoint source who action)
        (fun successor =>
          jet.endpointCoordinatePotential who successor -
            jet.endpointCoordinatePotential who source)
  rw [expect_sub, expect_const]
  rw [jet.endpointCoordinatePotential_harmonic_of_processed
    span processed who source]

omit [DecidableEq G.State] in
/-- Raw discounted Bellman inequality for one actual pure deviation. -/
theorem rawDiscountedPureDeviationGain_nonpos
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (action : G.Act who) :
    t ^ germ.ramification *
          germ.rawPureDeviationStageGainCurve
            t source who action +
        (1 - t ^ germ.ramification) *
          germ.rawMovingPureDeviationContinuationGainCurve
            germ.valueCurve t source who action ≤
      0 := by
  have bellman :=
    (germ.isDiscountedStationaryBellmanEq_finkPointAt ht).1
      source who (PMF.pure action)
  have gain_nonpos :
      G.finkGain (1 - t ^ germ.ramification)
          (germ.finkPointAt ht) source who action ≤ 0 := by
    rw [finkGain]
    rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
      G.finkAuxEU_eq_discountedAuxEU]
    exact sub_nonpos.mpr bellman
  rw [G.finkGain_eq_stage_add_continuation] at gain_nonpos
  rw [germ.finkValue_finkPointAt ht] at gain_nonpos
  rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
  rw [germ.rawMovingPureDeviationContinuationGainCurve_eq_finkPointAt
    germ.valueCurve ht]
  simpa only [sub_sub_cancel, valueCurve] using gain_nonpos

omit [DecidableEq G.State] in
/-- At a parameter where the lower-jet factorization holds, the moving-value
continuation gain splits into the endpoint-value drift and the lower-factor
gain with exactly the jet power. -/
theorem rawMovingValueGain_eq_endpoint_add_lowerFactor
    (jet : germ.LowerValueJet)
    {t : ℝ}
    (factorization :
      germ.valueIncrement t = t ^ jet.order • jet.factor t)
    (source : G.State) (who : ι) (action : G.Act who) :
    germ.rawMovingPureDeviationContinuationGainCurve
        germ.valueCurve t source who action =
      endpointPureDeviationDriftCurve germ source who action t +
        t ^ jet.order *
          jet.pureDeviationLowerFactorCurve source who action t := by
  have value_eq :
      germ.valueCurve t =
        germ.endpointValue + t ^ jet.order • jet.factor t := by
    rw [valueIncrement] at factorization
    ext state player
    have coordinate :=
      congrFun (congrFun factorization state) player
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at coordinate
    change
      germ.valueCurve t state player =
        germ.endpointValue state player +
          t ^ jet.order * jet.factor t state player
    linarith
  unfold endpointPureDeviationDriftCurve
    pureDeviationLowerFactorCurve
    rawMovingPureDeviationContinuationGainCurve
    rawPureDeviationContinuationGainCurve
  rw [value_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro state _
  ring

omit [DecidableEq G.State] in
/-- The endpoint-value drift and lower-factor gain are analytic scalar
germs. -/
theorem analytic_endpointPureDeviationDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι) (action : G.Act who) :
    AnalyticAt ℝ
      (endpointPureDeviationDriftCurve germ source who action) 0 := by
  have source_analytic :=
    (analyticAt_pi_iff.mp
      (germ.analytic_rawPureDeviationContinuationGainCurve
        germ.endpointValue)) source
  have player_analytic :=
    (analyticAt_pi_iff.mp source_analytic) who
  exact (analyticAt_pi_iff.mp player_analytic) action

omit [DecidableEq G.State] in
theorem analytic_pureDeviationLowerFactorCurve
    (jet : germ.LowerValueJet)
    (source : G.State) (who : ι) (action : G.Act who) :
    AnalyticAt ℝ
      (jet.pureDeviationLowerFactorCurve source who action) 0 := by
  have source_analytic :=
    (analyticAt_pi_iff.mp
      (germ.analytic_rawMovingPureDeviationContinuationGainCurve
        jet.factor jet.analytic_factor)) source
  have player_analytic :=
    (analyticAt_pi_iff.mp source_analytic) who
  exact (analyticAt_pi_iff.mp player_analytic) action

omit [DecidableEq G.State] in
/-- Exact high-order endpoint equation for a lower value jet.

If the endpoint-value transition drift is divisible by the lower-jet
power, the quotient does not disappear: it adds to the action-specific
continuation gain of the leading jet.  The discounted stage term is of
higher order because `jet.order < germ.ramification`. -/
theorem quotient_add_leadingContinuationGain_nonpos
    (jet : germ.LowerValueJet)
    (source : G.State) (who : ι) (action : G.Act who)
    (quotient : ℝ → ℝ)
    (quotient_analytic : AnalyticAt ℝ quotient 0)
    (drift_factorization :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        endpointPureDeviationDriftCurve germ source who action t =
          t ^ jet.order * quotient t) :
    quotient 0 +
        G.finkContinuationGain (jet.factor 0)
          germ.endpointFinkPoint source who action ≤
      0 := by
  let normalized : ℝ → ℝ := fun t =>
    t ^ (germ.ramification - jet.order) *
          germ.rawPureDeviationStageGainCurve t source who action +
      (1 - t ^ germ.ramification) *
        (quotient t +
          jet.pureDeviationLowerFactorCurve source who action t)
  have normalized_analytic : AnalyticAt ℝ normalized 0 := by
    have stage_analytic :
        AnalyticAt ℝ
          (fun t =>
            germ.rawPureDeviationStageGainCurve
              t source who action) 0 :=
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve source) who)
        action)
    exact
      ((analyticAt_id.pow
          (germ.ramification - jet.order)).mul stage_analytic).add
        ((analyticAt_const.sub
          (analyticAt_id.pow germ.ramification)).mul
            (quotient_analytic.add
              (jet.analytic_pureDeviationLowerFactorCurve
                source who action)))
  have normalized_nonpos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), normalized t ≤ 0 := by
    filter_upwards
        [Ioo_mem_nhdsGT germ.radius_pos,
          jet.valueIncrement_eq.filter_mono nhdsWithin_le_nhds,
          drift_factorization.filter_mono nhdsWithin_le_nhds] with
        t ht factorization drift_eq
    have raw_nonpos :=
      rawDiscountedPureDeviationGain_nonpos germ
        ht source who action
    rw [jet.rawMovingValueGain_eq_endpoint_add_lowerFactor
      factorization source who action, drift_eq] at raw_nonpos
    have power_split :
        t ^ germ.ramification =
          t ^ jet.order *
            t ^ (germ.ramification - jet.order) := by
      rw [← pow_add, Nat.add_sub_of_le
        (Nat.le_of_lt jet.order_lt_ramification)]
    have scaled :
        t ^ jet.order * normalized t =
          t ^ germ.ramification *
                germ.rawPureDeviationStageGainCurve
                  t source who action +
            (1 - t ^ germ.ramification) *
              (t ^ jet.order * quotient t +
                t ^ jet.order *
                  jet.pureDeviationLowerFactorCurve
                    source who action t) := by
      dsimp only [normalized]
      rw [power_split]
      ring
    have power_pos : 0 < t ^ jet.order :=
      pow_pos ht.1 jet.order
    have scaled_nonpos : t ^ jet.order * normalized t ≤ 0 :=
      scaled.trans_le raw_nonpos
    nlinarith
  have normalized_limit :
      Tendsto normalized (𝓝[>] (0 : ℝ))
        (𝓝 (normalized 0)) :=
    normalized_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have normalized_zero_nonpos : normalized 0 ≤ 0 :=
    le_of_tendsto normalized_limit normalized_nonpos
  have exponent_pos :
      0 < germ.ramification - jet.order :=
    Nat.sub_pos_of_lt jet.order_lt_ramification
  have factor_zero :
      jet.pureDeviationLowerFactorCurve
          source who action 0 =
        G.finkContinuationGain (jet.factor 0)
          germ.endpointFinkPoint source who action := by
    exact
      germ.rawMovingPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
        jet.factor source who action
  have normalized_zero :
      normalized 0 =
        quotient 0 +
          G.finkContinuationGain (jet.factor 0)
            germ.endpointFinkPoint source who action := by
    simp [normalized, exponent_pos.ne',
      germ.ramification_pos.ne', factor_zero]
  rwa [normalized_zero] at normalized_zero_nonpos

omit [DecidableEq G.State] in
/-- Processed-branch form of the coefficient equation.  The second summand
is exactly the conditional mean of the bounded endpoint-coordinate account
increment, while the quotient remains as a separate term. -/
theorem quotient_add_expectedAccountIncrement_nonpos_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (source : G.State) (who : ι) (action : G.Act who)
    (quotient : ℝ → ℝ)
    (quotient_analytic : AnalyticAt ℝ quotient 0)
    (drift_factorization :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        endpointPureDeviationDriftCurve germ source who action t =
          t ^ jet.order * quotient t) :
    quotient 0 +
        expect
          (G.finkPureDeviationStateKernel
            germ.endpointFinkPoint source who action)
          (fun successor =>
            jet.endpointCoordinatePotential who successor -
              jet.endpointCoordinatePotential who source) ≤
      0 := by
  rw [←
    jet.finkContinuationGain_eq_expect_endpointCoordinateIncrement_of_processed
      span processed source who action]
  exact
    jet.quotient_add_leadingContinuationGain_nonpos
      source who action quotient quotient_analytic drift_factorization

omit [DecidableEq G.State] in
/-- Sharp action-specific order alternative in the processed branch.

For an endpoint-continuation-neutral pure deviation, either the endpoint
value already supplies a negative transition drift strictly below the lower
jet's order, or that drift is divisible by the lower-jet power.  In the
second branch its quotient remains next to the expected bounded-account
increment in the endpoint Bellman inequality.
-/
theorem
    lowOrderEndpointDrift_or_quotientAccount_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (source : G.State) (who : ι) (action : G.Act who)
    (endpoint_neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0) :
    (∃ (order : ℕ) (factor : ℝ → ℝ) (margin : ℝ),
        0 < order ∧
        order < jet.order ∧
        AnalyticAt ℝ factor 0 ∧
        factor 0 < 0 ∧
        0 < margin ∧
        (∀ᶠ t in 𝓝 (0 : ℝ),
          endpointPureDeviationDriftCurve germ source who action t =
            t ^ order * factor t) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          margin * t ^ order ≤
            -endpointPureDeviationDriftCurve
              germ source who action t) ∨
      ∃ quotient : ℝ → ℝ,
        AnalyticAt ℝ quotient 0 ∧
        (∀ᶠ t in 𝓝 (0 : ℝ),
          endpointPureDeviationDriftCurve germ source who action t =
            t ^ jet.order * quotient t) ∧
        quotient 0 +
            expect
              (G.finkPureDeviationStateKernel
                germ.endpointFinkPoint source who action)
              (fun successor =>
                jet.endpointCoordinatePotential who successor -
                  jet.endpointCoordinatePotential who source) ≤
          0 := by
  let drift :=
    endpointPureDeviationDriftCurve germ source who action
  have drift_analytic : AnalyticAt ℝ drift 0 :=
    analytic_endpointPureDeviationDriftCurve
      germ source who action
  have drift_zero : drift 0 = 0 := by
    change
      germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue 0 source who action = 0
    rw [
      germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint]
    exact endpoint_neutral
  by_cases order_top : analyticOrderAt drift 0 = ⊤
  · right
    have order_ge :
        (jet.order : ℕ∞) ≤ analyticOrderAt drift 0 := by
      simp [order_top]
    obtain ⟨quotient, quotient_analytic, factorization⟩ :=
      (natCast_le_analyticOrderAt drift_analytic).mp order_ge
    refine ⟨quotient, quotient_analytic, ?_, ?_⟩
    · simpa only [drift, sub_zero, smul_eq_mul] using factorization
    · apply
        jet.quotient_add_expectedAccountIncrement_nonpos_of_processed
          span processed source who action quotient quotient_analytic
      simpa only [drift, sub_zero, smul_eq_mul] using factorization
  · let order := analyticOrderNatAt drift 0
    have order_eq :
        analyticOrderAt drift 0 = (order : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt order_top).symm
    by_cases order_lt : order < jet.order
    · left
      obtain ⟨factor, factor_analytic, factor_ne, factorization⟩ :=
        drift_analytic.analyticOrderAt_eq_natCast.mp order_eq
      have order_pos : 0 < order := by
        by_contra order_not_pos
        have order_zero : order = 0 :=
          Nat.eq_zero_of_not_pos order_not_pos
        have factor_at_zero := factorization.self_of_nhds
        have factor_zero : factor 0 = 0 := by
          simpa [drift_zero, order_zero] using factor_at_zero.symm
        exact factor_ne factor_zero
      let normalized : ℝ → ℝ := fun t =>
        t ^ (germ.ramification - order) *
              germ.rawPureDeviationStageGainCurve
                t source who action +
          (1 - t ^ germ.ramification) *
            (factor t +
              t ^ (jet.order - order) *
                jet.pureDeviationLowerFactorCurve
                  source who action t)
      have normalized_analytic : AnalyticAt ℝ normalized 0 := by
        have stage_analytic :
            AnalyticAt ℝ
              (fun t =>
                germ.rawPureDeviationStageGainCurve
                  t source who action) 0 :=
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStageGainCurve source) who)
            action)
        exact
          ((analyticAt_id.pow
              (germ.ramification - order)).mul stage_analytic).add
            ((analyticAt_const.sub
              (analyticAt_id.pow germ.ramification)).mul
                (factor_analytic.add
                  ((analyticAt_id.pow
                    (jet.order - order)).mul
                      (jet.analytic_pureDeviationLowerFactorCurve
                        source who action))))
      have normalized_nonpos :
          ∀ᶠ t in 𝓝[>] (0 : ℝ), normalized t ≤ 0 := by
        filter_upwards
            [Ioo_mem_nhdsGT germ.radius_pos,
              jet.valueIncrement_eq.filter_mono nhdsWithin_le_nhds,
              factorization.filter_mono nhdsWithin_le_nhds] with
            t ht value_factorization drift_factorization
        have raw_nonpos :=
          rawDiscountedPureDeviationGain_nonpos germ
            ht source who action
        rw [jet.rawMovingValueGain_eq_endpoint_add_lowerFactor
          value_factorization source who action] at raw_nonpos
        have drift_factorization' :
            endpointPureDeviationDriftCurve
                germ source who action t =
              t ^ order * factor t := by
          simpa only [drift, sub_zero, smul_eq_mul] using
            drift_factorization
        rw [drift_factorization'] at raw_nonpos
        have ramification_split :
            t ^ germ.ramification =
              t ^ order *
                t ^ (germ.ramification - order) := by
          rw [← pow_add, Nat.add_sub_of_le
            (order_lt.trans jet.order_lt_ramification).le]
        have jet_order_split :
            t ^ jet.order =
              t ^ order * t ^ (jet.order - order) := by
          rw [← pow_add, Nat.add_sub_of_le order_lt.le]
        have scaled :
            t ^ order * normalized t =
              t ^ germ.ramification *
                    germ.rawPureDeviationStageGainCurve
                      t source who action +
                (1 - t ^ germ.ramification) *
                  (t ^ order * factor t +
                    t ^ jet.order *
                      jet.pureDeviationLowerFactorCurve
                        source who action t) := by
          dsimp only [normalized]
          rw [ramification_split, jet_order_split]
          ring
        have scaled_nonpos :
            t ^ order * normalized t ≤ 0 :=
          scaled.trans_le raw_nonpos
        nlinarith [pow_pos ht.1 order]
      have normalized_limit :
          Tendsto normalized (𝓝[>] (0 : ℝ))
            (𝓝 (normalized 0)) :=
        normalized_analytic.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have normalized_zero_nonpos : normalized 0 ≤ 0 :=
        le_of_tendsto normalized_limit normalized_nonpos
      have ramification_sub_pos :
          0 < germ.ramification - order :=
        Nat.sub_pos_of_lt
          (order_lt.trans jet.order_lt_ramification)
      have jet_order_sub_pos : 0 < jet.order - order :=
        Nat.sub_pos_of_lt order_lt
      have factor_neg : factor 0 < 0 := by
        have normalized_zero : normalized 0 = factor 0 := by
          simp [normalized, ramification_sub_pos.ne',
            germ.ramification_pos.ne', jet_order_sub_pos.ne']
        rw [normalized_zero] at normalized_zero_nonpos
        exact lt_of_le_of_ne normalized_zero_nonpos factor_ne
      let margin : ℝ := -factor 0 / 2
      have margin_pos : 0 < margin := by
        dsimp only [margin]
        linarith
      have factor_upper :
          ∀ᶠ t in 𝓝 (0 : ℝ), factor t < factor 0 / 2 :=
        factor_analytic.continuousAt.tendsto.eventually_lt_const
          (by linarith)
      have power_charge :
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            margin * t ^ order ≤ -drift t := by
        filter_upwards
            [factorization.filter_mono nhdsWithin_le_nhds,
              factor_upper.filter_mono nhdsWithin_le_nhds,
              self_mem_nhdsWithin] with
            t factorization_at factor_upper_at t_pos
        simp only [sub_zero, smul_eq_mul] at factorization_at
        have power_nonneg : 0 ≤ t ^ order :=
          (pow_pos t_pos order).le
        calc
          margin * t ^ order ≤ (-factor t) * t ^ order := by
            apply mul_le_mul_of_nonneg_right _ power_nonneg
            dsimp only [margin]
            linarith
          _ = -drift t := by rw [factorization_at]; ring
      exact ⟨order, factor, margin, order_pos, order_lt,
        factor_analytic, factor_neg, margin_pos,
        by simpa only [drift, sub_zero, smul_eq_mul] using factorization,
        by simpa only [drift] using power_charge⟩
    · right
      have order_ge : jet.order ≤ order :=
        Nat.le_of_not_gt order_lt
      have analytic_order_ge :
          (jet.order : ℕ∞) ≤ analyticOrderAt drift 0 := by
        rw [order_eq]
        exact_mod_cast order_ge
      obtain ⟨quotient, quotient_analytic, factorization⟩ :=
        (natCast_le_analyticOrderAt drift_analytic).mp analytic_order_ge
      refine ⟨quotient, quotient_analytic, ?_, ?_⟩
      · simpa only [drift, sub_zero, smul_eq_mul] using factorization
      · apply
          jet.quotient_add_expectedAccountIncrement_nonpos_of_processed
            span processed source who action quotient quotient_analytic
        simpa only [drift, sub_zero, smul_eq_mul] using factorization

end LowerValueJet
end AnalyticBellmanGerm

namespace ProcessedHarmonicDeviationRemainderCounterexample

open Math Math.Probability

/-- A two-state analytic baseline law. -/
def baseline (_t : ℝ) (_state : Bool) : ℝ := 1 / 2

/-- A moving comparison law with a first-order drift. -/
def comparison (t : ℝ) (state : Bool) : ℝ :=
  if state then 1 / 2 - t else 1 / 2 + t

/-- The endpoint value detects the moving comparison law. -/
def endpointValue (state : Bool) : ℝ :=
  if state then 1 else 0

/-- A nonzero harmonic leading coefficient whose state account is constant.
-/
def leading (_state : Bool) : ℝ := 1

/-- The independent first-order quotient of the endpoint-value drift. -/
def quotient (_t : ℝ) : ℝ := -1

theorem baseline_mass (t : ℝ) :
    ∑ state, baseline t state = 1 := by
  simp [baseline]

theorem comparison_mass (t : ℝ) :
    ∑ state, comparison t state = 1 := by
  simp [comparison]
  ring

/-- The endpoint-value drift has nonzero quotient `-1` at lower-jet order
one. -/
theorem endpointValue_drift (t : ℝ) :
    finiteStateTransitionDrift
        baseline comparison (fun _ => endpointValue) t =
      t ^ (1 : ℕ) * quotient t := by
  simp [finiteStateTransitionDrift, finiteStatePairing, baseline,
    comparison, endpointValue, quotient]

/-- The same comparison has zero drift against the nonzero constant
harmonic leading coefficient. -/
theorem leading_drift (t : ℝ) :
    finiteStateTransitionDrift
        baseline comparison (fun _ => leading) t = 0 := by
  change
    finiteStateTransitionDrift
        baseline comparison (fun _ _ => (1 : ℝ)) t = 0
  rw [finiteStateTransitionDrift_const baseline comparison 1 t
    (baseline_mass t) (comparison_mass t)]

/-- The discounted inequality with discount exponent two and lower-jet
order one holds while the quotient is nonzero and the leading account drift
is zero.  Thus no coefficient equation can delete the quotient merely from
harmonicity of the leading jet. -/
theorem discounted_lowerJet_inequality
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t ^ (2 : ℕ) * 0 +
        (1 - t ^ (2 : ℕ)) *
          (finiteStateTransitionDrift
              baseline comparison (fun _ => endpointValue) t +
            t ^ (1 : ℕ) *
              finiteStateTransitionDrift
                baseline comparison (fun _ => leading) t) ≤
      0 := by
  rw [endpointValue_drift, leading_drift]
  simp only [quotient, mul_neg, mul_one, mul_zero, pow_one, add_zero,
    zero_add]
  have power_le_one : t ^ (2 : ℕ) ≤ 1 :=
    pow_le_one₀ ht.1.le ht.2.le
  have product_nonneg :
      0 ≤ (1 - t ^ (2 : ℕ)) * t :=
    mul_nonneg (sub_nonneg.mpr power_le_one) ht.1.le
  nlinarith

/-- Every realized account built from the constant leading coefficient has
zero increment, despite the nonzero quotient. -/
theorem leading_accountIncrement_zero
    (path : ℕ → Bool) (time : ℕ) :
    statePotentialIncrement leading path time = 0 := by
  simp [statePotentialIncrement, leading]

theorem quotient_zero_ne_accountDrift :
    quotient 0 ≠
      finiteStateTransitionDrift
        baseline comparison (fun _ => leading) 0 := by
  rw [leading_drift]
  norm_num [quotient]

end ProcessedHarmonicDeviationRemainderCounterexample

end StochasticGame
end GameTheory
