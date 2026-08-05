/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ProcessedHarmonicResidualCalendar

/-!
# Universal-calendar control of moving corrected response gains

The endpoint harmonic correction controls a continuation gain computed with
the endpoint lower-value factor.  At a positive Bellman parameter, both the
pure-deviation kernels and that lower-value factor move.  This file records
the complete finite analytic remainder.

For each invisible response, the raw moving response gain is the sum of:

* the raw stage gain;
* the raw continuation gain against the moving corrected factor
  `jet.factor t + correction.potential`.

Its difference from the corresponding endpoint stage-plus-continuation gain
is analytic and vanishes at zero.  A finite absolute envelope therefore
vanishes along the universal calendar, and its expected cumulative cost is
sublinear for every history law and every predictable behavioral mixture.

There is an important exact boundary.  The correction slack controls only
the endpoint continuation gain.  If one compares the full moving response
gain directly with that slack, the endpoint stage gain remains as a constant
term.  It need not vanish for an invisible neutral action, whose defining
neutrality concerns the endpoint-value continuation gain.  Thus the calendar
discharges all moving analytic error, but cannot erase a nonzero endpoint
stage incentive.
-/

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

/-- Moving payoff factor obtained by adding the fixed harmonic correction
to the analytic lower-value factor. -/
def HarmonicInvisibleQuotientCorrection.movingCorrectedFactor
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) : G.State → Payoff ι :=
  jet.factor t + G.finkPlayerPotential who correction.potential

omit [DecidableEq G.State] in
/-- The moving corrected factor is analytic through the endpoint. -/
theorem
    HarmonicInvisibleQuotientCorrection.analytic_movingCorrectedFactor
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    AnalyticAt ℝ correction.movingCorrectedFactor 0 := by
  unfold movingCorrectedFactor
  exact jet.analytic_factor.add analyticAt_const

/-- Raw continuation gain against the moving corrected lower-value factor.
This includes the moving pure-deviation and prescribed transition kernels,
as well as the moving lower-value factor. -/
def
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedContinuationGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) : ℝ :=
  germ.rawMovingPureDeviationContinuationGainCurve
    correction.movingCorrectedFactor t
    response.source who response.1.2

/-- Full raw stage-plus-continuation response quantity at the moving
Bellman parameter. -/
def HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) : ℝ :=
  germ.rawPureDeviationStageGainCurve
      t response.source who response.1.2 +
    correction.rawMovingCorrectedContinuationGain t response

/-- Endpoint stage-plus-corrected-continuation reference value. -/
def HarmonicInvisibleQuotientCorrection.endpointCorrectedResponseGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) : ℝ :=
  G.finkStageGain germ.endpointFinkPoint
      response.source who response.1.2 +
    G.finkContinuationGain
      (jet.factor 0 +
        G.finkPlayerPotential who correction.potential)
      germ.endpointFinkPoint
      response.source who response.1.2

/-- Complete moving analytic remainder relative to the endpoint
stage-plus-continuation value. -/
def HarmonicInvisibleQuotientCorrection.rawMovingResponseGainRemainder
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) : ℝ :=
  correction.rawMovingCorrectedResponseGain t response -
    correction.endpointCorrectedResponseGain response

omit [DecidableEq G.State] in
/-- The moving corrected continuation gain is analytic. -/
theorem
    HarmonicInvisibleQuotientCorrection.analytic_rawMovingCorrectedContinuationGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    AnalyticAt ℝ
      (fun t =>
        correction.rawMovingCorrectedContinuationGain t response) 0 := by
  have analytic_all :=
    germ.analytic_rawMovingPureDeviationContinuationGainCurve
      correction.movingCorrectedFactor
      correction.analytic_movingCorrectedFactor
  exact
    analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp analytic_all response.source) who)
      response.1.2

omit [DecidableEq G.State] in
/-- The full moving response gain is analytic. -/
theorem
    HarmonicInvisibleQuotientCorrection.analytic_rawMovingCorrectedResponseGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    AnalyticAt ℝ
      (fun t =>
        correction.rawMovingCorrectedResponseGain t response) 0 := by
  unfold rawMovingCorrectedResponseGain
  have stage_analytic :=
    analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          germ.analytic_rawPureDeviationStageGainCurve
          response.source)
        who)
      response.1.2
  exact stage_analytic.add
    (correction.analytic_rawMovingCorrectedContinuationGain response)

omit [DecidableEq G.State] in
/-- The complete moving response-gain remainder is analytic. -/
theorem
    HarmonicInvisibleQuotientCorrection.analytic_rawMovingResponseGainRemainder
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    AnalyticAt ℝ
      (fun t =>
        correction.rawMovingResponseGainRemainder t response) 0 := by
  unfold rawMovingResponseGainRemainder
  exact
    (correction.analytic_rawMovingCorrectedResponseGain response).sub
      analyticAt_const

omit [DecidableEq G.State] in
/-- At a valid positive parameter, the raw continuation term is exactly
the semantic continuation gain against the moving corrected factor. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedContinuationGain_eq_at
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedContinuationGain t response =
      G.finkContinuationGain
        (correction.movingCorrectedFactor t)
        (germ.finkPointAt ht)
        response.source who response.1.2 := by
  unfold rawMovingCorrectedContinuationGain
  exact
    germ.rawMovingPureDeviationContinuationGainCurve_eq_finkPointAt
      correction.movingCorrectedFactor ht
      response.source who response.1.2

omit [DecidableEq G.State] in
/-- Semantic equality for the full raw stage-plus-continuation response
quantity on the positive germ interval. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_eq_at
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain t response =
      G.finkStageGain (germ.finkPointAt ht)
          response.source who response.1.2 +
        G.finkContinuationGain
          (correction.movingCorrectedFactor t)
          (germ.finkPointAt ht)
          response.source who response.1.2 := by
  unfold rawMovingCorrectedResponseGain
  rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
  rw [correction.rawMovingCorrectedContinuationGain_eq_at ht]

omit [DecidableEq G.State] in
/-- The moving corrected continuation gain specializes to its endpoint
semantic value. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedContinuationGain_zero
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedContinuationGain 0 response =
      G.finkContinuationGain
        (jet.factor 0 +
          G.finkPlayerPotential who correction.potential)
        germ.endpointFinkPoint
        response.source who response.1.2 := by
  unfold rawMovingCorrectedContinuationGain movingCorrectedFactor
  exact
    germ.rawMovingPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
      (fun t =>
        jet.factor t +
          G.finkPlayerPotential who correction.potential)
      response.source who response.1.2

omit [DecidableEq G.State] in
/-- The full raw moving gain has exactly the expected endpoint value. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_zero
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain 0 response =
      correction.endpointCorrectedResponseGain response := by
  unfold rawMovingCorrectedResponseGain endpointCorrectedResponseGain
  rw [germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint]
  rw [correction.rawMovingCorrectedContinuationGain_zero]

omit [DecidableEq G.State] in
/-- The complete moving stage/kernel/value remainder vanishes at zero. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingResponseGainRemainder_zero
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingResponseGainRemainder 0 response = 0 := by
  unfold rawMovingResponseGainRemainder
  rw [correction.rawMovingCorrectedResponseGain_zero, sub_self]

omit [DecidableEq G.State] in
/-- Exact decomposition into endpoint reference and vanishing moving
remainder. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_eq_endpoint_add_remainder
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain t response =
      correction.endpointCorrectedResponseGain response +
        correction.rawMovingResponseGainRemainder t response := by
  unfold rawMovingResponseGainRemainder
  ring

omit [DecidableEq G.State] in
/-- The endpoint response reference is the endpoint stage gain minus the
nonnegative harmonic-correction slack. -/
theorem
    HarmonicInvisibleQuotientCorrection.endpointCorrectedResponseGain_eq_stage_sub_slack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.endpointCorrectedResponseGain response =
      G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 -
        correction.slack response := by
  unfold endpointCorrectedResponseGain slack
  ring

omit [DecidableEq G.State] in
/-- Comparing the full response gain directly with continuation slack
leaves the endpoint stage gain.  This is the exact nonvanishing boundary. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_add_slack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain t response +
        correction.slack response =
      G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 +
        correction.rawMovingResponseGainRemainder t response := by
  rw [
    correction.rawMovingCorrectedResponseGain_eq_endpoint_add_remainder,
    correction.endpointCorrectedResponseGain_eq_stage_sub_slack]
  ring

omit [DecidableEq G.State] in
/-- At the endpoint, the excess over continuation slack is exactly the
stage gain; invisibility and continuation neutrality do not remove it. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_zero_add_slack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain 0 response +
        correction.slack response =
      G.finkStageGain germ.endpointFinkPoint
        response.source who response.1.2 := by
  rw [correction.rawMovingCorrectedResponseGain_add_slack]
  rw [correction.rawMovingResponseGainRemainder_zero, add_zero]

/-- Finite absolute envelope for the complete moving response-gain
remainder. -/
def HarmonicInvisibleQuotientCorrection.rawMovingResponseGainEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) : ℝ :=
  ∑ response : germ.InvisibleNeutralAction who,
    |correction.rawMovingResponseGainRemainder t response|

omit [DecidableEq G.State] in
/-- The finite complete-remainder envelope tends to zero. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_rawMovingResponseGainEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    Tendsto correction.rawMovingResponseGainEnvelope
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  unfold rawMovingResponseGainEnvelope
  have sum_tendsto :=
    tendsto_finsetSum (s := Finset.univ)
      (fun (response : germ.InvisibleNeutralAction who) _ => by
        have remainder_tendsto :
            Tendsto
              (fun t =>
                correction.rawMovingResponseGainRemainder
                  t response)
              (𝓝 (0 : ℝ)) (𝓝 0) := by
          have continuous :=
            (correction.analytic_rawMovingResponseGainRemainder
              response).continuousAt
          change
            Tendsto
              (fun t =>
                correction.rawMovingResponseGainRemainder
                  t response)
              (𝓝 (0 : ℝ))
              (𝓝
                (correction.rawMovingResponseGainRemainder
                  0 response)) at continuous
          rw [correction.rawMovingResponseGainRemainder_zero response]
            at continuous
          exact continuous
        simpa only [abs_zero] using remainder_tendsto.abs)
  simpa using sum_tendsto

omit [DecidableEq G.State] in
/-- The complete moving envelope vanishes along the universal calendar. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_calendarResponseGainEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    Tendsto
      (fun stage =>
        correction.rawMovingResponseGainEnvelope
          (residualCalendarScale stage))
      atTop (𝓝 0) :=
  correction.tendsto_rawMovingResponseGainEnvelope.comp
    tendsto_residualCalendarScale

/-- Expected one-stage absolute complete response-gain remainder under an
arbitrary history law and predictable behavioral response mixture. -/
def
    HarmonicInvisibleQuotientCorrection.calendarResponseGainStageBudget
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) : ℝ :=
  expect (historyLaw stage) fun history =>
    expect (selection stage history) fun response =>
      |correction.rawMovingResponseGainRemainder
        (residualCalendarScale stage) response|

omit [DecidableEq G.State] in
theorem
    HarmonicInvisibleQuotientCorrection.calendarResponseGainStageBudget_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    0 ≤ correction.calendarResponseGainStageBudget
      historyLaw selection stage := by
  unfold calendarResponseGainStageBudget
  apply expect_nonneg
  intro history
  exact expect_nonneg _ _ fun response => abs_nonneg _

omit [DecidableEq G.State] in
/-- The finite analytic envelope dominates every expected stage budget. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarResponseGainStageBudget_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    correction.calendarResponseGainStageBudget historyLaw selection stage ≤
      correction.rawMovingResponseGainEnvelope
        (residualCalendarScale stage) := by
  unfold calendarResponseGainStageBudget
  calc
    expect (historyLaw stage)
        (fun history =>
          expect (selection stage history)
            (fun response =>
              |correction.rawMovingResponseGainRemainder
                (residualCalendarScale stage) response|)) ≤
        expect (historyLaw stage)
          (fun _ =>
            correction.rawMovingResponseGainEnvelope
              (residualCalendarScale stage)) := by
          apply expect_mono
          intro history
          calc
            expect (selection stage history)
                (fun response =>
                  |correction.rawMovingResponseGainRemainder
                    (residualCalendarScale stage) response|) ≤
                expect (selection stage history)
                  (fun _ =>
                    correction.rawMovingResponseGainEnvelope
                      (residualCalendarScale stage)) := by
                  apply expect_mono
                  intro response
                  unfold rawMovingResponseGainEnvelope
                  exact Finset.single_le_sum
                    (fun other _ => abs_nonneg
                      (correction.rawMovingResponseGainRemainder
                        (residualCalendarScale stage) other))
                    (Finset.mem_univ response)
            _ =
                correction.rawMovingResponseGainEnvelope
                  (residualCalendarScale stage) := by
              rw [expect_const]
    _ =
        correction.rawMovingResponseGainEnvelope
          (residualCalendarScale stage) := by
      rw [expect_const]

omit [DecidableEq G.State] in
/-- Every supplied law and behavioral mixture has vanishing expected
one-stage complete moving remainder. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_calendarResponseGainStageBudget
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    Tendsto
      (correction.calendarResponseGainStageBudget historyLaw selection)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun stage =>
      correction.calendarResponseGainStageBudget_nonneg
        historyLaw selection stage
  · exact Filter.Eventually.of_forall fun stage =>
      correction.calendarResponseGainStageBudget_le
        historyLaw selection stage
  · exact correction.tendsto_calendarResponseGainEnvelope

/-- Cumulative expected absolute moving stage/kernel/value remainder. -/
def
    HarmonicInvisibleQuotientCorrection.calendarResponseGainCumulativeBudget
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    correction.calendarResponseGainStageBudget
      historyLaw selection stage

omit [DecidableEq G.State] in
/-- The universal calendar makes the cumulative expected absolute complete
moving response-gain remainder sublinear. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarResponseGainCumulativeBudget_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    IsAsymptoticallySublinear
      (correction.calendarResponseGainCumulativeBudget
        historyLaw selection) := by
  unfold calendarResponseGainCumulativeBudget
  exact
    isAsymptoticallySublinear_iff_tendsto.mpr
      (correction.tendsto_calendarResponseGainStageBudget
        historyLaw selection).cesaro

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
