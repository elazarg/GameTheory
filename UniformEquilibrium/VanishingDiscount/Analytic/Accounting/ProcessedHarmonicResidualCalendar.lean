/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicMovingResidualDeflation
import Math.OnlineLearning.UniversalCalendar

/-!
# Universal-calendar discharge of moving harmonic residuals

The support-based deflation theorem pays a moving-baseline residual when it
is confined to an earlier strict set.  There is a second, independent
discharge mechanism requiring no support hypothesis.

For a harmonic correction, the raw prescribed-kernel residual is analytic
and vanishes at the endpoint.  Therefore its absolute value tends to zero
uniformly over the finite invisible-response family.  Evaluating it at the
piecewise-constant universal calendar scale gives a per-stage envelope
tending to zero.  Cesàro averaging then makes its cumulative expected
absolute cost sublinear under every predictable behavioral mixture and every
history law.

Only continuity at the endpoint is used after analyticity establishes it.
No finite analytic order is needed for this upper-bound argument.  The
slower-than-polynomial feature of the universal calendar remains available
to the simultaneous lower-bound monitoring arguments.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Filter Math Math.Probability Math.OnlineLearning Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- Prescribed-kernel residual written in the globally analytic raw
coordinates. -/
def HarmonicInvisibleQuotientCorrection.rawMovingBaselineResidual
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) (source : G.State) : ℝ :=
  (∑ destination,
      germ.rawStateKernelCurve t source destination *
        correction.potential destination) -
    correction.potential source

omit [DecidableEq G.State] in
/-- The raw moving residual is analytic at the endpoint. -/
theorem HarmonicInvisibleQuotientCorrection.analytic_rawMovingBaselineResidual
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (source : G.State) :
    AnalyticAt ℝ
      (fun t => correction.rawMovingBaselineResidual t source) 0 := by
  unfold rawMovingBaselineResidual
  have sum_analytic :
      AnalyticAt ℝ
        (fun t =>
          ∑ destination,
            germ.rawStateKernelCurve t source destination *
              correction.potential destination)
        0 := by
    have analytic_sum :=
      Finset.univ.analyticAt_sum
        (f := fun destination t =>
          germ.rawStateKernelCurve t source destination *
            correction.potential destination)
        fun destination _ =>
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              germ.analytic_rawStateKernelCurve source)
            destination).mul analyticAt_const
    apply analytic_sum.congr
    exact Filter.Eventually.of_forall fun t => by
      simp only [Finset.sum_apply]
  exact sum_analytic.sub analyticAt_const

omit [DecidableEq G.State] in
/-- Endpoint harmonicity makes the raw moving residual vanish at zero. -/
theorem HarmonicInvisibleQuotientCorrection.rawMovingBaselineResidual_zero
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (source : G.State) :
    correction.rawMovingBaselineResidual 0 source = 0 := by
  unfold rawMovingBaselineResidual
  calc
    (∑ destination,
          germ.rawStateKernelCurve 0 source destination *
            correction.potential destination) -
        correction.potential source =
      expect
          (G.finkStateKernel germ.endpointFinkPoint source)
          correction.potential -
        correction.potential source := by
          rw [expect_eq_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro destination _
          rw [germ.rawStateKernelCurve_zero_eq_finkStateKernel]
    _ = 0 := by
      rw [correction.harmonic source, sub_self]

omit [DecidableEq G.State] in
/-- On the positive analytic interval, the raw residual is exactly the
semantic `movingBaselineResidualAt`. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingBaselineResidual_eq_at
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) :
    correction.rawMovingBaselineResidual t source =
      correction.movingBaselineResidualAt ht source := by
  unfold rawMovingBaselineResidual movingBaselineResidualAt
  rw [expect_eq_sum]
  apply congrArg (fun value => value - correction.potential source)
  apply Finset.sum_congr rfl
  intro destination _
  rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]

/-- Finite-family absolute envelope for all invisible-response sources. -/
def HarmonicInvisibleQuotientCorrection.rawMovingResidualEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (t : ℝ) : ℝ :=
  ∑ response : germ.InvisibleNeutralAction who,
    |correction.rawMovingBaselineResidual t response.source|

omit [DecidableEq G.State] in
/-- The finite raw residual envelope tends to zero at the endpoint. -/
theorem HarmonicInvisibleQuotientCorrection.tendsto_rawMovingResidualEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    Tendsto correction.rawMovingResidualEnvelope
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  unfold rawMovingResidualEnvelope
  have sum_tendsto :=
    tendsto_finsetSum (s := Finset.univ)
      (fun (response : germ.InvisibleNeutralAction who) _ => by
      have residual_tendsto :
          Tendsto
            (fun t =>
              correction.rawMovingBaselineResidual
                t response.source)
            (𝓝 (0 : ℝ)) (𝓝 0) := by
        have continuous :=
          (correction.analytic_rawMovingBaselineResidual
            response.source).continuousAt
        change
          Tendsto
            (fun t =>
              correction.rawMovingBaselineResidual
                t response.source)
            (𝓝 (0 : ℝ))
            (𝓝
              (correction.rawMovingBaselineResidual
                0 response.source)) at continuous
        rw [
          correction.rawMovingBaselineResidual_zero response.source]
          at continuous
        exact continuous
      simpa only [abs_zero] using residual_tendsto.abs
      )
  simpa using sum_tendsto

private theorem tendsto_residualAnytimeEpochIndex :
    Tendsto anytimeEpochIndex atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards
    [eventually_ge_atTop
      (epochStart anytimeEpochLength K)] with t ht
  exact anytimeEpochIndex_ge_of_start_le ht

/-- Piecewise-constant universal parameter used at every calendar stage. -/
def residualCalendarScale (stage : ℕ) : ℝ :=
  universalEpochScale (anytimeEpochIndex stage)

theorem residualCalendarScale_pos (stage : ℕ) :
    0 < residualCalendarScale stage :=
  universalEpochScale_pos _

theorem tendsto_residualCalendarScale :
    Tendsto residualCalendarScale atTop (𝓝 0) :=
  tendsto_universalEpochScale.comp tendsto_residualAnytimeEpochIndex

omit [DecidableEq G.State] in
theorem eventually_residualCalendarScale_mem_radius :
    ∀ᶠ stage : ℕ in atTop,
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius := by
  have eventually_lt :
      ∀ᶠ stage : ℕ in atTop,
        residualCalendarScale stage < germ.radius :=
    tendsto_residualCalendarScale.eventually
      (Iio_mem_nhds germ.radius_pos)
  filter_upwards [eventually_lt] with stage stage_lt
  exact ⟨residualCalendarScale_pos stage, stage_lt⟩

omit [DecidableEq G.State] in
/-- The finite residual envelope vanishes along the universal calendar. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_calendarResidualEnvelope
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    Tendsto
      (fun stage =>
        correction.rawMovingResidualEnvelope
          (residualCalendarScale stage))
      atTop (𝓝 0) :=
  correction.tendsto_rawMovingResidualEnvelope.comp
    tendsto_residualCalendarScale

/-- Expected one-stage absolute moving residual.  The history law is
arbitrary; in applications it is the law generated by the scheduled
behavioral response kernels. -/
def HarmonicInvisibleQuotientCorrection.calendarResidualStageBudget
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
      |correction.rawMovingBaselineResidual
        (residualCalendarScale stage) response.source|

omit [DecidableEq G.State] in
/-- The expected stage budget is nonnegative. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarResidualStageBudget_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    0 ≤ correction.calendarResidualStageBudget
      historyLaw selection stage := by
  unfold calendarResidualStageBudget
  apply expect_nonneg
  intro history
  exact expect_nonneg _ _ fun response => abs_nonneg _

omit [DecidableEq G.State] in
/-- The finite analytic envelope dominates the expected residual under
every history law and predictable behavioral mixture. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarResidualStageBudget_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    correction.calendarResidualStageBudget historyLaw selection stage ≤
      correction.rawMovingResidualEnvelope
        (residualCalendarScale stage) := by
  unfold calendarResidualStageBudget
  calc
    expect (historyLaw stage)
        (fun history =>
          expect (selection stage history)
            (fun response =>
              |correction.rawMovingBaselineResidual
                (residualCalendarScale stage) response.source|)) ≤
        expect (historyLaw stage)
          (fun _ =>
            correction.rawMovingResidualEnvelope
              (residualCalendarScale stage)) := by
          apply expect_mono
          intro history
          calc
            expect (selection stage history)
                (fun response =>
                  |correction.rawMovingBaselineResidual
                    (residualCalendarScale stage) response.source|) ≤
                expect (selection stage history)
                  (fun _ =>
                    correction.rawMovingResidualEnvelope
                      (residualCalendarScale stage)) := by
                  apply expect_mono
                  intro response
                  unfold rawMovingResidualEnvelope
                  exact Finset.single_le_sum
                    (fun other _ => abs_nonneg
                      (correction.rawMovingBaselineResidual
                        (residualCalendarScale stage)
                        other.source))
                    (Finset.mem_univ response)
            _ =
                correction.rawMovingResidualEnvelope
                  (residualCalendarScale stage) := by
              rw [expect_const]
    _ =
        correction.rawMovingResidualEnvelope
          (residualCalendarScale stage) := by
      rw [expect_const]

omit [DecidableEq G.State] in
/-- Expected one-stage residual cost tends to zero uniformly over all
predictable behavioral selections and all supplied history laws. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_calendarResidualStageBudget
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    Tendsto
      (correction.calendarResidualStageBudget historyLaw selection)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun stage =>
      correction.calendarResidualStageBudget_nonneg
        historyLaw selection stage
  · exact Filter.Eventually.of_forall fun stage =>
      correction.calendarResidualStageBudget_le
        historyLaw selection stage
  · exact correction.tendsto_calendarResidualEnvelope

/-- Cumulative expected absolute moving residual on the universal
calendar. -/
def HarmonicInvisibleQuotientCorrection.calendarResidualCumulativeBudget
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
    correction.calendarResidualStageBudget
      historyLaw selection stage

omit [DecidableEq G.State] in
/-- The universal calendar makes cumulative expected absolute moving
residual sublinear without a strict-set support hypothesis. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarResidualCumulativeBudget_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    IsAsymptoticallySublinear
      (correction.calendarResidualCumulativeBudget
        historyLaw selection) := by
  unfold calendarResidualCumulativeBudget
  exact
    isAsymptoticallySublinear_iff_tendsto.mpr
      (correction.tendsto_calendarResidualStageBudget
        historyLaw selection).cesaro

/-- Calendar budget with an arbitrary supplied law for the moving residual.
The endpoint harmonic slack and the moving residual may be estimated under
different laws; applications can instantiate `historyLaw` with the actual
scheduled strategy law. -/
def HarmonicInvisibleQuotientCorrection.calendarMovingCorrectionBudgetWith
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (T : ℕ) : ℝ :=
  (∑ stage ∈ Finset.range T,
      correction.expectedMixedSlackStage initial selection stage) +
    correction.calendarResidualCumulativeBudget
      historyLaw selection T

omit [DecidableEq G.State] in
/-- The combined calendar budget is sublinear for every supplied residual
history law. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarMovingCorrectionBudgetWith_sublinear
    {jet : germ.LowerValueJet}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage))
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State)) :
    IsAsymptoticallySublinear
      (correction.calendarMovingCorrectionBudgetWith
        initial selection historyLaw) := by
  unfold calendarMovingCorrectionBudgetWith
  exact
    (correction.mixedSlackStageLedger_sublinear
      span processed initial selection source_compatible).add
      (correction.calendarResidualCumulativeBudget_sublinear
        historyLaw selection)

/-- Endpoint-kernel history law used by the already constructed harmonic
slack account. -/
def HarmonicInvisibleQuotientCorrection.endpointMixedHistoryLaw
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (_correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) : PMF (Fin (stage + 1) → G.State) :=
  adaptiveHistoryLaw
    (adaptiveMarkovStep initial
      (mixedTransitionComparison
        (fun response : germ.InvisibleNeutralAction who =>
          response.kernel)
        selection))
    (stage + 1)

/-- Complete calendar budget: automatic endpoint harmonic slack plus the
scheduled moving-baseline residual. -/
def HarmonicInvisibleQuotientCorrection.calendarMovingCorrectionBudget
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  correction.calendarMovingCorrectionBudgetWith
    initial selection
    (correction.endpointMixedHistoryLaw initial selection) T

omit [DecidableEq G.State] in
/-- The universal schedule removes the fixed-parameter support hypothesis:
the full harmonic-slack plus moving-residual budget is sublinear for every
source-compatible predictable behavioral mixture. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarMovingCorrectionBudget_sublinear
    {jet : germ.LowerValueJet}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage)) :
    IsAsymptoticallySublinear
      (correction.calendarMovingCorrectionBudget
        initial selection) := by
  unfold calendarMovingCorrectionBudget
  exact correction.calendarMovingCorrectionBudgetWith_sublinear
    span processed initial selection source_compatible
    (correction.endpointMixedHistoryLaw initial selection)

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
