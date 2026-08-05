/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ProcessedHarmonicResponseRealization

/-!
# Realized Bellman gains for processed harmonic responses

The behavioral realization of a predictable invisible-response selector has
the correct state kernel.  This file also identifies its actual one-step
stage-payoff-plus-continuation gain.

On calendar stages inside the analytic germ interval, the realized gain is
the selector average of the raw moving corrected response gain.  On the
finite fallback prefix, it is instead the selector average of the endpoint
corrected response gain.  This distinction is exact: the fallback profile
and continuation factor are both evaluated at the endpoint.

Consequently, in the branch where every endpoint stage gain is nonpositive,
the expected positive part of the actual Bellman gain is asymptotically
sublinear.  Eventual membership of the universal calendar in the germ
interval is precisely what removes the finite fallback prefix.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Filter Math Math.PMFProduct Math.Probability Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- Safe corrected factor used by the realized calendar.  It follows the
moving analytic factor once the scale is valid and uses the endpoint factor
on the finite fallback prefix. -/
def HarmonicInvisibleQuotientCorrection.calendarCorrectedFactor
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage : ℕ) : G.State → Payoff ι :=
  if _valid :
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius then
    correction.movingCorrectedFactor (residualCalendarScale stage)
  else
    correction.movingCorrectedFactor 0

omit [DecidableEq G.State] in
theorem
    HarmonicInvisibleQuotientCorrection.calendarCorrectedFactor_eq_moving
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage : ℕ)
    (valid :
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius) :
    correction.calendarCorrectedFactor stage =
      correction.movingCorrectedFactor
        (residualCalendarScale stage) := by
  simp [calendarCorrectedFactor, valid]

omit [DecidableEq G.State] in
theorem
    HarmonicInvisibleQuotientCorrection.calendarCorrectedFactor_eq_endpoint
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage : ℕ)
    (invalid :
      ¬residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius) :
    correction.calendarCorrectedFactor stage =
      correction.movingCorrectedFactor 0 := by
  simp [calendarCorrectedFactor, invalid]

/-- The response gain matching the safe calendar implementation. -/
def HarmonicInvisibleQuotientCorrection.calendarSemanticResponseGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage : ℕ) (response : germ.InvisibleNeutralAction who) : ℝ :=
  if residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius then
    correction.rawMovingCorrectedResponseGain
      (residualCalendarScale stage) response
  else
    correction.endpointCorrectedResponseGain response

/-- Actual one-step stage-plus-continuation gain of the realized response
profile over the safe scheduled Fink baseline after a game history. -/
def HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainAt
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    {stage : ℕ} (history : G.Hist stage) : ℝ :=
  let profile :=
    realizedInvisibleResponseProfile germ who selection
  let factor := correction.calendarCorrectedFactor stage
  G.stageEUAt profile history who +
      expect (behaviorStateStep profile history)
        (fun successor => factor successor who) -
    (G.mixedStageEU history.2
        (calendarFinkMixedProfile germ stage history.2) who +
      expect
        ((pmfPi
          (calendarFinkMixedProfile germ stage history.2)).bind
            (G.transition history.2))
        (fun successor => factor successor who))

omit [DecidableEq G.State] in
private theorem realized_stageEU_eq_selector
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
        (realizedInvisibleResponseProfile germ who selection)
        history who =
      expect (selection stage (stateHistoryOfHist history))
        (fun response =>
          G.mixedStageEU response.source
            (Function.update
              (calendarFinkMixedProfile germ stage response.source)
              who (PMF.pure response.1.2))
            who) := by
  unfold stageEUAt realizedInvisibleResponseProfile
  unfold calendarFinkBehaviorProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold invisibleResponseBehaviorStrategy
  rw [pmfPi_update_bind, expect_bind, expect_map]
  apply ProbabilityMassFunction.expect_congr_on_support
  intro response response_mem
  have source_eq :
      response.source = history.2 := by
    rw [← stateHistoryOfHist_last history]
    exact source_compatible stage (stateHistoryOfHist history)
      response response_mem
  simp only [mixedStageEU]
  rw [source_eq]

omit [DecidableEq G.State] in
private theorem realized_continuation_eq_selector
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage))
    (factor : G.State → Payoff ι)
    {stage : ℕ} (history : G.Hist stage) :
    expect
        (behaviorStateStep
          (realizedInvisibleResponseProfile germ who selection)
          history)
        (fun successor => factor successor who) =
      expect (selection stage (stateHistoryOfHist history))
        (fun response =>
          expect
            (calendarInvisibleResponseKernel germ stage response)
            (fun successor => factor successor who)) := by
  rw [
    behaviorStateStep_realizedInvisibleResponseProfile germ
      who selection source_compatible history]
  unfold calendarInvisibleMixedStep
  rw [expect_bind]

omit [DecidableEq G.State] in
theorem
    HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainAt_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    correction.realizedCalendarBellmanGainAt selection history =
      expect (selection stage (stateHistoryOfHist history))
        (correction.calendarSemanticResponseGain stage) := by
  by_cases valid :
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius
  · rw [show correction.calendarSemanticResponseGain stage =
        fun response =>
          correction.rawMovingCorrectedResponseGain
            (residualCalendarScale stage) response by
        funext response
        simp [calendarSemanticResponseGain, valid]]
    unfold realizedCalendarBellmanGainAt
    dsimp only
    rw [correction.calendarCorrectedFactor_eq_moving stage valid]
    rw [realized_stageEU_eq_selector germ who selection
      source_compatible history]
    rw [realized_continuation_eq_selector germ who selection
      source_compatible]
    rw [← expect_add]
    rw [← expect_const
      (selection stage (stateHistoryOfHist history))
      (G.mixedStageEU history.2
          (calendarFinkMixedProfile germ stage history.2) who +
        expect
          ((pmfPi
            (calendarFinkMixedProfile germ stage history.2)).bind
              (G.transition history.2))
          (fun successor =>
            correction.movingCorrectedFactor
              (residualCalendarScale stage) successor who))]
    rw [← expect_sub]
    apply ProbabilityMassFunction.expect_congr_on_support
    intro response response_mem
    have source_eq :
        response.source = history.2 := by
      rw [← stateHistoryOfHist_last history]
      exact source_compatible stage (stateHistoryOfHist history)
        response response_mem
    rw [
      correction.rawMovingCorrectedResponseGain_eq_at
        valid response]
    simp only [
      calendarFinkMixedProfile_eq_finkPointAt germ stage valid]
    unfold finkStageGain finkContinuationGain mixedStageEU
    rw [
      calendarInvisibleResponseKernel_eq_finkPointAt
        germ stage valid response]
    simp only [source_eq]
    rw [G.expect_finkPureDeviationStateKernel_eq, expect_bind]
    ring
  · rw [show correction.calendarSemanticResponseGain stage =
        correction.endpointCorrectedResponseGain by
        funext response
        simp [calendarSemanticResponseGain, valid]]
    unfold realizedCalendarBellmanGainAt
    dsimp only
    rw [correction.calendarCorrectedFactor_eq_endpoint stage valid]
    rw [realized_stageEU_eq_selector germ who selection
      source_compatible history]
    rw [realized_continuation_eq_selector germ who selection
      source_compatible]
    rw [← expect_add]
    rw [← expect_const
      (selection stage (stateHistoryOfHist history))
      (G.mixedStageEU history.2
          (calendarFinkMixedProfile germ stage history.2) who +
        expect
          ((pmfPi
            (calendarFinkMixedProfile germ stage history.2)).bind
              (G.transition history.2))
          (fun successor =>
            correction.movingCorrectedFactor 0 successor who))]
    rw [← expect_sub]
    apply ProbabilityMassFunction.expect_congr_on_support
    intro response response_mem
    have source_eq :
        response.source = history.2 := by
      rw [← stateHistoryOfHist_last history]
      exact source_compatible stage (stateHistoryOfHist history)
        response response_mem
    simp only [source_eq]
    unfold endpointCorrectedResponseGain
    rw [calendarInvisibleResponseKernel_eq_endpoint
      germ stage valid response]
    unfold finkStageGain finkContinuationGain mixedStageEU
      movingCorrectedFactor
    simp only [calendarFinkMixedProfile, valid, dite_false]
    simp only [germ.finkProfile_endpointFinkPoint]
    simp only [source_eq]
    rw [G.expect_finkPureDeviationStateKernel_eq, expect_bind]
    have endpoint_deviation_profile_eq :
        Function.update
            (G.finkProfile germ.endpointFinkPoint history.2)
            who (PMF.pure response.1.2) =
          Function.update (germ.endpointProfile history.2)
            who (PMF.pure response.1.2) :=
      congrArg
        (fun profile =>
          Function.update profile who (PMF.pure response.1.2))
        (congrFun germ.finkProfile_endpointFinkPoint history.2)
    rw [endpoint_deviation_profile_eq]
    ring

/-- Expected signed realized Bellman gain at one calendar stage. -/
def
    HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) : ℝ :=
  expect
    (G.histDist
      (realizedInvisibleResponseProfile germ who selection)
      initial stage)
    (correction.realizedCalendarBellmanGainAt selection)

omit [DecidableEq G.State] in
/-- Exact expected-gain identity under the actual game-history law.  The
right-hand side uses the safe semantic response gain and therefore retains
the endpoint fallback distinction. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainStage_eq
    {jet : germ.LowerValueJet} {who : ι}
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
    (stage : ℕ) :
    correction.realizedCalendarBellmanGainStage
        initial selection stage =
      expect
        (realizedInvisibleStateHistoryLaw
          germ who initial selection stage)
        (fun history =>
          expect (selection stage history)
            (correction.calendarSemanticResponseGain stage)) := by
  unfold realizedCalendarBellmanGainStage
    realizedInvisibleStateHistoryLaw
  rw [expect_map]
  apply congrArg
    (expect
      (G.histDist
        (realizedInvisibleResponseProfile germ who selection)
        initial stage))
  funext history
  exact correction.realizedCalendarBellmanGainAt_eq
    selection source_compatible history

omit [DecidableEq G.State] in
/-- On a valid calendar stage, the actual expected gain is exactly the
selector average of the moving analytic response gain. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainStage_eq_moving
    {jet : germ.LowerValueJet} {who : ι}
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
    (stage : ℕ)
    (valid :
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius) :
    correction.realizedCalendarBellmanGainStage
        initial selection stage =
      expect
        (realizedInvisibleStateHistoryLaw
          germ who initial selection stage)
        (fun history =>
          expect (selection stage history)
            (fun response =>
              correction.rawMovingCorrectedResponseGain
                (residualCalendarScale stage) response)) := by
  rw [
    correction.realizedCalendarBellmanGainStage_eq
      initial selection source_compatible stage]
  apply congrArg
    (expect
      (realizedInvisibleStateHistoryLaw
        germ who initial selection stage))
  funext history
  apply congrArg (expect (selection stage history))
  funext response
  simp [calendarSemanticResponseGain, valid]

omit [DecidableEq G.State] in
/-- On a fallback stage, the actual expected gain is exactly the selector
average of the endpoint corrected response gain. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedCalendarBellmanGainStage_eq_endpoint
    {jet : germ.LowerValueJet} {who : ι}
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
    (stage : ℕ)
    (invalid :
      ¬residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius) :
    correction.realizedCalendarBellmanGainStage
        initial selection stage =
      expect
        (realizedInvisibleStateHistoryLaw
          germ who initial selection stage)
        (fun history =>
          expect (selection stage history)
            correction.endpointCorrectedResponseGain) := by
  rw [
    correction.realizedCalendarBellmanGainStage_eq
      initial selection source_compatible stage]
  apply congrArg
    (expect
      (realizedInvisibleStateHistoryLaw
        germ who initial selection stage))
  funext history
  apply congrArg (expect (selection stage history))
  funext response
  simp [calendarSemanticResponseGain, invalid]

/-- Expected positive realized Bellman gain at one calendar stage. -/
def
    HarmonicInvisibleQuotientCorrection.realizedPositiveBellmanGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) : ℝ :=
  expect
    (G.histDist
      (realizedInvisibleResponseProfile germ who selection)
      initial stage)
    (fun history =>
      max 0
        (correction.realizedCalendarBellmanGainAt
          selection history))

/-- Cumulative expected positive realized Bellman gain. -/
def
    HarmonicInvisibleQuotientCorrection.realizedPositiveBellmanGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    correction.realizedPositiveBellmanGainStage
      initial selection stage

omit [DecidableEq G.State] in
/-- The realized positive Bellman gain is nonnegative stage by stage. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedPositiveBellmanGainStage_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    0 ≤ correction.realizedPositiveBellmanGainStage
      initial selection stage := by
  unfold realizedPositiveBellmanGainStage
  exact expect_nonneg _ _ fun history => le_max_left _ _

omit [DecidableEq G.State] in
/-- On valid stages, convexity of the positive part bounds the realized
gain by the selector-wise positive-gain quantity used by the analytic
calendar theorem. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedPositiveBellmanGainStage_le
    {jet : germ.LowerValueJet} {who : ι}
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
    (stage : ℕ)
    (valid :
      residualCalendarScale stage ∈ Ioo (0 : ℝ) germ.radius) :
    correction.realizedPositiveBellmanGainStage
        initial selection stage ≤
      correction.calendarPositiveResponseGainStage
        (realizedInvisibleStateHistoryLaw
          germ who initial selection)
        selection stage := by
  unfold realizedPositiveBellmanGainStage
    calendarPositiveResponseGainStage
  calc
    expect
        (G.histDist
          (realizedInvisibleResponseProfile germ who selection)
          initial stage)
        (fun history =>
          max 0
            (correction.realizedCalendarBellmanGainAt
              selection history)) =
      expect
        (G.histDist
          (realizedInvisibleResponseProfile germ who selection)
          initial stage)
        (fun history =>
          max 0
            (expect
              (selection stage (stateHistoryOfHist history))
              (fun response =>
                correction.rawMovingCorrectedResponseGain
                  (residualCalendarScale stage) response))) := by
        apply congrArg
          (expect
            (G.histDist
              (realizedInvisibleResponseProfile germ who selection)
              initial stage))
        funext history
        rw [
          correction.realizedCalendarBellmanGainAt_eq
            selection source_compatible history]
        apply congrArg (max 0)
        apply congrArg
          (expect
            (selection stage (stateHistoryOfHist history)))
        funext response
        simp [calendarSemanticResponseGain, valid]
    _ ≤
      expect
        (G.histDist
          (realizedInvisibleResponseProfile germ who selection)
          initial stage)
        (fun history =>
          expect
            (selection stage (stateHistoryOfHist history))
            (fun response =>
              max 0
                (correction.rawMovingCorrectedResponseGain
                  (residualCalendarScale stage) response))) := by
        apply expect_mono
        intro history
        apply max_le
        · exact expect_nonneg _ _ fun response => le_max_left _ _
        · exact
            expect_mono _ _ _
              (fun response =>
                le_max_right 0
                  (correction.rawMovingCorrectedResponseGain
                    (residualCalendarScale stage) response))
    _ =
      expect
        (realizedInvisibleStateHistoryLaw
          germ who initial selection stage)
        (fun history =>
          expect (selection stage history)
            (fun response =>
              max 0
                (correction.rawMovingCorrectedResponseGain
                  (residualCalendarScale stage) response))) := by
        unfold realizedInvisibleStateHistoryLaw
        rw [expect_map]

omit [DecidableEq G.State] in
/-- In the nonpositive endpoint-stage branch, the actual expected positive
Bellman gain vanishes stagewise.  The proof uses the moving analytic budget
eventually; all fallback stages lie in a finite prefix. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_realizedPositiveBellmanGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage)) :
    Tendsto
      (correction.realizedPositiveBellmanGainStage
        initial selection)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun stage =>
      correction.realizedPositiveBellmanGainStage_nonneg
        initial selection stage
  · filter_upwards
      [eventually_residualCalendarScale_mem_radius
        (germ := germ)] with stage valid
    exact
      (correction.realizedPositiveBellmanGainStage_le
        initial selection source_compatible stage valid).trans
        (correction.calendarPositiveResponseGainStage_le
          stage_nonpos
          (realizedInvisibleStateHistoryLaw
            germ who initial selection)
          selection stage)
  · exact
      correction.tendsto_calendarResponseGainStageBudget
        (realizedInvisibleStateHistoryLaw
          germ who initial selection)
        selection

omit [DecidableEq G.State] in
/-- The cumulative expected positive Bellman gain of the actual realized
behavior is sublinear.  No separate numerical prefix bound is needed:
Cesàro averaging automatically absorbs the finitely many endpoint fallback
stages. -/
theorem
    HarmonicInvisibleQuotientCorrection.realizedPositiveBellmanGain_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ stage history response,
        selection stage history response ≠ 0 →
          response.source = history (Fin.last stage)) :
    IsAsymptoticallySublinear
      (correction.realizedPositiveBellmanGain
        initial selection) := by
  unfold realizedPositiveBellmanGain
  exact
    isAsymptoticallySublinear_iff_tendsto.mpr
      (correction.tendsto_realizedPositiveBellmanGainStage
        stage_nonpos initial selection source_compatible).cesaro

omit [DecidableEq G.State] in
/-- Operational processed-harmonic alternative stated entirely for the
actual realized behavior: either one fixed owned analytic stage response is
available, or that behavior's cumulative positive corrected Bellman gain is
sublinear. -/
theorem
    HarmonicInvisibleQuotientCorrection.ownedStagePublicResponse_or_realizedSublinearBellmanGain
    {jet : germ.LowerValueJet} {who : ι}
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
    (∃ response : germ.InvisibleNeutralAction who,
        Nonempty
          (AnalyticFinkStagePublicResponse germ
            (ownedInvisibleForwardResponse response))) ∨
      IsAsymptoticallySublinear
        (correction.realizedPositiveBellmanGain
          initial selection) := by
  rcases
      exists_ownedStagePublicResponse_or_endpointStageGain_nonpos
        germ who with response | stage_nonpos
  · exact Or.inl response
  · exact Or.inr
      (correction.realizedPositiveBellmanGain_sublinear
        stage_nonpos initial selection source_compatible)

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
