/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ProcessedHarmonicResponseRealization

/-!
# Baseline fallback for processed harmonic response selectors

An invisible-response family need not contain an action at every public
state. Requiring a response-only selector at every history would therefore
be stronger than the strategic construction needs.

This file adjoins an explicit baseline choice. At each history the selector
may either use one source-compatible invisible response or leave the owning
player on the scheduled Fink mixture. The resulting choice mixture is
realized by an actual behavior profile, and its next-state law is exactly the
corresponding mixture of scheduled response and baseline kernels.

The baseline branch has zero response charge. Consequently this interface
removes an artificial total-source-coverage hypothesis without claiming that
the positive-response branch is already a credible punishment.
-/

set_option autoImplicit false

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

/-- A selector choice either keeps the scheduled baseline action mixture or
uses one invisible response. -/
abbrev InvisibleResponseOrBaseline
    (germ : G.AnalyticBellmanGerm) (who : ι) :=
  Option (germ.InvisibleNeutralAction who)

/-- Source-indexed fallback choices make compatibility intrinsic. -/
abbrev LocalInvisibleResponseOrBaseline
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (source : G.State) :=
  Option
    { response : germ.InvisibleNeutralAction who //
      response.source = source }

/-- Forget the source proof carried by a local fallback choice. -/
def eraseLocalInvisibleResponse
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (source : G.State) :
    LocalInvisibleResponseOrBaseline germ who source →
      InvisibleResponseOrBaseline germ who
  | none => none
  | some response => some response.1

/-- Embed a selector whose response type is indexed by the current state
into the common fallback-choice type. -/
def embedLocalFallbackSelection
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage (history : Fin (stage + 1) → G.State),
        PMF
          (LocalInvisibleResponseOrBaseline germ who
            (history (Fin.last stage)))) :
    ∀ stage, (Fin (stage + 1) → G.State) →
      PMF (InvisibleResponseOrBaseline germ who) :=
  fun stage history =>
    (selection stage history).map
      (eraseLocalInvisibleResponse germ who
        (history (Fin.last stage)))

omit [DecidableEq G.State] in
/-- A source-indexed selector is source compatible after forgetting its
proof fields. -/
theorem embedLocalFallbackSelection_source_compatible
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage (history : Fin (stage + 1) → G.State),
        PMF
          (LocalInvisibleResponseOrBaseline germ who
            (history (Fin.last stage)))) :
    ∀ stage history response,
      embedLocalFallbackSelection germ who selection
          stage history (some response) ≠ 0 →
        response.source = history (Fin.last stage) := by
  intro stage history response response_mem
  have response_support :
      some response ∈
        (embedLocalFallbackSelection
          germ who selection stage history).support :=
    response_mem
  unfold embedLocalFallbackSelection at response_support
  obtain ⟨choice, -, choice_eq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp response_support
  cases choice with
  | none =>
      simp [eraseLocalInvisibleResponse] at choice_eq
  | some chosen =>
      simp only [eraseLocalInvisibleResponse,
        Option.some.injEq] at choice_eq
      rw [← choice_eq]
      exact chosen.2

/-- The scheduled baseline next-state kernel. -/
def calendarFinkStateKernel
    (germ : G.AnalyticBellmanGerm)
    (stage : ℕ) (source : G.State) : PMF G.State :=
  (pmfPi (calendarFinkMixedProfile germ stage source)).bind
    (G.transition source)

/-- The owner's action law associated with a fallback selector choice. -/
def calendarFallbackActionDist
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (stage : ℕ) (source : G.State) :
    InvisibleResponseOrBaseline germ who → PMF (G.Act who)
  | none => calendarFinkMixedProfile germ stage source who
  | some response => PMF.pure response.1.2

/-- The next-state kernel associated with a fallback selector choice. -/
def calendarFallbackResponseKernel
    (germ : G.AnalyticBellmanGerm) {who : ι}
    (stage : ℕ) (source : G.State) :
    InvisibleResponseOrBaseline germ who → PMF G.State
  | none => calendarFinkStateKernel germ stage source
  | some response =>
      calendarInvisibleResponseKernel germ stage response

/-- Actual behavior strategy realizing the fallback selector. -/
def fallbackInvisibleResponseBehaviorStrategy
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who)) :
    G.BehaviorStrategy who :=
  fun stage history =>
    (selection stage (stateHistoryOfHist history)).bind
      (calendarFallbackActionDist germ who stage history.2)

/-- Behavior profile that realizes fallback selection for one owner and
keeps every other player on the scheduled Fink profile. -/
def realizedFallbackInvisibleResponseProfile
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who)) :
    G.BehaviorProfile :=
  Function.update (calendarFinkBehaviorProfile germ) who
    (fallbackInvisibleResponseBehaviorStrategy germ who selection)

/-- Selector mixture of baseline and response kernels. -/
def calendarFallbackMixedStep
    (germ : G.AnalyticBellmanGerm) {who : ι}
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (stage : ℕ) (history : Fin (stage + 1) → G.State) :
    PMF G.State :=
  (selection stage history).bind
    (calendarFallbackResponseKernel germ stage
      (history (Fin.last stage)))

omit [DecidableEq G.State] in
/-- Exact one-step realization of a fallback selector.

Source compatibility is required only for actual response choices. The
baseline choice is automatically defined at the current public state. -/
theorem behaviorStateStep_realizedFallbackInvisibleResponseProfile
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (source_compatible :
      ∀ stage history response,
        selection stage history (some response) ≠ 0 →
          response.source = history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    behaviorStateStep
        (realizedFallbackInvisibleResponseProfile germ who selection)
        history =
      calendarFallbackMixedStep germ selection stage
        (stateHistoryOfHist history) := by
  unfold behaviorStateStep
    realizedFallbackInvisibleResponseProfile
  change
    (G.stageActionDist
      (Function.update
        (G.scheduledMarkovBehaviorProfile
          (fun stage source =>
            calendarFinkMixedProfile germ stage source))
        who
        (fallbackInvisibleResponseBehaviorStrategy
          germ who selection))
      history).bind (G.transition history.2) =
      calendarFallbackMixedStep germ selection stage
        (stateHistoryOfHist history)
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold fallbackInvisibleResponseBehaviorStrategy
    calendarFallbackMixedStep
  rw [pmfPi_update_bind, PMF.bind_bind, PMF.bind_bind]
  apply ProbabilityMassFunction.bind_congr_on_support
  intro choice choice_mem
  cases choice with
  | none =>
      simp only [calendarFallbackActionDist,
        calendarFallbackResponseKernel]
      rw [stateHistoryOfHist_last]
      unfold calendarFinkStateKernel
      rw [← PMF.bind_bind, ← pmfPi_update_bind]
      rw [Function.update_eq_self]
  | some response =>
      have source_eq :
          response.source = history.2 := by
        rw [← stateHistoryOfHist_last history]
        exact source_compatible stage
          (stateHistoryOfHist history) response choice_mem
      simp only [calendarFallbackActionDist,
        calendarFallbackResponseKernel, PMF.pure_bind]
      unfold calendarInvisibleResponseKernel
      rw [source_eq]

/-- Actual state-history marginal generated by the fallback behavior
profile. -/
def realizedFallbackInvisibleStateHistoryLaw
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (stage : ℕ) :
    PMF (Fin (stage + 1) → G.State) :=
  (G.histDist
    (realizedFallbackInvisibleResponseProfile germ who selection)
    initial stage).map stateHistoryOfHist

omit [DecidableEq G.State] in
/-- One-step recursion for the actual fallback state-history marginal. -/
theorem realizedFallbackInvisibleStateHistoryLaw_succ
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (source_compatible :
      ∀ stage history response,
        selection stage history (some response) ≠ 0 →
          response.source = history (Fin.last stage))
    (stage : ℕ) :
    realizedFallbackInvisibleStateHistoryLaw germ
        who initial selection (stage + 1) =
      (realizedFallbackInvisibleStateHistoryLaw germ
        who initial selection stage).bind fun history =>
          (calendarFallbackMixedStep germ
            selection stage history).map
              (Fin.snoc history) := by
  unfold realizedFallbackInvisibleStateHistoryLaw
  rw [G.histDist_succ, PMF.map_bind]
  calc
    (G.histDist
        (realizedFallbackInvisibleResponseProfile
          germ who selection)
        initial stage).bind
        (fun history =>
          (((G.stageActionDist
              (realizedFallbackInvisibleResponseProfile
                germ who selection)
              history).bind
                (fun jointAction =>
                  (G.transition history.2 jointAction).bind
                    (fun successor =>
                      PMF.pure
                        ((Fin.snoc history.1
                          (history.2, jointAction), successor) :
                            G.Hist (stage + 1))))).map
            stateHistoryOfHist)) =
      (G.histDist
        (realizedFallbackInvisibleResponseProfile
          germ who selection)
        initial stage).bind
        (fun history =>
          (behaviorStateStep
            (realizedFallbackInvisibleResponseProfile
              germ who selection)
            history).map
              (Fin.snoc (stateHistoryOfHist history))) := by
        congr 1
        funext history
        rw [PMF.map_bind, behaviorStateStep]
        rw [PMF.map_bind]
        congr 1
        funext jointAction
        rw [PMF.map_bind]
        congr 1
        funext successor
        simp only [PMF.pure_map, Function.comp_apply]
        exact congrArg PMF.pure
          (stateHistoryOfHist_snoc
            history jointAction successor)
    _ =
      (G.histDist
        (realizedFallbackInvisibleResponseProfile
          germ who selection)
        initial stage).bind
        (fun history =>
          (calendarFallbackMixedStep germ selection stage
            (stateHistoryOfHist history)).map
              (Fin.snoc (stateHistoryOfHist history))) := by
        congr 1
        funext history
        rw [
          behaviorStateStep_realizedFallbackInvisibleResponseProfile
            germ who selection source_compatible history]
    _ =
      ((G.histDist
        (realizedFallbackInvisibleResponseProfile
          germ who selection)
        initial stage).map stateHistoryOfHist).bind
        (fun history =>
          (calendarFallbackMixedStep germ
            selection stage history).map
              (Fin.snoc history)) := by
        rw [PMF.bind_map]
        rfl

omit [DecidableEq G.State] in
/-- The actual fallback state-history marginal is the adaptive law of its
mixed baseline/response kernels. -/
theorem
    realizedFallbackInvisibleStateHistoryLaw_eq_adaptiveHistoryLaw
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (source_compatible :
      ∀ stage history response,
        selection stage history (some response) ≠ 0 →
          response.source = history (Fin.last stage))
    (stage : ℕ) :
    realizedFallbackInvisibleStateHistoryLaw germ
        who initial selection stage =
      adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (calendarFallbackMixedStep germ selection))
        (stage + 1) := by
  induction stage with
  | zero =>
      unfold realizedFallbackInvisibleStateHistoryLaw
      rw [G.histDist_zero, PMF.pure_map]
      rw [adaptiveHistoryLaw_succ, adaptiveHistoryLaw_zero]
      rw [PMF.pure_bind, adaptiveMarkovStep_zero, PMF.pure_map]
      exact congrArg PMF.pure
        (stateHistoryOfHist_empty initial)
  | succ stage inductionHypothesis =>
      rw [
        realizedFallbackInvisibleStateHistoryLaw_succ
          germ who initial selection source_compatible stage,
        inductionHypothesis]
      rw [
        adaptiveHistoryLaw_succ
          (adaptiveMarkovStep initial
            (calendarFallbackMixedStep germ selection))
          (stage + 1)]
      rfl

/-- Expected positive corrected gain of a fallback selector. The baseline
choice contributes zero. -/
def
    HarmonicInvisibleQuotientCorrection.calendarFallbackPositiveGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (stage : ℕ) : ℝ :=
  expect (historyLaw stage) fun history =>
    expect (selection stage history) fun choice =>
      match choice with
      | none => 0
      | some response =>
          max 0
            (correction.rawMovingCorrectedResponseGain
              (residualCalendarScale stage) response)

omit [DecidableEq G.State] in
theorem
    HarmonicInvisibleQuotientCorrection.calendarFallbackPositiveGainStage_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (stage : ℕ) :
    0 ≤ correction.calendarFallbackPositiveGainStage
      historyLaw selection stage := by
  unfold calendarFallbackPositiveGainStage
  apply expect_nonneg
  intro history
  apply expect_nonneg
  intro choice
  cases choice with
  | none => simp
  | some response => exact le_max_left _ _

omit [DecidableEq G.State] in
/-- Under the nonpositive endpoint-stage branch, every fallback selector is
bounded by the same finite analytic remainder envelope. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarFallbackPositiveGainStage_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (stage : ℕ) :
    correction.calendarFallbackPositiveGainStage
        historyLaw selection stage ≤
      correction.rawMovingResponseGainEnvelope
        (residualCalendarScale stage) := by
  unfold calendarFallbackPositiveGainStage
  calc
    expect (historyLaw stage)
        (fun history =>
          expect (selection stage history)
            (fun choice =>
              match choice with
              | none => 0
              | some response =>
                  max 0
                    (correction.rawMovingCorrectedResponseGain
                      (residualCalendarScale stage)
                      response))) ≤
      expect (historyLaw stage)
        (fun _ =>
          correction.rawMovingResponseGainEnvelope
            (residualCalendarScale stage)) := by
        apply expect_mono
        intro history
        calc
          expect (selection stage history)
              (fun choice =>
                match choice with
                | none => 0
                | some response =>
                    max 0
                      (correction.rawMovingCorrectedResponseGain
                        (residualCalendarScale stage)
                        response)) ≤
            expect (selection stage history)
              (fun _ =>
                correction.rawMovingResponseGainEnvelope
                  (residualCalendarScale stage)) := by
              apply expect_mono
              intro choice
              cases choice with
              | none =>
                  simp only
                  unfold
                    HarmonicInvisibleQuotientCorrection.rawMovingResponseGainEnvelope
                  exact Finset.sum_nonneg fun response _ =>
                    abs_nonneg
                      (correction.rawMovingResponseGainRemainder
                        (residualCalendarScale stage)
                        response)
              | some response =>
                  exact
                    (correction.max_zero_rawMovingCorrectedResponseGain_le_abs_remainder
                      stage_nonpos
                      (residualCalendarScale stage)
                      response).trans
                        (Finset.single_le_sum
                          (fun other _ =>
                            abs_nonneg
                              (correction.rawMovingResponseGainRemainder
                                (residualCalendarScale stage)
                                other))
                          (Finset.mem_univ response))
          _ =
              correction.rawMovingResponseGainEnvelope
                (residualCalendarScale stage) := by
            rw [expect_const]
    _ =
        correction.rawMovingResponseGainEnvelope
          (residualCalendarScale stage) := by
      rw [expect_const]

omit [DecidableEq G.State] in
/-- Every fallback selector has vanishing expected positive one-stage gain
when all endpoint response gains are nonpositive. -/
theorem
    HarmonicInvisibleQuotientCorrection.tendsto_calendarFallbackPositiveGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who)) :
    Tendsto
      (correction.calendarFallbackPositiveGainStage
        historyLaw selection) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun stage =>
      correction.calendarFallbackPositiveGainStage_nonneg
        historyLaw selection stage
  · exact Eventually.of_forall fun stage =>
      correction.calendarFallbackPositiveGainStage_le
        stage_nonpos historyLaw selection stage
  · exact correction.tendsto_calendarResponseGainEnvelope

/-- Cumulative positive corrected gain of a fallback selector. -/
def
    HarmonicInvisibleQuotientCorrection.calendarFallbackPositiveGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    correction.calendarFallbackPositiveGainStage
      historyLaw selection stage

omit [DecidableEq G.State] in
/-- The cumulative positive corrected fallback gain is sublinear. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarFallbackPositiveGain_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw :
      ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who)) :
    IsAsymptoticallySublinear
      (correction.calendarFallbackPositiveGain
        historyLaw selection) := by
  unfold calendarFallbackPositiveGain
  exact
    isAsymptoticallySublinear_iff_tendsto.mpr
      (correction.tendsto_calendarFallbackPositiveGainStage
        stage_nonpos historyLaw selection).cesaro

omit [DecidableEq G.State] in
/-- Operational fallback capstone. Either a fixed owned stage response
exists, or the actual fallback implementation accumulates only sublinear
positive corrected gain. -/
theorem
    HarmonicInvisibleQuotientCorrection.ownedStagePublicResponse_or_realizedFallbackSublinearGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (InvisibleResponseOrBaseline germ who))
    (source_compatible :
      ∀ stage history response,
        selection stage history (some response) ≠ 0 →
          response.source = history (Fin.last stage)) :
    (∃ response : germ.InvisibleNeutralAction who,
        Nonempty
          (AnalyticFinkStagePublicResponse germ
            (ownedInvisibleForwardResponse response))) ∨
      (IsAsymptoticallySublinear
          (correction.calendarFallbackPositiveGain
            (realizedFallbackInvisibleStateHistoryLaw
              germ who initial selection)
            selection) ∧
        ∀ stage,
          realizedFallbackInvisibleStateHistoryLaw
              germ who initial selection stage =
            adaptiveHistoryLaw
              (adaptiveMarkovStep initial
                (calendarFallbackMixedStep germ selection))
              (stage + 1)) := by
  rcases
      exists_ownedStagePublicResponse_or_endpointStageGain_nonpos
        germ who with response | stage_nonpos
  · exact Or.inl response
  · exact Or.inr
      ⟨correction.calendarFallbackPositiveGain_sublinear
          stage_nonpos
          (realizedFallbackInvisibleStateHistoryLaw
            germ who initial selection)
          selection,
        realizedFallbackInvisibleStateHistoryLaw_eq_adaptiveHistoryLaw
          germ who initial selection source_compatible⟩

omit [DecidableEq G.State] in
/-- Source-indexed fallback selectors satisfy the operational capstone
without a separate compatibility hypothesis. -/
theorem
    HarmonicInvisibleQuotientCorrection.ownedStageResponse_or_localFallbackSublinearGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ stage (history : Fin (stage + 1) → G.State),
        PMF
          (LocalInvisibleResponseOrBaseline germ who
            (history (Fin.last stage)))) :
    (∃ response : germ.InvisibleNeutralAction who,
        Nonempty
          (AnalyticFinkStagePublicResponse germ
            (ownedInvisibleForwardResponse response))) ∨
      (IsAsymptoticallySublinear
          (correction.calendarFallbackPositiveGain
            (realizedFallbackInvisibleStateHistoryLaw
              germ who initial
              (embedLocalFallbackSelection
                germ who selection))
            (embedLocalFallbackSelection
              germ who selection)) ∧
        ∀ stage,
          realizedFallbackInvisibleStateHistoryLaw
              germ who initial
              (embedLocalFallbackSelection
                germ who selection) stage =
            adaptiveHistoryLaw
              (adaptiveMarkovStep initial
                (calendarFallbackMixedStep germ
                  (embedLocalFallbackSelection
                    germ who selection)))
              (stage + 1)) := by
  exact
    correction.ownedStagePublicResponse_or_realizedFallbackSublinearGain
      initial
      (embedLocalFallbackSelection germ who selection)
      (embedLocalFallbackSelection_source_compatible
        germ who selection)

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
