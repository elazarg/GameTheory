/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.PuncturedPotentialCalendarAccount
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicResponseRealization

/-!
# Full-history behavior accounts for player-owned potentials

Fix a player and an arbitrary unilateral behavior strategy.  At every public
history, the strategy's action distribution is a mixture of the corresponding
pure-action rows in the full player-owned operational family.  The other
players follow the Fink profile at the parameter of the current universal
calendar epoch.

There is no endpoint-neutral support condition in this construction.  The
full player-owned scaled potential controls every action row, so its
punctured state potential telescopes directly under the actual deviating
profile's `histDist`.  Completed epochs and the current prefix are paid by
one explicit asymptotically sublinear budget.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Math.PMFProduct Math.Probability Set
open Math.Probability.AnalyticScaledChargedOccupationPotential
open GameTheory.StochasticGame.AnalyticBellmanGerm.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The shifted analytic parameter used at one calendar stage.  This is
exactly `calendarScale`, the shared wrapper around
`shiftedUniversalEpochScale` and `anytimeEpochIndex` also used by the
player-neutral calendar account. -/
abbrev playerOwnedCalendarScale
    (startEpoch stage : ℕ) : ℝ :=
  calendarScale startEpoch stage

/-- The actual unilateral deviation against the changing Fink calendar. -/
def scheduledPlayerOwnedFinkDeviationProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who) :
    G.BehaviorProfile :=
  Function.update
    (G.scheduledMarkovBehaviorProfile
      (fun stage source =>
        G.finkProfile
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          source))
    who dev

/-- The one-step state law obtained by mixing the owner's genuine
pure-action rows with the arbitrary behavior strategy at this history. -/
def playerOwnedCalendarMixedStep
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    PMF G.State :=
  (dev stage history).bind fun action =>
    germ.finkOwnerActualOccupationKernelAt
      (valid (anytimeEpochIndex stage)) who
      (.inr (history.2, action))

omit [DecidableEq G.State] in
/-- Exact one-step realization under the actual arbitrary unilateral
behavior strategy. -/
theorem behaviorStateStep_scheduledPlayerOwnedFinkDeviationProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    LowerValueJet.behaviorStateStep
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        history =
      playerOwnedCalendarMixedStep
        germ who startEpoch valid dev history := by
  unfold LowerValueJet.behaviorStateStep
    scheduledPlayerOwnedFinkDeviationProfile
    playerOwnedCalendarMixedStep
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  rw [pmfPi_update_bind, PMF.bind_bind]
  apply ProbabilityMassFunction.bind_congr_on_support
  intro action _
  rfl

/-- Expected moving raw owner charge at one actual public history. -/
def playerOwnedCalendarRawCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (dev : G.BehaviorStrategy who) :
    G.HistoryPotential :=
  fun stage history =>
    expect (dev stage history) fun action =>
      germ.rawPlayerOwnedOccupationCharge B who
        (playerOwnedCalendarScale startEpoch stage)
        (.inr (history.2, action))

omit [DecidableEq G.State] in
private theorem scheduledPlayerOwned_stageEU_eq_actionRows
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        history who =
      expect (dev stage history) (fun action =>
        germ.playerOwnedOccupationStageEUAt
          (valid (anytimeEpochIndex stage)) who
          (.inr (history.2, action))) := by
  unfold stageEUAt scheduledPlayerOwnedFinkDeviationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  rw [pmfPi_update_bind, expect_bind]
  rfl

omit [DecidableEq G.State] in
private theorem scheduledPlayerOwned_continuation_eq_actionRows
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    G.historyContinuationEU
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        (fun _ nextHistory => B nextHistory.2 who)
        history =
      expect (dev stage history) (fun action =>
        expect
          (germ.finkOwnerActualOccupationKernelAt
            (valid (anytimeEpochIndex stage)) who
            (.inr (history.2, action)))
          (fun destination => B destination who)) := by
  unfold historyContinuationEU
    scheduledPlayerOwnedFinkDeviationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  rw [pmfPi_update_bind, expect_bind]
  apply congrArg (expect (dev stage history))
  funext action
  change
    expect
        (pmfPi
          (Function.update
            (G.finkProfile
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2)
            who (PMF.pure action)))
        (fun actions =>
          expect (G.transition history.2 actions)
            (fun destination => B destination who)) =
      expect
        (G.finkPureDeviationStateKernel
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who action)
        (fun destination => B destination who)
  exact
    (G.expect_finkPureDeviationStateKernel_eq
      (germ.finkPointAt
        (valid (anytimeEpochIndex stage)))
      history.2 who action
      (fun destination => B destination who)).symm

omit [DecidableEq G.State] in
/-- Exact Bellman meaning of the history charge: actual unilateral
stage-plus-`B` continuation equals the prescribed Fink quantity plus the
expected full-owner raw charge. -/
theorem playerOwnedCalendar_bellmanAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          history who +
        G.historyContinuationEU
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          (fun _ nextHistory => B nextHistory.2 who)
          history =
      G.finkStageEU
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
        G.finkContinuationEU B
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
        playerOwnedCalendarRawCharge
          germ B who startEpoch dev stage history := by
  rw [
    scheduledPlayerOwned_stageEU_eq_actionRows
      germ who startEpoch valid dev history,
    scheduledPlayerOwned_continuation_eq_actionRows
      germ B who startEpoch valid dev history,
    ← expect_add]
  unfold playerOwnedCalendarRawCharge playerOwnedCalendarScale
    calendarScale
  calc
    expect (dev stage history) (fun action =>
        germ.playerOwnedOccupationStageEUAt
              (valid (anytimeEpochIndex stage)) who
              (.inr (history.2, action)) +
          expect
            (germ.finkOwnerActualOccupationKernelAt
              (valid (anytimeEpochIndex stage)) who
              (.inr (history.2, action)))
            (fun destination => B destination who)) =
      expect (dev stage history) (fun action =>
        (G.finkStageEU
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who +
          G.finkContinuationEU B
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who) +
          germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch
              (anytimeEpochIndex stage))
            (.inr (history.2, action))) := by
        apply congrArg (expect (dev stage history))
        funext action
        exact germ.playerOwnedOccupation_bellmanAccount_eq
          B (valid (anytimeEpochIndex stage)) who
            (.inr (history.2, action))
    _ =
      G.finkStageEU
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
        G.finkContinuationEU B
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
        expect (dev stage history) (fun action =>
          germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch
              (anytimeEpochIndex stage))
            (.inr (history.2, action))) := by
        rw [expect_add, expect_const]

/-- State-only punctured potential frozen throughout one calendar epoch. -/
def playerOwnedCalendarEpochPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch k : ℕ) :
    G.HistoryPotential :=
  fun _ history =>
    germ.puncturedPlayerOwnedPotentialAt B who P
      (shiftedUniversalEpochScale startEpoch k) history.2

/-- At every public history, the arbitrary behavior mixture's raw charge is
dominated by the actual one-step drift of the current epoch potential. -/
theorem playerOwnedCalendarRawCharge_le_epochPotentialDrift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    playerOwnedCalendarRawCharge
        germ B who startEpoch dev stage history ≤
      G.historyContinuationEU
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          (playerOwnedCalendarEpochPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          history -
        playerOwnedCalendarEpochPotential
          germ B who P startEpoch
            (anytimeEpochIndex stage) stage history := by
  let k := anytimeEpochIndex stage
  let C : G.State → ℝ :=
    germ.puncturedPlayerOwnedPotentialAt B who P
      (shiftedUniversalEpochScale startEpoch k)
  calc
    playerOwnedCalendarRawCharge
          germ B who startEpoch dev stage history =
        expect (dev stage history) fun action =>
          germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k)
            (.inr (history.2, action)) := by
      rfl
    _ ≤
        expect (dev stage history) fun action =>
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who) C
            (.inr (history.2, action)) :=
      expect_mono (dev stage history) _ _ fun action =>
        hcharge k (.inr (history.2, action))
    _ =
        expect (dev stage history) (fun action =>
          expect
              (germ.finkOwnerActualOccupationKernelAt
                (valid k) who (.inr (history.2, action)))
              C - C history.2) := by
      rfl
    _ =
        expect (dev stage history) (fun action =>
          expect
              (germ.finkOwnerActualOccupationKernelAt
                (valid k) who (.inr (history.2, action)))
              C) - C history.2 := by
      rw [expect_sub, expect_const]
    _ =
        expect
            (LowerValueJet.behaviorStateStep
              (scheduledPlayerOwnedFinkDeviationProfile
                germ who startEpoch valid dev)
              history)
            C - C history.2 := by
      rw [
        behaviorStateStep_scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev history]
      unfold playerOwnedCalendarMixedStep
      rw [expect_bind]
    _ =
        G.historyContinuationEU
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            (playerOwnedCalendarEpochPotential
              germ B who P startEpoch k)
            history -
          playerOwnedCalendarEpochPotential
            germ B who P startEpoch k stage history := by
      unfold historyContinuationEU LowerValueJet.behaviorStateStep
        playerOwnedCalendarEpochPotential
      rw [expect_bind]

/-- Expected raw charge at one stage is bounded by the increment of the
fixed potential of that stage's epoch under the same root history law. -/
theorem expected_playerOwnedCalendarRawCharge_le_epochPotentialIncrement
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (stage : ℕ) :
    G.expectedHistoryValue
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial
        (playerOwnedCalendarRawCharge
          germ B who startEpoch dev)
        stage ≤
      G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarEpochPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          (stage + 1) -
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarEpochPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          stage := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let raw :=
    playerOwnedCalendarRawCharge germ B who startEpoch dev
  let value :=
    playerOwnedCalendarEpochPotential
      germ B who P startEpoch (anytimeEpochIndex stage)
  rw [G.expectedHistoryValue_succ]
  unfold expectedHistoryValue
  rw [← expect_sub]
  exact expect_mono (G.histDist profile initial stage) _ _
    (playerOwnedCalendarRawCharge_le_epochPotentialDrift
      germ B who P startEpoch valid hcharge dev)

private theorem expected_playerOwnedCalendarEpochPotential_upper
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (k stage : ℕ) :
    G.expectedHistoryValue
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial
        (playerOwnedCalendarEpochPotential
          germ B who P startEpoch k)
        stage ≤
      finiteStatePotentialBound
        (germ.puncturedPlayerOwnedPotentialAt B who P
          (shiftedUniversalEpochScale startEpoch k)) := by
  unfold expectedHistoryValue playerOwnedCalendarEpochPotential
  calc
    expect
        (G.histDist
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage)
        (fun history =>
          germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k) history.2) ≤
      expect
        (G.histDist
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage)
        (fun _ =>
          finiteStatePotentialBound
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))) := by
        apply expect_mono
        intro history
        have habs :
            |germ.puncturedPlayerOwnedPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k) history.2| ≤
              finiteStatePotentialBound
                (germ.puncturedPlayerOwnedPotentialAt B who P
                  (shiftedUniversalEpochScale startEpoch k)) := by
          simpa [statePotentialAccount] using
            abs_statePotentialAccount_le_finiteStatePotentialBound
              (germ.puncturedPlayerOwnedPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k))
              (fun _ => history.2) 0
        exact (le_abs_self _).trans habs
    _ =
        finiteStatePotentialBound
          (germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) := by
      rw [expect_const]

private theorem expected_playerOwnedCalendarEpochPotential_lower
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (k stage : ℕ) :
    -finiteStatePotentialBound
        (germ.puncturedPlayerOwnedPotentialAt B who P
          (shiftedUniversalEpochScale startEpoch k)) ≤
      G.expectedHistoryValue
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial
        (playerOwnedCalendarEpochPotential
          germ B who P startEpoch k)
        stage := by
  unfold expectedHistoryValue playerOwnedCalendarEpochPotential
  calc
    -finiteStatePotentialBound
          (germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) =
      expect
        (G.histDist
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage)
        (fun _ =>
          -finiteStatePotentialBound
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))) := by
        rw [expect_const]
    _ ≤
      expect
        (G.histDist
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage)
        (fun history =>
          germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k) history.2) := by
        apply expect_mono
        intro history
        have habs :
            |germ.puncturedPlayerOwnedPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k) history.2| ≤
              finiteStatePotentialBound
                (germ.puncturedPlayerOwnedPotentialAt B who P
                  (shiftedUniversalEpochScale startEpoch k)) := by
          simpa [statePotentialAccount] using
            abs_statePotentialAccount_le_finiteStatePotentialBound
              (germ.puncturedPlayerOwnedPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k))
              (fun _ => history.2) 0
        exact neg_le_of_abs_le habs

/-- Every prefix of one calendar epoch has expected full-owner raw charge
bounded by that epoch's punctured-potential bill. -/
theorem expected_playerOwnedCalendarEpochCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (k horizon : ℕ)
    (hhorizon : horizon ≤ anytimeEpochLength k) :
    ∑ offset ∈ Finset.range horizon,
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarRawCharge
            germ B who startEpoch dev)
          (epochStart anytimeEpochLength k + offset) ≤
      playerOwnedPotentialEpochBudget
        germ B who P startEpoch k := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let raw :=
    playerOwnedCalendarRawCharge germ B who startEpoch dev
  let value :=
    playerOwnedCalendarEpochPotential
      germ B who P startEpoch k
  let start := epochStart anytimeEpochLength k
  have hindex (offset : ℕ) (hoffset : offset < horizon) :
      anytimeEpochIndex (start + offset) = k := by
    apply anytimeEpochIndex_eq
    · exact Nat.le_add_right start offset
    · rw [epochStart_succ]
      omega
  have hstep (offset : ℕ) (hoffset : offset < horizon) :
      G.expectedHistoryValue profile initial raw
          (start + offset) ≤
        G.expectedHistoryValue profile initial value
            (start + offset + 1) -
          G.expectedHistoryValue profile initial value
            (start + offset) := by
    have h :=
      expected_playerOwnedCalendarRawCharge_le_epochPotentialIncrement
        germ B who P startEpoch valid hcharge dev
          initial (start + offset)
    simpa only [hindex offset hoffset, profile, raw, value] using h
  calc
    ∑ offset ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial raw
            (start + offset) ≤
        ∑ offset ∈ Finset.range horizon,
          (G.expectedHistoryValue profile initial value
              (start + offset + 1) -
            G.expectedHistoryValue profile initial value
              (start + offset)) := by
      apply Finset.sum_le_sum
      intro offset hoffset
      exact hstep offset (Finset.mem_range.mp hoffset)
    _ =
        G.expectedHistoryValue profile initial value
            (start + horizon) -
          G.expectedHistoryValue profile initial value start := by
      let f : ℕ → ℝ := fun offset =>
        G.expectedHistoryValue profile initial value (start + offset)
      have htelescope := Finset.sum_range_sub' f horizon
      have hneg :
          (∑ offset ∈ Finset.range horizon,
              (f (offset + 1) - f offset)) =
            -(∑ offset ∈ Finset.range horizon,
              (f offset - f (offset + 1))) := by
        calc
          (∑ offset ∈ Finset.range horizon,
              (f (offset + 1) - f offset)) =
            ∑ offset ∈ Finset.range horizon,
              -(f offset - f (offset + 1)) := by
                apply Finset.sum_congr rfl
                intro offset _
                ring
          _ =
            -(∑ offset ∈ Finset.range horizon,
              (f offset - f (offset + 1))) :=
                Finset.sum_neg_distrib _
      change
        (∑ offset ∈ Finset.range horizon,
            (f (offset + 1) - f offset)) =
          f horizon - f 0
      rw [hneg, htelescope]
      dsimp only [f]
      ring
    _ ≤
        2 * finiteStatePotentialBound
          (germ.puncturedPlayerOwnedPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) := by
      have hupper :=
        expected_playerOwnedCalendarEpochPotential_upper
          germ B who P startEpoch valid dev
            initial k (start + horizon)
      have hlower :=
        expected_playerOwnedCalendarEpochPotential_lower
          germ B who P startEpoch valid dev initial k start
      change
        G.expectedHistoryValue profile initial value
              (start + horizon) -
            G.expectedHistoryValue profile initial value start ≤
          2 * finiteStatePotentialBound
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
      linarith
    _ =
        playerOwnedPotentialEpochBudget
          germ B who P startEpoch k := by
      rfl

private theorem expected_playerOwnedCompletedCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (K : ℕ) :
    ∑ stage ∈ Finset.range (epochStart anytimeEpochLength K),
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarRawCharge
            germ B who startEpoch dev)
          stage ≤
      ∑ k ∈ Finset.range K,
        playerOwnedPotentialEpochBudget
          germ B who P startEpoch k := by
  induction K with
  | zero =>
      simp [epochStart]
  | succ K inductionHypothesis =>
      rw [epochStart_succ, Finset.sum_range_add,
        Finset.sum_range_succ]
      exact add_le_add inductionHypothesis
        (expected_playerOwnedCalendarEpochCharge_le
          germ B who P startEpoch valid hcharge dev
            initial K (anytimeEpochLength K) le_rfl)

/-- Cumulative expected full player-owned raw charge under the actual
unilateral deviation's root public-history law. -/
def expectedPlayerOwnedBehaviorCalendarCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (scheduledPlayerOwnedFinkDeviationProfile
        germ who startEpoch valid dev)
      initial
      (playerOwnedCalendarRawCharge
        germ B who startEpoch dev)
      stage

/-- The actual full-history raw charge is bounded at every horizon by the
completed-plus-current player-owned calendar envelope. -/
theorem expectedPlayerOwnedBehaviorCalendarCharge_le_budget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) :
    expectedPlayerOwnedBehaviorCalendarCharge
        germ B who startEpoch valid dev initial T ≤
      playerOwnedPotentialCalendarBudget
        germ B who P startEpoch T := by
  let K := anytimeEpochIndex T
  let offset := anytimeEpochOffset T
  have htime :
      epochStart anytimeEpochLength K + offset = T :=
    anytimeEpochStart_add_offset T
  unfold expectedPlayerOwnedBehaviorCalendarCharge
    playerOwnedPotentialCalendarBudget
    completedAndCurrentEpochBudget
  change
    (∑ stage ∈ Finset.range T,
      G.expectedHistoryValue
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial
        (playerOwnedCalendarRawCharge
          germ B who startEpoch dev)
        stage) ≤
      (∑ k ∈ Finset.range K,
        playerOwnedPotentialEpochBudget
          germ B who P startEpoch k) +
        playerOwnedPotentialEpochBudget
          germ B who P startEpoch K
  rw [← htime, Finset.sum_range_add]
  apply add_le_add
  · exact expected_playerOwnedCompletedCharge_le
      germ B who P startEpoch valid hcharge dev initial K
  · exact expected_playerOwnedCalendarEpochCharge_le
      germ B who P startEpoch valid hcharge dev initial K offset
        (anytimeEpochOffset_le T)

/-- Every full player-owned scaled potential yields one universal-calendar
sublinear raw-charge account for every arbitrary unilateral behavior
strategy of that player. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_playerOwnedBehaviorCalendarAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (dev : G.BehaviorStrategy who) initial T,
        expectedPlayerOwnedBehaviorCalendarCharge
            germ B who startEpoch valid dev initial T ≤
          playerOwnedPotentialCalendarBudget
            germ B who P startEpoch T ∧
        IsAsymptoticallySublinear
          (playerOwnedPotentialCalendarBudget
            germ B who P startEpoch) := by
  obtain ⟨startEpoch, valid, hcharge⟩ :=
    exists_startEpoch_playerOwnedCharge_le_drift germ B who P
  refine ⟨startEpoch, valid, ?_⟩
  intro dev initial T
  exact
    ⟨expectedPlayerOwnedBehaviorCalendarCharge_le_budget
        germ B who P startEpoch valid hcharge dev initial T,
      playerOwnedPotentialCalendarBudget_sublinear
        germ B who P startEpoch⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
