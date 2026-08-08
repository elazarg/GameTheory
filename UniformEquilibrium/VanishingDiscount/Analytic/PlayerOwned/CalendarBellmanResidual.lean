/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.BehaviorCalendarAccount

/-!
# The residual left by a player-owned calendar account

The full player-owned potential pays the moving unilateral charge, but it
does not pay the prescribed Bellman residual.  This file records the exact
finite-horizon identity separating those two quantities.

Consequently, the existing sublinear charge budget gives a unilateral
average-payoff cap once the cumulative expected prescribed residual has its
own sublinear upper budget.  No such residual hypothesis is inferred from a
charged-occupation potential.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Prescribed Bellman residual at the parameter used by one calendar
stage.  It is the term not controlled by the player-owned occupation
charge. -/
def playerOwnedCalendarPrescribedBellmanResidual
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : ℝ) :
    G.HistoryPotential :=
  fun stage history =>
    G.finkStageEU
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
      G.finkContinuationEU B
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who -
      B history.2 who -
      target

omit [DecidableEq G.State] in
/-- Pointwise Bellman identity exposing the prescribed residual and the
player-owned charge as distinct terms. -/
theorem playerOwnedCalendar_bellmanResidualAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : ℝ)
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
      target + B history.2 who +
        playerOwnedCalendarPrescribedBellmanResidual
          germ B who startEpoch valid target stage history +
        playerOwnedCalendarRawCharge
          germ B who startEpoch dev stage history := by
  rw [playerOwnedCalendar_bellmanAccount_eq
    germ B who startEpoch valid dev history]
  unfold playerOwnedCalendarPrescribedBellmanResidual
  ring

omit [DecidableEq G.State] in
/-- Expected one-step form of the residual account under the deviating
profile's own public-history law. -/
theorem expected_playerOwnedCalendar_bellmanResidualAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : ℝ)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (stage : ℕ) :
    G.expectedStagePayoff
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage who +
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (fun _ history => B history.2 who)
          (stage + 1) =
      target +
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (fun _ history => B history.2 who)
          stage +
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarPrescribedBellmanResidual
            germ B who startEpoch valid target)
          stage +
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarRawCharge
            germ B who startEpoch dev)
          stage := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  have pointwise :
      ∀ history : G.Hist stage,
        G.stageEUAt profile history who +
            G.historyContinuationEU profile
              (fun _ nextHistory => B nextHistory.2 who) history =
          target + B history.2 who +
            playerOwnedCalendarPrescribedBellmanResidual
              germ B who startEpoch valid target stage history +
            playerOwnedCalendarRawCharge
              germ B who startEpoch dev stage history := by
    intro history
    exact playerOwnedCalendar_bellmanResidualAccount_eq
      germ B who startEpoch valid target dev history
  have averaged :=
    congrArg
      (expect
        (G.histDist profile initial stage))
      (funext pointwise)
  simp only [expect_add, expect_const] at averaged
  rw [← G.expectedHistoryValue_succ] at averaged
  exact averaged

omit [DecidableEq G.State] in
/-- Exact finite-horizon decomposition.  The endpoint term of `B`, the
cumulative prescribed residual, and the cumulative player-owned charge are
the only corrections to `T * target`. -/
theorem sum_expectedStagePayoff_playerOwnedCalendar_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : ℝ)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) :
    (∑ stage ∈ Finset.range T,
        G.expectedStagePayoff
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial stage who) =
      (T : ℝ) * target +
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (fun _ history => B history.2 who)
          0 -
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (fun _ history => B history.2 who)
          T +
        (∑ stage ∈ Finset.range T,
          G.expectedHistoryValue
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            initial
            (playerOwnedCalendarPrescribedBellmanResidual
              germ B who startEpoch valid target)
            stage) +
        expectedPlayerOwnedBehaviorCalendarCharge
          germ B who startEpoch valid dev initial T := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let value : G.HistoryPotential :=
    fun _ history => B history.2 who
  let residual :=
    playerOwnedCalendarPrescribedBellmanResidual
      germ B who startEpoch valid target
  let charge :=
    playerOwnedCalendarRawCharge
      germ B who startEpoch dev
  have step (stage : ℕ) :
      G.expectedStagePayoff profile initial stage who =
        target +
          G.expectedHistoryValue profile initial value stage -
          G.expectedHistoryValue profile initial value (stage + 1) +
          G.expectedHistoryValue profile initial residual stage +
          G.expectedHistoryValue profile initial charge stage := by
    have h :=
      expected_playerOwnedCalendar_bellmanResidualAccount_eq
        germ B who startEpoch valid target dev initial stage
    change
      G.expectedStagePayoff profile initial stage who +
            G.expectedHistoryValue profile initial value (stage + 1) =
        target +
          G.expectedHistoryValue profile initial value stage +
          G.expectedHistoryValue profile initial residual stage +
          G.expectedHistoryValue profile initial charge stage at h
    linarith
  induction T with
  | zero =>
      simp [expectedPlayerOwnedBehaviorCalendarCharge]
  | succ T inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis]
      rw [Finset.sum_range_succ]
      unfold expectedPlayerOwnedBehaviorCalendarCharge
      rw [Finset.sum_range_succ]
      rw [step T]
      push_cast
      ring

omit [DecidableEq G.State] in
/-- Conditional unilateral finite-average cap.  In this direct account
route, besides the player-owned charge budget, one separately bounds the
cumulative expected prescribed Bellman residual. -/
theorem finiteAveragePayoff_playerOwnedCalendar_le_target_add
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target chargeBudget residualBudget : ℝ)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) {T : ℕ}
    (hcharge :
      expectedPlayerOwnedBehaviorCalendarCharge
          germ B who startEpoch valid dev initial T ≤
        chargeBudget)
    (hresidual :
      (∑ stage ∈ Finset.range T,
        G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          initial
          (playerOwnedCalendarPrescribedBellmanResidual
            germ B who startEpoch valid target)
          stage) ≤
        residualBudget)
    (hT : 0 < T) :
    G.finiteAveragePayoff initial T
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        who ≤
      target +
        (2 * finiteStatePotentialBound (fun state => B state who) +
          chargeBudget + residualBudget) / (T : ℝ) := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let value : G.HistoryPotential :=
    fun _ history => B history.2 who
  have hvalue (stage : ℕ) :
      |G.expectedHistoryValue profile initial value stage| ≤
        finiteStatePotentialBound (fun state => B state who) := by
    apply abs_expect_le_of_abs_le
    intro history
    simpa [value, statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        (fun state => B state who) (fun _ => history.2) 0
  have hsum :=
    sum_expectedStagePayoff_playerOwnedCalendar_eq
      germ B who startEpoch valid target dev initial T
  have hraw :
      (∑ stage ∈ Finset.range T,
        G.expectedStagePayoff profile initial stage who) ≤
      (T : ℝ) * target +
        2 * finiteStatePotentialBound (fun state => B state who) +
        chargeBudget + residualBudget := by
    change
      (∑ stage ∈ Finset.range T,
          G.expectedStagePayoff profile initial stage who) =
        (T : ℝ) * target +
          G.expectedHistoryValue profile initial value 0 -
          G.expectedHistoryValue profile initial value T +
          (∑ stage ∈ Finset.range T,
            G.expectedHistoryValue profile initial
              (playerOwnedCalendarPrescribedBellmanResidual
                germ B who startEpoch valid target) stage) +
          expectedPlayerOwnedBehaviorCalendarCharge
            germ B who startEpoch valid dev initial T at hsum
    rw [hsum]
    have hzero := hvalue 0
    have hfinal := hvalue T
    rw [abs_le] at hzero hfinal
    linarith
  have hTreal : (0 : ℝ) < T := by
    exact_mod_cast hT
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  calc
    (T : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range T,
            G.expectedStagePayoff profile initial stage who ≤
        (T : ℝ)⁻¹ *
          ((T : ℝ) * target +
            2 * finiteStatePotentialBound (fun state => B state who) +
            chargeBudget + residualBudget) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hTreal.le)
    _ =
        target +
          (2 * finiteStatePotentialBound (fun state => B state who) +
            chargeBudget + residualBudget) / (T : ℝ) := by
      field_simp [ne_of_gt hTreal]
      ring

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
