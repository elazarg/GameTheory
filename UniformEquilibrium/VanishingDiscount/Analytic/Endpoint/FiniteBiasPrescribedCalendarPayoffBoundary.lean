/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedResidualBridge

/-!
# Prescribed-calendar payoff boundary in the finite-bias branch

The player-owned calendar account controls unilateral deviations.  Uniform
equilibrium also requires the prescribed calendar itself to realize the
endpoint target from the chosen public entry.

This file records the exact prescribed-play identity.  Its four terms are:

* the endpoint target;
* the telescope of the canonical Poisson bias;
* the moving Poisson residual;
* the baseline current-state versus entry-state endpoint transport.

The Poisson equation makes the absolute residual envelope sublinear.  The
bias telescope is uniformly bounded.  Thus the only separate on-path
boundary is two-sided sublinearity of the prescribed baseline endpoint
transport.  No target-realization conclusion is assumed in that boundary.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

open Filter Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Prescribed play on the shifted universal calendar. -/
def prescribedPlayerOwnedFinkCalendarProfile
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius) :
    G.BehaviorProfile :=
  G.scheduledMarkovBehaviorProfile
    (fun stage source =>
      G.finkProfile
        (germ.finkPointAt (valid (anytimeEpochIndex stage)))
        source)

/-- Signed cumulative moving Poisson residual under prescribed play. -/
def expectedPrescribedCalendarPoissonResidual
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (prescribedPlayerOwnedFinkCalendarProfile
        germ startEpoch valid)
      entry
      (fun _ history =>
        seed.playerOwnedPoissonResidualCurve correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who)
      stage

/-- Cumulative current-state minus entry-state endpoint target under
prescribed calendar play. -/
def expectedPrescribedCalendarEndpointTargetTransport
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (prescribedPlayerOwnedFinkCalendarProfile
        germ startEpoch valid)
      entry
      (fun _ history =>
        germ.endpointValue history.2 who -
          germ.endpointValue entry who)
      stage

omit [DecidableEq G.State] in
/-- Exact one-step prescribed Bellman identity at the canonical Poisson
bias. -/
theorem prescribedCalendar_poissonBellman_eq
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          history who +
        G.historyContinuationEU
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          (fun _ nextHistory =>
            seed.playerOwnedPoissonBias correction
              nextHistory.2 who)
          history =
      germ.endpointValue entry who +
        seed.playerOwnedPoissonBias correction history.2 who +
        seed.playerOwnedPoissonResidualCurve correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who +
        (germ.endpointValue history.2 who -
          germ.endpointValue entry who) := by
  have hsemantic :=
    seed.playerOwnedPoissonResidualCurve_eq_finkPointAt
      correction (valid (anytimeEpochIndex stage)) history.2 who
  have hstage :
      G.stageEUAt
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          history who =
        G.finkStageEU
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who := by
    unfold prescribedPlayerOwnedFinkCalendarProfile stageEUAt
    rw [G.stageActionDist_scheduledMarkovBehaviorProfile]
    rfl
  have hcontinuation :
      G.historyContinuationEU
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          (fun _ nextHistory =>
            seed.playerOwnedPoissonBias correction
              nextHistory.2 who)
          history =
        G.finkContinuationEU
          (seed.playerOwnedPoissonBias correction)
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who := by
    unfold prescribedPlayerOwnedFinkCalendarProfile
      historyContinuationEU finkContinuationEU
    rw [G.stageActionDist_scheduledMarkovBehaviorProfile]
  rw [hstage, hcontinuation]
  simpa only [playerOwnedCalendarScale, calendarScale] using
    (show
      G.finkStageEU
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who +
          G.finkContinuationEU
            (seed.playerOwnedPoissonBias correction)
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who =
        germ.endpointValue entry who +
          seed.playerOwnedPoissonBias correction history.2 who +
          seed.playerOwnedPoissonResidualCurve correction
            (shiftedUniversalEpochScale startEpoch
              (anytimeEpochIndex stage))
            history.2 who +
          (germ.endpointValue history.2 who -
            germ.endpointValue entry who) by
      linarith [hsemantic])

omit [DecidableEq G.State] in
/-- Exact finite-horizon prescribed payoff identity. -/
theorem sum_expectedStagePayoff_prescribedCalendar_eq
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (T : ℕ) :
    (∑ stage ∈ Finset.range T,
        G.expectedStagePayoff
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          entry stage who) =
      (T : ℝ) * germ.endpointValue entry who +
        seed.playerOwnedPoissonBias correction entry who -
        G.expectedHistoryValue
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          entry
          (fun _ history =>
            seed.playerOwnedPoissonBias correction
              history.2 who)
          T +
        seed.expectedPrescribedCalendarPoissonResidual
          correction who entry startEpoch valid T +
        expectedPrescribedCalendarEndpointTargetTransport
          germ who entry startEpoch valid T := by
  let profile :=
    prescribedPlayerOwnedFinkCalendarProfile
      germ startEpoch valid
  let bias : G.HistoryPotential := fun _ history =>
    seed.playerOwnedPoissonBias correction history.2 who
  let residual : G.HistoryPotential := fun stage history =>
    seed.playerOwnedPoissonResidualCurve correction
      (playerOwnedCalendarScale startEpoch stage)
      history.2 who
  let transport : G.HistoryPotential := fun _ history =>
    germ.endpointValue history.2 who -
      germ.endpointValue entry who
  have step (stage : ℕ) :
      G.expectedStagePayoff profile entry stage who =
        germ.endpointValue entry who +
          G.expectedHistoryValue profile entry bias stage -
          G.expectedHistoryValue profile entry bias (stage + 1) +
          G.expectedHistoryValue profile entry residual stage +
          G.expectedHistoryValue profile entry transport stage := by
    have pointwise :
        ∀ history : G.Hist stage,
          G.stageEUAt profile history who +
              G.historyContinuationEU profile bias history =
            germ.endpointValue entry who +
              bias stage history +
              residual stage history +
              transport stage history := by
      intro history
      exact
        seed.prescribedCalendar_poissonBellman_eq
          correction who entry startEpoch valid history
    have averaged :=
      congrArg
        (expect (G.histDist profile entry stage))
        (funext pointwise)
    simp only [expect_add, expect_const] at averaged
    rw [← G.expectedHistoryValue_succ] at averaged
    change
      G.expectedStagePayoff profile entry stage who +
            G.expectedHistoryValue profile entry bias (stage + 1) =
        germ.endpointValue entry who +
          G.expectedHistoryValue profile entry bias stage +
          G.expectedHistoryValue profile entry residual stage +
          G.expectedHistoryValue profile entry transport stage at averaged
    linarith
  change
    (∑ stage ∈ Finset.range T,
        G.expectedStagePayoff profile entry stage who) =
      (T : ℝ) * germ.endpointValue entry who +
        seed.playerOwnedPoissonBias correction entry who -
        G.expectedHistoryValue profile entry bias T +
        (∑ stage ∈ Finset.range T,
          G.expectedHistoryValue profile entry residual stage) +
        (∑ stage ∈ Finset.range T,
          G.expectedHistoryValue profile entry transport stage)
  induction T with
  | zero =>
      simp [profile, bias, expectedHistoryValue, emptyHist]
  | succ T inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        Finset.sum_range_succ, Finset.sum_range_succ, step T]
      push_cast
      ring

omit [DecidableEq G.State] in
/-- Exact finite-average form of the prescribed payoff identity. -/
theorem finiteAveragePayoff_prescribedCalendar_eq
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff entry T
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          who =
      germ.endpointValue entry who +
        (seed.playerOwnedPoissonBias correction entry who -
            G.expectedHistoryValue
              (prescribedPlayerOwnedFinkCalendarProfile
                germ startEpoch valid)
              entry
              (fun _ history =>
                seed.playerOwnedPoissonBias correction
                  history.2 who)
              T +
            seed.expectedPrescribedCalendarPoissonResidual
              correction who entry startEpoch valid T +
            expectedPrescribedCalendarEndpointTargetTransport
              germ who entry startEpoch valid T) /
          (T : ℝ) := by
  have hsum :=
    seed.sum_expectedStagePayoff_prescribedCalendar_eq
      correction who entry startEpoch valid T
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff, hsum]
  have hTreal : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT)
  field_simp [hTreal]
  ring

omit [DecidableEq G.State] in
/-- The signed cumulative prescribed Poisson residual is bounded in
absolute value by its canonical absolute envelope. -/
theorem abs_expectedPrescribedCalendarPoissonResidual_le
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (T : ℕ) :
    |seed.expectedPrescribedCalendarPoissonResidual
        correction who entry startEpoch valid T| ≤
      seed.playerOwnedPoissonResidualCalendarBudget
        correction startEpoch T := by
  unfold expectedPrescribedCalendarPoissonResidual
    playerOwnedPoissonResidualCalendarBudget
  calc
    |∑ stage ∈ Finset.range T,
        G.expectedHistoryValue
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          entry
          (fun _ history =>
            seed.playerOwnedPoissonResidualCurve correction
              (playerOwnedCalendarScale startEpoch stage)
              history.2 who)
          stage| ≤
        ∑ stage ∈ Finset.range T,
          |G.expectedHistoryValue
            (prescribedPlayerOwnedFinkCalendarProfile
              germ startEpoch valid)
            entry
            (fun _ history =>
              seed.playerOwnedPoissonResidualCurve correction
                (playerOwnedCalendarScale startEpoch stage)
                history.2 who)
            stage| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ stage ∈ Finset.range T,
          seed.playerOwnedPoissonResidualEnvelope correction
            (playerOwnedCalendarScale startEpoch stage) := by
      apply Finset.sum_le_sum
      intro stage _
      unfold expectedHistoryValue
      apply abs_expect_le_of_abs_le
      intro history
      exact
        seed.abs_playerOwnedPoissonResidualCurve_le_envelope
          correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who

omit [DecidableEq G.State] in
/-- Exact finite-horizon error bound.  The only term not already bounded
or known sublinear from the Poisson equation is the absolute prescribed
baseline endpoint transport. -/
theorem abs_finiteAveragePayoff_prescribedCalendar_sub_endpointValue_le
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    {T : ℕ} (hT : 0 < T) :
    |G.finiteAveragePayoff entry T
          (prescribedPlayerOwnedFinkCalendarProfile
            germ startEpoch valid)
          who -
        germ.endpointValue entry who| ≤
      (2 * finiteStatePotentialBound
            (fun state =>
              seed.playerOwnedPoissonBias correction state who) +
          seed.playerOwnedPoissonResidualCalendarBudget
            correction startEpoch T +
          |expectedPrescribedCalendarEndpointTargetTransport
            germ who entry startEpoch valid T|) /
        (T : ℝ) := by
  let profile :=
    prescribedPlayerOwnedFinkCalendarProfile
      germ startEpoch valid
  let bias : G.HistoryPotential := fun _ history =>
    seed.playerOwnedPoissonBias correction history.2 who
  let biasBound :=
    finiteStatePotentialBound
      (fun state =>
        seed.playerOwnedPoissonBias correction state who)
  have hentry :
      |seed.playerOwnedPoissonBias correction entry who| ≤
        biasBound := by
    simpa [biasBound, statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        (fun state =>
          seed.playerOwnedPoissonBias correction state who)
        (fun _ => entry) 0
  have hfinal :
      |G.expectedHistoryValue profile entry bias T| ≤
        biasBound := by
    apply abs_expect_le_of_abs_le
    intro history
    simpa [bias, biasBound, statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        (fun state =>
          seed.playerOwnedPoissonBias correction state who)
        (fun _ => history.2) 0
  have hbias :
      |seed.playerOwnedPoissonBias correction entry who -
          G.expectedHistoryValue profile entry bias T| ≤
        2 * biasBound := by
    calc
      |seed.playerOwnedPoissonBias correction entry who -
          G.expectedHistoryValue profile entry bias T| ≤
          |seed.playerOwnedPoissonBias correction entry who| +
            |G.expectedHistoryValue profile entry bias T| :=
        abs_sub _ _
      _ ≤ 2 * biasBound := by linarith
  have hresidual :=
    seed.abs_expectedPrescribedCalendarPoissonResidual_le
      correction who entry startEpoch valid T
  have hnumerator :
      |seed.playerOwnedPoissonBias correction entry who -
            G.expectedHistoryValue profile entry bias T +
          seed.expectedPrescribedCalendarPoissonResidual
            correction who entry startEpoch valid T +
          expectedPrescribedCalendarEndpointTargetTransport
            germ who entry startEpoch valid T| ≤
        2 * biasBound +
          seed.playerOwnedPoissonResidualCalendarBudget
            correction startEpoch T +
          |expectedPrescribedCalendarEndpointTargetTransport
            germ who entry startEpoch valid T| := by
    calc
      |seed.playerOwnedPoissonBias correction entry who -
              G.expectedHistoryValue profile entry bias T +
            seed.expectedPrescribedCalendarPoissonResidual
              correction who entry startEpoch valid T +
            expectedPrescribedCalendarEndpointTargetTransport
              germ who entry startEpoch valid T| ≤
          |seed.playerOwnedPoissonBias correction entry who -
              G.expectedHistoryValue profile entry bias T| +
            |seed.expectedPrescribedCalendarPoissonResidual
              correction who entry startEpoch valid T| +
            |expectedPrescribedCalendarEndpointTargetTransport
              germ who entry startEpoch valid T| := by
        calc
          |seed.playerOwnedPoissonBias correction entry who -
                  G.expectedHistoryValue profile entry bias T +
                seed.expectedPrescribedCalendarPoissonResidual
                  correction who entry startEpoch valid T +
                expectedPrescribedCalendarEndpointTargetTransport
                  germ who entry startEpoch valid T| ≤
              |seed.playerOwnedPoissonBias correction entry who -
                  G.expectedHistoryValue profile entry bias T +
                seed.expectedPrescribedCalendarPoissonResidual
                  correction who entry startEpoch valid T| +
                |expectedPrescribedCalendarEndpointTargetTransport
                  germ who entry startEpoch valid T| :=
            abs_add_le _ _
          _ ≤
              (|seed.playerOwnedPoissonBias correction entry who -
                  G.expectedHistoryValue profile entry bias T| +
                |seed.expectedPrescribedCalendarPoissonResidual
                  correction who entry startEpoch valid T|) +
                |expectedPrescribedCalendarEndpointTargetTransport
                  germ who entry startEpoch valid T| := by
            gcongr
            exact abs_add_le _ _
      _ ≤
          2 * biasBound +
            seed.playerOwnedPoissonResidualCalendarBudget
              correction startEpoch T +
            |expectedPrescribedCalendarEndpointTargetTransport
              germ who entry startEpoch valid T| := by
        linarith
  rw [seed.finiteAveragePayoff_prescribedCalendar_eq
    correction who entry startEpoch valid hT]
  simp only [add_sub_cancel_left, abs_div]
  have hTreal : (0 : ℝ) < T := by
    exact_mod_cast hT
  rw [abs_of_pos hTreal]
  exact div_le_div_of_nonneg_right hnumerator hTreal.le

/-- Minimal two-sided on-path boundary left by the exact identity: the
absolute prescribed baseline endpoint transport is asymptotically
sublinear, coordinatewise in the finite player set. -/
def HasSublinearPrescribedCalendarEndpointTargetTransport
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius) : Prop :=
  ∀ who,
    IsAsymptoticallySublinear fun T =>
      |expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid T|

omit [DecidableEq G.State] in
/-- The Poisson equation and the two-sided baseline transport boundary
give one horizon threshold at which prescribed play realizes every
player's endpoint target. -/
theorem
    eventually_all_abs_finiteAveragePayoff_prescribedCalendar_sub_endpointValue_le
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (transport :
      HasSublinearPrescribedCalendarEndpointTargetTransport
        germ entry startEpoch valid)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop,
      ∀ who,
        |G.finiteAveragePayoff entry T
              (prescribedPlayerOwnedFinkCalendarProfile
                germ startEpoch valid)
              who -
            germ.endpointValue entry who| ≤
          δ := by
  have hwho (who : ι) :
      ∀ᶠ T : ℕ in atTop,
        |G.finiteAveragePayoff entry T
              (prescribedPlayerOwnedFinkCalendarProfile
                germ startEpoch valid)
              who -
            germ.endpointValue entry who| ≤
          δ := by
    let totalBudget : ℕ → ℝ := fun T =>
      2 * finiteStatePotentialBound
          (fun state =>
            seed.playerOwnedPoissonBias correction state who) +
        seed.playerOwnedPoissonResidualCalendarBudget
          correction startEpoch T +
        |expectedPrescribedCalendarEndpointTargetTransport
          germ who entry startEpoch valid T|
    have htotal :
        IsAsymptoticallySublinear totalBudget := by
      apply IsAsymptoticallySublinear.add
      · apply IsAsymptoticallySublinear.add
        · exact IsAsymptoticallySublinear.const
            (2 * finiteStatePotentialBound
              (fun state =>
                seed.playerOwnedPoissonBias correction state who))
        · exact
            seed.playerOwnedPoissonResidualCalendarBudget_sublinear
              correction hPoisson startEpoch
      · exact transport who
    filter_upwards
        [htotal.eventually_average_le hδ,
          eventually_gt_atTop 0] with T haverage hT
    have hbound :=
      seed.abs_finiteAveragePayoff_prescribedCalendar_sub_endpointValue_le
        correction who entry startEpoch valid hT
    calc
      |G.finiteAveragePayoff entry T
            (prescribedPlayerOwnedFinkCalendarProfile
              germ startEpoch valid)
            who -
          germ.endpointValue entry who| ≤
          totalBudget T / (T : ℝ) := by
        simpa only [totalBudget] using hbound
      _ = (T : ℝ)⁻¹ * totalBudget T := by
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ δ := haverage
  exact Filter.eventually_all.mpr hwho

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
