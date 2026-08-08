/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.OccupationAlternative
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CalendarBellmanResidual
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BiasAlternative

/-!
# Finite bias as the canonical player-owned residual input

In the Poisson-solvable finite-bias branch, the fixed bias used by the
player-owned occupation alternative is

`seed.H - correction`.

The endpoint Poisson equation says exactly that this bias has zero
prescribed Bellman residual relative to the state-dependent endpoint value.
The corresponding moving residual is analytic, so its finite-coordinate
absolute envelope tends to zero along the analytic Bellman germ.

This is the analytic bridge into the full player-owned alternative.  It does
not turn the state-dependent endpoint target into the value at one public
entry; that still uses harmonic/excessive target transport.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

open Filter Math Math.OnlineLearning Math.PMFProduct Math.Probability
  Set Topology

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The fixed bias canonically associated with an endpoint Poisson
correction of a finite-bias seed. -/
def playerOwnedPoissonBias
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι) :
    G.State → Payoff ι :=
  seed.H - correction

omit [DecidableEq G.State] in
/-- Raw expected stage payoff at the endpoint equals its semantic Fink
expectation. -/
theorem rawStageCurve_zero_eq_finkStageEU
    (germ : G.AnalyticBellmanGerm) :
    germ.rawStageCurve 0 =
      fun source who =>
        G.finkStageEU germ.endpointFinkPoint source who := by
  ext source who
  unfold AnalyticBellmanGerm.rawStageCurve finkStageEU
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro action _
  rw [germ.rawProfileWeight_zero_eq_pmfPi_endpointProfile,
    germ.finkProfile_endpointFinkPoint]

/-- Moving prescribed Bellman residual of the fixed Poisson bias, measured
relative to the state-dependent endpoint value. -/
def playerOwnedPoissonResidualCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι) :
    ℝ → G.State → Payoff ι :=
  fun t source who =>
    germ.rawStageCurve t source who +
      germ.rawContinuationCurve
          (fun _ => seed.playerOwnedPoissonBias correction)
          t source who -
      seed.playerOwnedPoissonBias correction source who -
      germ.endpointValue source who

omit [DecidableEq G.State] in
/-- The moving prescribed residual is analytic in the germ parameter. -/
theorem analytic_playerOwnedPoissonResidualCurve
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι) :
    AnalyticAt ℝ
      (seed.playerOwnedPoissonResidualCurve correction) 0 := by
  rw [analyticAt_pi_iff]
  intro source
  rw [analyticAt_pi_iff]
  intro who
  exact
    (((analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp germ.analytic_rawStageCurve source)
          who).add
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (germ.analytic_rawContinuationCurve analyticAt_const)
            source) who)).sub
      analyticAt_const).sub analyticAt_const

omit [DecidableEq G.State] in
/-- At a positive germ parameter, the raw residual is the semantic
prescribed Fink stage-plus-bias residual. -/
theorem playerOwnedPoissonResidualCurve_eq_finkPointAt
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) :
    seed.playerOwnedPoissonResidualCurve correction t source who =
      G.finkStageEU (germ.finkPointAt ht) source who +
        G.finkContinuationEU
          (seed.playerOwnedPoissonBias correction)
          (germ.finkPointAt ht) source who -
        seed.playerOwnedPoissonBias correction source who -
        germ.endpointValue source who := by
  unfold playerOwnedPoissonResidualCurve
  rw [germ.rawStageCurve_eq_finkStageEU ht,
    germ.rawContinuationCurve_eq_finkContinuationEU
      (fun _ => seed.playerOwnedPoissonBias correction) ht]

omit [DecidableEq G.State] in
/-- More generally, the harmonic obstruction in the finite-bias forcing
decomposition is exactly the negative endpoint residual of
`seed.H - correction`.  Thus only the zero-obstruction (Poisson) branch
gives a vanishing prescribed residual by this canonical construction. -/
theorem playerOwnedPoissonResidualCurve_zero_eq_neg_obstruction
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (obstruction correction : G.State → Payoff ι)
    (hforcing :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        obstruction -
          G.finkContinuationResidualVector
            correction germ.endpointFinkPoint) :
    seed.playerOwnedPoissonResidualCurve correction 0 =
      -obstruction := by
  funext source who
  have hcoordinate :=
    congrFun (congrFun hforcing source) who
  unfold playerOwnedPoissonResidualCurve
  change
    germ.rawStageCurve 0 source who +
          germ.rawContinuationCurve
              (fun _ => seed.playerOwnedPoissonBias correction)
              0 source who -
        seed.playerOwnedPoissonBias correction source who -
      germ.endpointValue source who =
        (-obstruction) source who
  rw [rawStageCurve_zero_eq_finkStageEU germ,
    germ.rawContinuationCurve_zero_eq_finkContinuationEU]
  change
    G.finkStageEU germ.endpointFinkPoint source who +
          G.finkContinuationEU
            (seed.playerOwnedPoissonBias correction)
            germ.endpointFinkPoint source who -
        seed.playerOwnedPoissonBias correction source who -
      germ.endpointValue source who =
        -obstruction source who
  unfold finkBellmanForcingVector
    finkContinuationResidualVector
    finkContinuationResidual at hcoordinate
  unfold playerOwnedPoissonBias
  rw [G.finkContinuationEU_sub]
  simp only [Pi.sub_apply] at hcoordinate ⊢
  linarith

omit [DecidableEq G.State] in
/-- The endpoint Poisson equation annihilates the prescribed residual of
the canonical fixed bias. -/
theorem playerOwnedPoissonResidualCurve_zero
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint) :
    seed.playerOwnedPoissonResidualCurve correction 0 = 0 := by
  have hforcing :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        (0 : G.State → Payoff ι) -
          G.finkContinuationResidualVector
            correction germ.endpointFinkPoint := by
    simpa using hPoisson
  simpa using
    seed.playerOwnedPoissonResidualCurve_zero_eq_neg_obstruction
      0 correction hforcing

/-- Finite-coordinate absolute envelope of the moving prescribed
residual. -/
def playerOwnedPoissonResidualEnvelope
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (t : ℝ) : ℝ :=
  ∑ pair : G.State × ι,
    |seed.playerOwnedPoissonResidualCurve
      correction t pair.1 pair.2|

omit [DecidableEq G.State] in
/-- The endpoint Poisson equation makes the moving prescribed residual
uniformly vanish over the finite state-player family. -/
theorem tendsto_playerOwnedPoissonResidualEnvelope
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint) :
    Tendsto
      (seed.playerOwnedPoissonResidualEnvelope correction)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  unfold playerOwnedPoissonResidualEnvelope
  have hzero :=
    seed.playerOwnedPoissonResidualCurve_zero correction hPoisson
  have hcontinuous :=
    (seed.analytic_playerOwnedPoissonResidualCurve correction).continuousAt
  have total :=
    tendsto_finsetSum (s := Finset.univ)
      (fun pair : G.State × ι => fun _ => by
        have hcoordinate :
            Tendsto
                (fun t =>
                  seed.playerOwnedPoissonResidualCurve
                    correction t pair.1 pair.2)
                (𝓝 (0 : ℝ))
                (𝓝
                  (seed.playerOwnedPoissonResidualCurve
                    correction 0 pair.1 pair.2)) :=
          ((tendsto_pi_nhds.mp
            (tendsto_pi_nhds.mp hcontinuous pair.1)) pair.2)
        have hcoordinate_zero :
            seed.playerOwnedPoissonResidualCurve
                correction 0 pair.1 pair.2 = 0 := by
          simpa only [Pi.zero_apply] using
            congrFun (congrFun hzero pair.1) pair.2
        simpa only [hcoordinate_zero, abs_zero] using hcoordinate.abs)
  simpa using total

omit [DecidableEq G.State] in
/-- Every residual coordinate is bounded by the common finite envelope. -/
theorem abs_playerOwnedPoissonResidualCurve_le_envelope
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (t : ℝ) (source : G.State) (who : ι) :
    |seed.playerOwnedPoissonResidualCurve
        correction t source who| ≤
      seed.playerOwnedPoissonResidualEnvelope correction t := by
  unfold playerOwnedPoissonResidualEnvelope
  exact Finset.single_le_sum
    (fun pair _ =>
      abs_nonneg
        (seed.playerOwnedPoissonResidualCurve
          correction t pair.1 pair.2))
    (Finset.mem_univ (source, who))

private theorem tendsto_finiteBias_anytimeEpochIndex :
    Tendsto anytimeEpochIndex atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards
    [eventually_ge_atTop
      (epochStart anytimeEpochLength K)] with stage hstage
  exact anytimeEpochIndex_ge_of_start_le hstage

private theorem tendsto_finiteBias_playerOwnedCalendarScale
    (startEpoch : ℕ) :
    Tendsto (playerOwnedCalendarScale startEpoch)
      atTop (𝓝 0) :=
  (tendsto_shiftedUniversalEpochScale startEpoch).comp
    tendsto_finiteBias_anytimeEpochIndex

/-- Cumulative absolute prescribed-residual envelope along the shifted
universal calendar. -/
def playerOwnedPoissonResidualCalendarBudget
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (startEpoch T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    seed.playerOwnedPoissonResidualEnvelope correction
      (playerOwnedCalendarScale startEpoch stage)

omit [DecidableEq G.State] in
/-- The shifted-calendar cumulative Poisson residual envelope is
asymptotically sublinear. -/
theorem playerOwnedPoissonResidualCalendarBudget_sublinear
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (startEpoch : ℕ) :
    IsAsymptoticallySublinear
      (seed.playerOwnedPoissonResidualCalendarBudget
        correction startEpoch) := by
  let stageResidual : ℕ → ℝ := fun stage =>
    seed.playerOwnedPoissonResidualEnvelope correction
      (playerOwnedCalendarScale startEpoch stage)
  have hstage :
      Tendsto stageResidual atTop (𝓝 0) := by
    exact
      (seed.tendsto_playerOwnedPoissonResidualEnvelope
          correction hPoisson).comp
        (tendsto_finiteBias_playerOwnedCalendarScale startEpoch)
  rw [isAsymptoticallySublinear_iff_tendsto]
  simpa [playerOwnedPoissonResidualCalendarBudget, stageResidual]
    using hstage.cesaro

omit [DecidableEq G.State] in
/-- The fixed-entry residual used by the calendar payoff account is the
state-target Poisson residual plus the current-minus-entry endpoint value.
-/
theorem
    playerOwnedCalendarPrescribedBellmanResidual_eq_poisson_add_targetTransport
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
    playerOwnedCalendarPrescribedBellmanResidual
        germ (seed.playerOwnedPoissonBias correction)
        who startEpoch valid
        (germ.endpointValue entry who)
        stage history =
      seed.playerOwnedPoissonResidualCurve correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who +
        (germ.endpointValue history.2 who -
          germ.endpointValue entry who) := by
  have hsemantic :=
    seed.playerOwnedPoissonResidualCurve_eq_finkPointAt
      correction (valid (anytimeEpochIndex stage)) history.2 who
  have hsemantic' :
      seed.playerOwnedPoissonResidualCurve correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who =
        G.finkStageEU
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2 who +
            G.finkContinuationEU
              (seed.playerOwnedPoissonBias correction)
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2 who -
            seed.playerOwnedPoissonBias correction history.2 who -
          germ.endpointValue history.2 who := by
    simpa only [playerOwnedCalendarScale, calendarScale] using hsemantic
  unfold playerOwnedCalendarPrescribedBellmanResidual
  change
    G.finkStageEU
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who +
        G.finkContinuationEU
          (seed.playerOwnedPoissonBias correction)
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2 who -
        seed.playerOwnedPoissonBias correction history.2 who -
        germ.endpointValue entry who =
      seed.playerOwnedPoissonResidualCurve correction
          (playerOwnedCalendarScale startEpoch stage)
          history.2 who +
        (germ.endpointValue history.2 who -
          germ.endpointValue entry who)
  linarith [hsemantic']

/-- Cumulative expected current-minus-entry endpoint value under one
unilateral calendar deviation.  This is the target-transport term not paid
by the absolute Poisson residual envelope. -/
def expectedPlayerOwnedCalendarEndpointTargetTransport
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
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
      (fun _ history =>
        germ.endpointValue history.2 who -
          germ.endpointValue entry who)
      stage

omit [DecidableEq G.State] in
/-- After paying the sublinear absolute Poisson envelope, the accumulated
endpoint target-transport term is the only residual-budget obligation left
by the fixed-entry player-owned calendar account. -/
theorem sum_expected_playerOwnedCalendarPrescribedBellmanResidual_le
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) :
    (∑ stage ∈ Finset.range T,
      G.expectedHistoryValue
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial
        (playerOwnedCalendarPrescribedBellmanResidual
          germ (seed.playerOwnedPoissonBias correction)
          who startEpoch valid
          (germ.endpointValue entry who))
        stage) ≤
      seed.playerOwnedPoissonResidualCalendarBudget
          correction startEpoch T +
        expectedPlayerOwnedCalendarEndpointTargetTransport
          germ who entry startEpoch valid dev initial T := by
  unfold playerOwnedPoissonResidualCalendarBudget
    expectedPlayerOwnedCalendarEndpointTargetTransport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro stage _
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let residual : G.HistoryPotential :=
    playerOwnedCalendarPrescribedBellmanResidual
      germ (seed.playerOwnedPoissonBias correction)
      who startEpoch valid (germ.endpointValue entry who)
  let transport : G.HistoryPotential := fun _ history =>
    germ.endpointValue history.2 who -
      germ.endpointValue entry who
  have pointwise :
      ∀ history : G.Hist stage,
        residual stage history =
          seed.playerOwnedPoissonResidualCurve correction
              (playerOwnedCalendarScale startEpoch stage)
              history.2 who +
            transport stage history := by
    intro history
    exact
      seed.playerOwnedCalendarPrescribedBellmanResidual_eq_poisson_add_targetTransport
        correction who entry startEpoch valid history
  calc
    G.expectedHistoryValue profile initial residual stage =
        G.expectedHistoryValue profile initial
            (fun _ history =>
              seed.playerOwnedPoissonResidualCurve correction
                  (playerOwnedCalendarScale startEpoch stage)
                  history.2 who)
            stage +
          G.expectedHistoryValue profile initial transport stage := by
      unfold expectedHistoryValue
      rw [← expect_add]
      apply congrArg (expect (G.histDist profile initial stage))
      funext history
      exact pointwise history
    _ ≤
        seed.playerOwnedPoissonResidualEnvelope correction
            (playerOwnedCalendarScale startEpoch stage) +
          G.expectedHistoryValue profile initial transport stage := by
      have hresidual :
          G.expectedHistoryValue profile initial
              (fun _ history =>
                seed.playerOwnedPoissonResidualCurve correction
                  (playerOwnedCalendarScale startEpoch stage)
                  history.2 who)
              stage ≤
            seed.playerOwnedPoissonResidualEnvelope correction
              (playerOwnedCalendarScale startEpoch stage) := by
        unfold expectedHistoryValue
        calc
          expect (G.histDist profile initial stage)
                (fun history =>
                  seed.playerOwnedPoissonResidualCurve correction
                    (playerOwnedCalendarScale startEpoch stage)
                    history.2 who) ≤
              expect (G.histDist profile initial stage)
                (fun _ =>
                  seed.playerOwnedPoissonResidualEnvelope correction
                    (playerOwnedCalendarScale startEpoch stage)) := by
                apply expect_mono
                intro history
                exact
                  (le_abs_self
                      (seed.playerOwnedPoissonResidualCurve correction
                        (playerOwnedCalendarScale startEpoch stage)
                        history.2 who)).trans
                    (seed.abs_playerOwnedPoissonResidualCurve_le_envelope
                      correction
                      (playerOwnedCalendarScale startEpoch stage)
                      history.2 who)
          _ =
              seed.playerOwnedPoissonResidualEnvelope correction
                (playerOwnedCalendarScale startEpoch stage) := by
            rw [expect_const]
      linarith

/-- In the Poisson-solvable finite-bias branch, the synchronized full-owner
charged-flow alternative is available at the canonical fixed bias. -/
theorem
    playerOwnedPositiveChargedCirculation_or_commonScaledPotential_of_poisson
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι) :
    (∃ who,
      Nonempty
        (AnalyticPositiveChargedCirculation
          (germ.rawOwnerAnalyticOccupationColumn who)
          (germ.rawPlayerOwnedOccupationCharge
            (seed.playerOwnedPoissonBias correction) who))) ∨
    Nonempty
      (AnalyticOwnerScaledChargedOccupationPotential
        (fun who => OwnerOccupationIndex G who)
        (fun who => germ.rawOwnerAnalyticOccupationColumn who)
        (fun who =>
          germ.rawPlayerOwnedOccupationCharge
            (seed.playerOwnedPoissonBias correction) who)) :=
  germ.exists_playerOwnedPositiveChargedCirculation_or_commonScaledPotential
    (seed.playerOwnedPoissonBias correction)

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
