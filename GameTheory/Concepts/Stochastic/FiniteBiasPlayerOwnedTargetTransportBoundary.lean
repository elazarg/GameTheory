/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasPlayerOwnedResidualBridge
import GameTheory.Concepts.Stochastic.PlayerNeutralOccupationHistoryAccount
import GameTheory.Concepts.Stochastic.PlayerOwnedCommonPotentialPayoffBoundary

/-!
# Target-transport boundary in the finite-bias player-owned branch

For the canonical Poisson bias, the analytic prescribed residual has an
explicit sublinear calendar envelope.  What remains is the accumulated
difference between the endpoint value at the current public state and at
the entry state.

This file names a uniform sublinear upper account for precisely that term.
It compiles such an account into the residual account and then into
simultaneous unilateral deviation caps.  No target-transport account is
inferred from endpoint harmonicity alone.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.PMFProduct Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace FiniteBiasSeed

/-- Uniform sublinear control of the current-minus-entry endpoint target
under every unilateral deviation against one prescribed Fink calendar. -/
structure PlayerOwnedCalendarEndpointTargetTransportAccount
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius) where
  budget : ι → ℕ → ℝ
  transport_le :
    ∀ (who : ι) (dev : G.BehaviorStrategy who) T,
      expectedPlayerOwnedCalendarEndpointTargetTransport
          germ who entry startEpoch valid dev entry T ≤
        budget who T
  sublinear :
    ∀ who, IsAsymptoticallySublinear (budget who)

/-- Every actual player-owned row is superharmonic for that owner's endpoint
value at every parameter used by the common calendar. -/
def IsMovingPlayerOwnedEndpointSuperharmonic
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius) : Prop :=
  ∀ (who : ι) k source (action : G.Act who),
    expect
        (germ.finkOwnerActualOccupationKernelAt
          (valid k) who (.inr (source, action)))
        (fun destination => germ.endpointValue destination who) ≤
      germ.endpointValue source who

omit [DecidableEq G.State] in
/-- Moving-row superharmonicity is preserved by an arbitrary behavioral
mixture of the deviating player's pure actions. -/
theorem historyContinuationEU_endpointValue_le_of_movingSuperharmonic
    {germ : G.AnalyticBellmanGerm}
    {startEpoch : ℕ}
    {valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius}
    (hsuper :
      IsMovingPlayerOwnedEndpointSuperharmonic
        germ startEpoch valid)
    (who : ι) (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    G.historyContinuationEU
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          (fun _ nextHistory =>
            germ.endpointValue nextHistory.2 who)
          history ≤
      germ.endpointValue history.2 who := by
  let profile :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  have hcontinuation :
      G.historyContinuationEU profile
          (fun _ nextHistory =>
            germ.endpointValue nextHistory.2 who)
          history =
        expect
          (LowerValueJet.behaviorStateStep profile history)
          (fun destination =>
            germ.endpointValue destination who) :=
    historyContinuationEU_statePotential_eq_behaviorStateStep
      profile (fun destination =>
        germ.endpointValue destination who) history
  rw [hcontinuation]
  rw [behaviorStateStep_scheduledPlayerOwnedFinkDeviationProfile
    germ who startEpoch valid dev history]
  unfold playerOwnedCalendarMixedStep
  rw [expect_bind]
  calc
    expect (dev stage history) (fun action =>
          expect
            (germ.finkOwnerActualOccupationKernelAt
              (valid (anytimeEpochIndex stage)) who
              (.inr (history.2, action)))
            (fun destination =>
              germ.endpointValue destination who)) ≤
        expect (dev stage history) (fun _ =>
          germ.endpointValue history.2 who) := by
      exact expect_mono _ _ _ fun action =>
        hsuper who (anytimeEpochIndex stage)
          history.2 action
    _ = germ.endpointValue history.2 who := by
      rw [expect_const]

omit [DecidableEq G.State] in
/-- From the selected entry, the endpoint value is a supermartingale under
every unilateral behavior strategy on a moving-superharmonic calendar. -/
theorem expectedHistoryEndpointValue_le_entry_of_movingSuperharmonic
    {germ : G.AnalyticBellmanGerm}
    {startEpoch : ℕ}
    {valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius}
    (hsuper :
      IsMovingPlayerOwnedEndpointSuperharmonic
        germ startEpoch valid)
    (who : ι) (dev : G.BehaviorStrategy who)
    (entry : G.State) :
    ∀ stage,
      G.expectedHistoryValue
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          entry
          (fun _ history =>
            germ.endpointValue history.2 who)
          stage ≤
        germ.endpointValue entry who := by
  intro stage
  induction stage with
  | zero =>
      rw [G.expectedHistoryValue_zero]
      exact le_rfl
  | succ stage inductionHypothesis =>
      rw [G.expectedHistoryValue_succ]
      calc
        expect
              (G.histDist
                (scheduledPlayerOwnedFinkDeviationProfile
                  germ who startEpoch valid dev)
                entry stage)
              (fun history =>
                G.historyContinuationEU
                  (scheduledPlayerOwnedFinkDeviationProfile
                    germ who startEpoch valid dev)
                  (fun _ nextHistory =>
                    germ.endpointValue nextHistory.2 who)
                  history) ≤
            expect
              (G.histDist
                (scheduledPlayerOwnedFinkDeviationProfile
                  germ who startEpoch valid dev)
                entry stage)
              (fun history =>
                germ.endpointValue history.2 who) := by
          exact expect_mono _ _ _ fun history =>
            historyContinuationEU_endpointValue_le_of_movingSuperharmonic
              hsuper who dev history
        _ ≤ germ.endpointValue entry who :=
          inductionHypothesis

omit [DecidableEq G.State] in
/-- Moving-row superharmonicity makes the full endpoint target-transport
sum nonpositive from the selected entry. -/
theorem expectedPlayerOwnedCalendarEndpointTargetTransport_le_zero
    {germ : G.AnalyticBellmanGerm}
    {startEpoch : ℕ}
    {valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius}
    (hsuper :
      IsMovingPlayerOwnedEndpointSuperharmonic
        germ startEpoch valid)
    (who : ι) (dev : G.BehaviorStrategy who)
    (entry : G.State) (T : ℕ) :
    expectedPlayerOwnedCalendarEndpointTargetTransport
        germ who entry startEpoch valid dev entry T ≤ 0 := by
  unfold expectedPlayerOwnedCalendarEndpointTargetTransport
  apply Finset.sum_nonpos
  intro stage _
  unfold expectedHistoryValue
  rw [expect_sub, expect_const]
  exact sub_nonpos.mpr
    (expectedHistoryEndpointValue_le_entry_of_movingSuperharmonic
      hsuper who dev entry stage)

/-- Moving-row superharmonicity supplies the target-transport account with
the identically zero budget. -/
def targetTransportAccountOfMovingSuperharmonic
    {germ : G.AnalyticBellmanGerm}
    {startEpoch : ℕ}
    {valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius}
    (hsuper :
      IsMovingPlayerOwnedEndpointSuperharmonic
        germ startEpoch valid)
    (entry : G.State) :
    PlayerOwnedCalendarEndpointTargetTransportAccount
      germ entry startEpoch valid where
  budget := fun _ _ => 0
  transport_le := fun who dev T =>
    expectedPlayerOwnedCalendarEndpointTargetTransport_le_zero
      hsuper who dev entry T
  sublinear := fun _ => IsAsymptoticallySublinear.const 0

/-- The sublinear analytic residual envelope and a target-transport account
combine into the exact fixed-entry residual account. -/
def playerOwnedCalendarResidualAccount_of_targetTransport
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
      PlayerOwnedCalendarEndpointTargetTransportAccount
        germ entry startEpoch valid) :
    PlayerOwnedCalendarResidualAccountAt
      germ (seed.playerOwnedPoissonBias correction)
      entry startEpoch valid (germ.endpointValue entry) where
  budget := fun who T =>
    seed.playerOwnedPoissonResidualCalendarBudget
        correction startEpoch T +
      transport.budget who T
  residual_le := by
    intro who dev T
    exact
      (seed.sum_expected_playerOwnedCalendarPrescribedBellmanResidual_le
          correction who entry startEpoch valid dev entry T).trans
        (by
          simpa only [add_comm] using
            add_le_add_left
              (transport.transport_le who dev T)
              (seed.playerOwnedPoissonResidualCalendarBudget
                correction startEpoch T))
  sublinear := by
    intro who
    exact
      (seed.playerOwnedPoissonResidualCalendarBudget_sublinear
          correction hPoisson startEpoch).add
        (transport.sublinear who)

/-- In the finite-bias Poisson/common-potential branch, target transport is
the final input needed for one shared horizon of unilateral deviation caps.
The on-path two-sided payoff estimate remains separate. -/
theorem eventually_all_deviationPayoff_le_endpointValue_add_of_targetTransport
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who))
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who
              (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt
              (seed.playerOwnedPoissonBias correction) who
              (CommonPlayerOwnedPotentialCalendar.ownerPotential
                germ (seed.playerOwnedPoissonBias correction)
                P who)
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (transport :
      PlayerOwnedCalendarEndpointTargetTransportAccount
        germ entry startEpoch valid)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop,
      ∀ (who : ι) (dev : G.BehaviorStrategy who),
        G.finiteAveragePayoff entry T
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            who ≤
          germ.endpointValue entry who + δ := by
  exact
    eventually_all_finiteAveragePayoff_playerOwnedCalendarAt_le_target_add
      germ (seed.playerOwnedPoissonBias correction) P entry
      startEpoch valid hcharge (germ.endpointValue entry)
      (seed.playerOwnedCalendarResidualAccount_of_targetTransport
        correction hPoisson entry startEpoch valid transport)
      hδ

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
