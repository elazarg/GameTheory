/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FullHorizonPublicHistoryEnvelope
import Math.Probability.FiniteControlledStoppingOptimalPolicy

/-!
# Optimal unilateral controls for full-horizon public-history envelopes

The finite controlled stopping envelope is not only an upper bound.  A
node-dependent pure policy attains it exactly: at every nonterminal node,
choose a pure action maximizing the continuation envelope.  Backward
induction then identifies the policy's controlled stopping value with the
worst-case potential.

For the bounded public-history tree this pure policy is an ordinary
history-dependent behavior strategy for the controlling player.  It keeps
the prescribed opponents, uses the maximizing pure replacement before the
fixed horizon, and returns to the prescribed behavior afterwards.  The
expected full-history obstacle under that unilateral deviation is exactly
the root envelope.

This closes the operational meaning of the unsafe branch of the finite
envelope: strict root domination is realized by one actual finite-prefix
unilateral behavior deviation, rather than only by unrelated local Bellman
witnesses.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

namespace FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}
    (profile : G.BehaviorProfile)
    (obstacle : G.Hist fuel → ι → ℝ)

private abbrev fullModel :=
  G.finiteFullHistoryControlledStoppingModel profile obstacle

omit [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
private theorem boundedPublicHistorySuccessor_node'
    {time : ℕ} (history : G.Hist time) (time_lt : time < fuel)
    (action : G.JointAct) (next : G.State) :
    G.boundedPublicHistorySuccessor
        (G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt))
        time_lt action next =
      G.boundedPublicHistoryNode
        ((Fin.snoc history.1 (history.2, action), next) :
          G.Hist (time + 1))
        (Nat.succ_le_of_lt time_lt) := by
  rfl

/-- The finite-prefix behavior deviation obtained from the envelope's
maximizing pure node policy.  At and after the fixed horizon the strategy
returns to the prescribed behavior. -/
def optimalFiniteHorizonDeviation (who : ι) :
    G.BehaviorStrategy who :=
  fun time history =>
    if before : time < fuel then
      (fullModel profile obstacle).optimalPurePolicy who
        (G.boundedPublicHistoryNode history (Nat.le_of_lt before))
    else
      profile who time history

omit [Finite G.State] in
@[simp] theorem optimalFiniteHorizonDeviation_of_lt
    (who : ι) {time : ℕ} (history : G.Hist time)
    (before : time < fuel) :
    optimalFiniteHorizonDeviation profile obstacle who time history =
      (fullModel profile obstacle).optimalPurePolicy who
        (G.boundedPublicHistoryNode history (Nat.le_of_lt before)) := by
  simp [optimalFiniteHorizonDeviation, before]

omit [Finite G.State] in
@[simp] theorem optimalFiniteHorizonDeviation_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (after : fuel ≤ time) :
    optimalFiniteHorizonDeviation profile obstacle who time history =
      profile who time history := by
  simp [optimalFiniteHorizonDeviation, Nat.not_lt.mpr after]

/-- Before the horizon, the worst-unilateral history potential is exactly
harmonic under the maximizing finite-prefix behavior deviation. -/
theorem worstUnilateralHistoryPotential_optimalDeviation_harmonic
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU
        (Function.update profile who
          (optimalFiniteHorizonDeviation profile obstacle who))
        (worstUnilateralHistoryPotential profile obstacle who)
        history =
      worstUnilateralHistoryPotential profile obstacle who time history := by
  let node :=
    G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt)
  have nonterminal : ¬G.IsFullHorizonNode node := by
    simpa [node, IsFullHorizonNode] using ne_of_lt time_lt
  have harmonic :=
    (fullModel profile obstacle).optimalPureAction_expect_eq_worstCasePotential
      who node nonterminal
  have action_dist :
      G.stageActionDist
          (Function.update profile who
            (optimalFiniteHorizonDeviation profile obstacle who))
          history =
        pmfPi
          (Function.update
            (fun player => profile player time history)
            who
            ((fullModel profile obstacle).optimalPurePolicy who node)) := by
    unfold stageActionDist
    congr 1
    funext player
    by_cases same : player = who
    · subst same
      simp only [Function.update_self]
      simpa [node] using
        optimalFiniteHorizonDeviation_of_lt
          profile obstacle player history time_lt
    · simp [Function.update_of_ne same]
  unfold historyContinuationEU
  rw [action_dist]
  rw [
    worstUnilateralHistoryPotential_of_le
      profile obstacle who history (Nat.le_of_lt time_lt)
  ]
  unfold Math.Probability.FiniteControlledStoppingModel.optimalPurePolicy
    at action_dist ⊢
  change
    expect
        (G.boundedPublicHistoryControlledKernel profile node who
          ((fullModel profile obstacle).optimalPureAction who node))
        ((fullModel profile obstacle).worstCasePotential who) =
      (fullModel profile obstacle).worstCasePotential who node
    at harmonic
  have node_strict : node.1.val < fuel := by
    simpa [node] using time_lt
  simp only [
    boundedPublicHistoryControlledKernel,
    dif_pos node_strict
  ] at harmonic
  rw [expect_bind] at harmonic
  dsimp [node] at harmonic
  apply Eq.trans _ harmonic
  apply congrArg
  funext action
  rw [expect_bind]
  apply congrArg (expect (G.transition history.2 action))
  funext next
  rw [expect_pure]
  rw [
    worstUnilateralHistoryPotential_of_le
      profile obstacle who
      ((Fin.snoc history.1 (history.2, action), next) :
        G.Hist (time + 1))
      (Nat.succ_le_of_lt time_lt)
  ]
  exact congrArg
    (worstUnilateralNodePotential profile obstacle who)
    (boundedPublicHistorySuccessor_node'
      history time_lt action next).symm

/-- The expected worst-envelope history potential is constant through the
finite prefix controlled by the maximizing deviation. -/
theorem expectedWorstUnilateralHistoryPotential_eq_root
    (initial : G.State) (who : ι) :
    ∀ time, time ≤ fuel →
      G.expectedHistoryValue
          (Function.update profile who
            (optimalFiniteHorizonDeviation profile obstacle who))
          initial
          (worstUnilateralHistoryPotential profile obstacle who)
          time =
        worstUnilateralHistoryPotential profile obstacle who 0
          (G.emptyHist initial) := by
  intro time time_le
  induction time with
  | zero =>
      simp [expectedHistoryValue]
  | succ time ih =>
      have time_lt : time < fuel := by
        omega
      rw [G.expectedHistoryValue_succ]
      calc
        expect
            (G.histDist
              (Function.update profile who
                (optimalFiniteHorizonDeviation
                  profile obstacle who))
              initial time)
            (fun history =>
              G.historyContinuationEU
                (Function.update profile who
                  (optimalFiniteHorizonDeviation
                    profile obstacle who))
                (worstUnilateralHistoryPotential
                  profile obstacle who)
                history) =
          expect
            (G.histDist
              (Function.update profile who
                (optimalFiniteHorizonDeviation
                  profile obstacle who))
              initial time)
            (worstUnilateralHistoryPotential
              profile obstacle who time) := by
                apply congrArg
                funext history
                exact
                  worstUnilateralHistoryPotential_optimalDeviation_harmonic
                    profile obstacle who history time_lt
        _ =
          worstUnilateralHistoryPotential profile obstacle who 0
            (G.emptyHist initial) :=
              ih (Nat.le_of_lt time_lt)

/-- Under any unilateral behavior deviation, the expected worst-envelope
history potential cannot exceed its root value before the fixed horizon. -/
theorem expectedWorstUnilateralHistoryPotential_le_root
    (initial : G.State) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    ∀ time, time ≤ fuel →
      G.expectedHistoryValue
          (Function.update profile who deviation)
          initial
          (worstUnilateralHistoryPotential profile obstacle who)
          time ≤
        worstUnilateralHistoryPotential profile obstacle who 0
          (G.emptyHist initial) := by
  intro time time_le
  induction time with
  | zero =>
      simp [expectedHistoryValue]
  | succ time ih =>
      have time_lt : time < fuel := by
        omega
      rw [G.expectedHistoryValue_succ]
      calc
        expect
            (G.histDist
              (Function.update profile who deviation)
              initial time)
            (fun history =>
              G.historyContinuationEU
                (Function.update profile who deviation)
                (worstUnilateralHistoryPotential
                  profile obstacle who)
                history) ≤
          expect
            (G.histDist
              (Function.update profile who deviation)
              initial time)
            (worstUnilateralHistoryPotential
              profile obstacle who time) := by
                apply expect_mono
                intro history
                exact
                  worstUnilateralHistoryPotential_deviation_superharmonic
                    profile obstacle who deviation history time_lt
        _ ≤
          worstUnilateralHistoryPotential profile obstacle who 0
            (G.emptyHist initial) :=
              ih (Nat.le_of_lt time_lt)

/-- Every unilateral behavior deviation's expected complete-history
obstacle is bounded by the root worst-case envelope. -/
theorem expect_obstacle_deviation_le_worstCasePotential
    (initial : G.State) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update profile who deviation)
          initial fuel)
        (fun history => obstacle history who) ≤
      (fullModel profile obstacle).worstCasePotential who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) initial) := by
  calc
    expect
        (G.histDist
          (Function.update profile who deviation)
          initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue
          (Function.update profile who deviation)
          initial
          (worstUnilateralHistoryPotential profile obstacle who)
          fuel := by
            unfold expectedHistoryValue
            apply congrArg
            funext history
            exact
              (worstUnilateralHistoryPotential_at_horizon
                profile obstacle who history).symm
    _ ≤
      worstUnilateralHistoryPotential profile obstacle who 0
        (G.emptyHist initial) :=
          expectedWorstUnilateralHistoryPotential_le_root
            profile obstacle initial who deviation fuel (le_refl fuel)
    _ =
      (fullModel profile obstacle).worstCasePotential who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) initial) := by
            rw [
              worstUnilateralHistoryPotential_of_le
                profile obstacle who (G.emptyHist initial)
                (Nat.zero_le fuel)
            ]
            rfl

/-- The maximizing node policy is realized by one actual unilateral
behavior deviation: its expected complete-history obstacle equals the root
worst-case envelope exactly. -/
theorem expect_obstacle_optimalFiniteHorizonDeviation_eq_worstCasePotential
    (initial : G.State) (who : ι) :
    expect
        (G.histDist
          (Function.update profile who
            (optimalFiniteHorizonDeviation profile obstacle who))
          initial fuel)
        (fun history => obstacle history who) =
      (fullModel profile obstacle).worstCasePotential who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) initial) := by
  calc
    expect
        (G.histDist
          (Function.update profile who
            (optimalFiniteHorizonDeviation profile obstacle who))
          initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue
          (Function.update profile who
            (optimalFiniteHorizonDeviation profile obstacle who))
          initial
          (worstUnilateralHistoryPotential profile obstacle who)
          fuel := by
            unfold expectedHistoryValue
            apply congrArg
            funext history
            exact
              (worstUnilateralHistoryPotential_at_horizon
                profile obstacle who history).symm
    _ =
      worstUnilateralHistoryPotential profile obstacle who 0
        (G.emptyHist initial) :=
          expectedWorstUnilateralHistoryPotential_eq_root
            profile obstacle initial who fuel (le_refl fuel)
    _ =
      (fullModel profile obstacle).worstCasePotential who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) initial) := by
            rw [
              worstUnilateralHistoryPotential_of_le
                profile obstacle who (G.emptyHist initial)
                (Nat.zero_le fuel)
            ]
            rfl

/-- Operational form of the finite root split.

In the safe branch every unilateral finite-prefix obstacle is bounded by the
root envelope.  In the unsafe branch the displayed canonical unilateral
behavior deviation itself beats the prescribed stopping value by `error`. -/
theorem everyDeviation_le_or_optimalDeviation_gt
    (initial : G.State) (who : ι)
    (error : ℝ) :
    (∀ deviation : G.BehaviorStrategy who,
      expect
          (G.histDist (Function.update profile who deviation)
            initial fuel)
          (fun history => obstacle history who) ≤
        (fullModel profile obstacle).prescribedPotential who
            (FinitePublicHistoryControlledStoppingModel.root
              (fuel := fuel) initial) +
          error) ∨
      (fullModel profile obstacle).prescribedPotential who
            (FinitePublicHistoryControlledStoppingModel.root
              (fuel := fuel) initial) +
          error <
        expect
          (G.histDist
            (Function.update profile who
              (optimalFiniteHorizonDeviation
                profile obstacle who))
            initial fuel)
          (fun history => obstacle history who) := by
  let root :=
    FinitePublicHistoryControlledStoppingModel.root
      (fuel := fuel) initial
  by_cases safe :
      (fullModel profile obstacle).worstCasePotential who root ≤
        (fullModel profile obstacle).prescribedPotential who root + error
  · apply Or.inl
    intro deviation
    calc
      expect
          (G.histDist (Function.update profile who deviation)
            initial fuel)
          (fun history => obstacle history who) ≤
        (fullModel profile obstacle).worstCasePotential who root := by
          exact
            expect_obstacle_deviation_le_worstCasePotential
              profile obstacle initial who deviation
      _ ≤
        (fullModel profile obstacle).prescribedPotential who root + error :=
          safe
  · apply Or.inr
    rw [
      expect_obstacle_optimalFiniteHorizonDeviation_eq_worstCasePotential
        profile obstacle initial who
    ]
    exact lt_of_not_ge safe

end FiniteFullHistoryControlledStoppingModel
end StochasticGame
end GameTheory
