/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkMonitor
import Math.OnlineLearning.ContextualMultiplicativeWeights

/-!
# Context-local predictable public monitors

A public context is revealed before prediction.  Each context owns an
independent horizon-free multiplicative-weights learner, and only the
learner for the revealed context advances.  Local observation streams make
the timing explicit: the distribution at local round `n` depends only on
rounds strictly before `n`.

The generic part of this file handles arbitrary finite monitor and outcome
sets.  The final section specializes the score to the signed PMF-coordinate
tests used by Fink obstruction monitors.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

section Generic

variable {Q A Ω : Type*}
  [Fintype Q] [DecidableEq Q]
  [Fintype A] [Nonempty A]
  [Finite Ω]

/-- Realized local gain vector for a monitor family. -/
def contextualMonitorGain
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (q : Q) (n : ℕ) (a : A) : ℝ :=
  score q n a (observation q n)

/-- Monitor distribution selected after the current context is revealed.
Only gains from earlier visits to that context affect this distribution. -/
def contextualMonitorDist
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (t : ℕ) : PMF A :=
  Math.OnlineLearning.contextualMWDist context
    (contextualMonitorGain score observation) t

/-- The public score at global time `t` if the next outcome is `x`. -/
def contextualWeightedMonitorScore
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (t : ℕ) (x : Ω) : ℝ :=
  let q := context t
  let n := Math.OnlineLearning.contextLocalRound context t
  expect (contextualMonitorDist context score observation t)
    (fun a => score q n a x)

omit [Fintype Q] [Finite Ω] in
/-- Exact causality: changing current or future observations in the active
context does not change the distribution played now. -/
theorem contextualMonitorDist_congr_of_local_past
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation observation' : Q → ℕ → Ω)
    (t : ℕ)
    (heq :
      ∀ n < Math.OnlineLearning.contextLocalRound context t,
        observation (context t) n =
          observation' (context t) n) :
    contextualMonitorDist context score observation t =
      contextualMonitorDist context score observation' t := by
  apply Math.OnlineLearning.contextualMWDist_congr_of_local_past
  intro n hn
  funext a
  simp only [contextualMonitorGain]
  rw [heq n hn]

/-- Total gain accumulated by all context-local monitor learners. -/
def contextualMonitorAlgGain
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (T : ℕ) : ℝ :=
  Math.OnlineLearning.contextualAlgGain context
    (contextualMonitorGain score observation) T

/-- Realized gain of one fixed context-to-monitor policy. -/
def contextualMonitorPolicyGain
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (T : ℕ) (policy : Q → A) : ℝ :=
  Math.OnlineLearning.contextualPolicyGain context
    (contextualMonitorGain score observation) T policy

omit [Fintype A] [Nonempty A] [Finite Ω] in
/-- The policy comparator is exactly the realized score of the fixed
context-to-monitor map on the interleaved observation stream. -/
theorem contextualMonitorPolicyGain_eq_sum
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (T : ℕ) (policy : Q → A) :
    contextualMonitorPolicyGain
        context score observation T policy =
      ∑ t ∈ Finset.range T,
        score (context t)
          (Math.OnlineLearning.contextLocalRound context t)
          (policy (context t))
          (observation (context t)
            (Math.OnlineLearning.contextLocalRound context t)) := by
  rw [contextualMonitorPolicyGain,
    Math.OnlineLearning.contextualPolicyGain_eq_sum]
  rfl

omit [Finite Ω] in
/-- The abstract learner gain is exactly the sum of realized public scores
of the distributions played on the revealed contexts. -/
theorem contextualMonitorAlgGain_eq_sum_weightedScore
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (T : ℕ) :
    contextualMonitorAlgGain context score observation T =
      ∑ t ∈ Finset.range T,
        contextualWeightedMonitorScore
          context score observation t
          (observation (context t)
            (Math.OnlineLearning.contextLocalRound context t)) := by
  rw [contextualMonitorAlgGain,
    Math.OnlineLearning.contextualAlgGain_eq_sum]
  rfl

omit [Fintype Q] in
/-- Expected weighted score is the learner mixture of the monitor
conditional means.  This is the one-step compensator identity. -/
theorem expect_contextualWeightedMonitorScore
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (outcomeLaw : PMF Ω) (t : ℕ) :
    expect outcomeLaw
        (contextualWeightedMonitorScore
          context score observation t) =
      expect
        (contextualMonitorDist context score observation t)
        (fun a =>
          expect outcomeLaw
            (score (context t)
              (Math.OnlineLearning.contextLocalRound context t) a)) := by
  rw [show
      contextualWeightedMonitorScore
          context score observation t =
        fun x =>
          ∑ a,
            ((contextualMonitorDist
              context score observation t) a).toReal *
              score (context t)
                (Math.OnlineLearning.contextLocalRound context t) a x by
    funext x
    exact expect_eq_sum _ _]
  rw [← expect_sum_comm, expect_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [expect_const_mul]

omit [Fintype Q] in
/-- A coordinatewise centered monitor family remains exactly centered after
the predictable context-local learner mixes it. -/
theorem expect_contextualWeightedMonitorScore_baseline_eq_zero
    (context : ℕ → Q)
    (score : Q → ℕ → A → Ω → ℝ)
    (observation : Q → ℕ → Ω)
    (baseline : Q → ℕ → PMF Ω)
    (hcentered :
      ∀ q n a, expect (baseline q n) (score q n a) = 0)
    (t : ℕ) :
    expect
        (baseline (context t)
          (Math.OnlineLearning.contextLocalRound context t))
        (contextualWeightedMonitorScore
          context score observation t) = 0 := by
  rw [expect_contextualWeightedMonitorScore]
  simp_rw [hcentered]
  simp

omit [Finite Ω] in
/-- Pathwise contextual regret.  Context switches are absent from the
bound; only visitation counts occur. -/
theorem contextualMonitor_fixedPolicyRegret_le_visits
    (context : ℕ → Q)
    {score : Q → ℕ → A → Ω → ℝ}
    (observation : Q → ℕ → Ω)
    (hscore :
      ∀ q n a x, score q n a x ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (policy : Q → A) :
    contextualMonitorPolicyGain
          context score observation T policy -
        contextualMonitorAlgGain context score observation T ≤
      8 * (Real.log (Fintype.card A) + 1) *
        ∑ q,
          Real.sqrt
            (Math.OnlineLearning.contextVisitCount context q T) := by
  exact
    Math.OnlineLearning.contextual_fixedPolicyRegret_le_visits
      context (fun q n a => hscore q n a (observation q n))
      T policy

omit [Finite Ω] in
/-- Cardinality-only contextual regret bound. -/
theorem contextualMonitor_fixedPolicyRegret_le_card
    (context : ℕ → Q)
    {score : Q → ℕ → A → Ω → ℝ}
    (observation : Q → ℕ → Ω)
    (hscore :
      ∀ q n a x, score q n a x ∈ Set.Icc (-1 : ℝ) 1)
    (T : ℕ) (policy : Q → A) :
    contextualMonitorPolicyGain
          context score observation T policy -
        contextualMonitorAlgGain context score observation T ≤
      8 * (Real.log (Fintype.card A) + 1) *
        Real.sqrt (Fintype.card Q * T) := by
  exact
    Math.OnlineLearning.contextual_fixedPolicyRegret_le_card
      context (fun q n a => hscore q n a (observation q n))
      T policy

end Generic

section FinkCoordinate

variable {Q : Type*} {Ω : Type}
  [Fintype Q] [DecidableEq Q]
  [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]

/-- Context-local signed coordinate-monitor score. -/
def contextualPMFCoordinateMonitorScore
    (baseline : Q → ℕ → PMF Ω)
    (q : Q) (n : ℕ)
    (monitor : PMFCoordinateMonitor Ω) (x : Ω) : ℝ :=
  pmfCoordinateTestScore
    (baseline q n) monitor.1 monitor.2 x

/-- Fink coordinate-monitor distribution selected on a revealed context. -/
def contextualPMFCoordinateMonitorDist
    (context : ℕ → Q)
    (baseline : Q → ℕ → PMF Ω)
    (observation : Q → ℕ → Ω)
    (t : ℕ) :
    PMF (PMFCoordinateMonitor Ω) :=
  contextualMonitorDist context
    (contextualPMFCoordinateMonitorScore baseline)
    observation t

/-- Realized gain of the contextual Fink coordinate-monitor learner. -/
def contextualPMFCoordinateMonitorAlgGain
    (context : ℕ → Q)
    (baseline : Q → ℕ → PMF Ω)
    (observation : Q → ℕ → Ω)
    (T : ℕ) : ℝ :=
  contextualMonitorAlgGain context
    (contextualPMFCoordinateMonitorScore baseline)
    observation T

omit [Fintype Q] in
/-- Every context-local Fink mixture is exactly centered under its current
baseline kernel. -/
theorem expect_contextualPMFCoordinateMonitorScore_baseline_eq_zero
    (context : ℕ → Q)
    (baseline : Q → ℕ → PMF Ω)
    (observation : Q → ℕ → Ω)
    (t : ℕ) :
    let q := context t
    let n := Math.OnlineLearning.contextLocalRound context t
    expect (baseline q n)
        (contextualWeightedMonitorScore context
          (contextualPMFCoordinateMonitorScore baseline)
          observation t) = 0 := by
  dsimp only
  apply expect_contextualWeightedMonitorScore_baseline_eq_zero
  intro q n monitor
  exact expect_pmfCoordinateTestScore_baseline
    (baseline q n) monitor.1 monitor.2

omit [Fintype Q] in
/-- Under a comparison kernel, the contextual Fink score compensator is
the learner mixture of oriented coordinate-probability differences. -/
theorem expect_contextualPMFCoordinateMonitorScore_eq_difference
    (context : ℕ → Q)
    (baseline : Q → ℕ → PMF Ω)
    (observation : Q → ℕ → Ω)
    (comparison : PMF Ω) (t : ℕ) :
    let q := context t
    let n := Math.OnlineLearning.contextLocalRound context t
    expect comparison
        (contextualWeightedMonitorScore context
          (contextualPMFCoordinateMonitorScore baseline)
          observation t) =
      expect
        (contextualPMFCoordinateMonitorDist
          context baseline observation t)
        (fun monitor =>
          (if monitor.2 then 1 else -1) *
            ((comparison monitor.1).toReal -
              (baseline q n monitor.1).toReal)) := by
  dsimp only
  rw [expect_contextualWeightedMonitorScore]
  congr 1
  funext monitor
  exact expect_pmfCoordinateTestScore
    (baseline (context t)
      (Math.OnlineLearning.contextLocalRound context t))
    comparison monitor.1 monitor.2

/-- A fixed public context-to-coordinate-monitor policy is captured with
square-root contextual regret and no context-switch penalty. -/
theorem contextualPMFCoordinateMonitor_fixedPolicyRegret_le_card
    (context : ℕ → Q)
    (baseline : Q → ℕ → PMF Ω)
    (observation : Q → ℕ → Ω)
    (T : ℕ) (policy : Q → PMFCoordinateMonitor Ω) :
    contextualMonitorPolicyGain context
          (contextualPMFCoordinateMonitorScore baseline)
          observation T policy -
        contextualPMFCoordinateMonitorAlgGain
          context baseline observation T ≤
      8 *
          (Real.log
            (Fintype.card (PMFCoordinateMonitor Ω)) + 1) *
        Real.sqrt (Fintype.card Q * T) := by
  apply contextualMonitor_fixedPolicyRegret_le_card
  intro q n monitor x
  exact abs_le.mp
    (abs_pmfCoordinateTestScore_le_one
      (baseline q n) monitor.1 monitor.2 x)

end FinkCoordinate

end StochasticGame
end GameTheory
