/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.BigMatch.Basic
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope

/-!
# Negative-singleton survival charge can be a strict upper bound

This two-player one-root calculation fences a tempting exceptional-tail
identity.  Player `false` quits surely, player `true` quits with probability
one half, and the continuation agrees with player `false`'s negative
singleton payoff.  The root is an exact Nash root and player `false`'s best
one-root deviation gain is zero.  Nevertheless the product of opponent
survival and the negative-singleton magnitude is `1 / 2`.

Thus opponent survival times negative singleton debt is a valid possible
charge, but it is not in general the *exact* deviation gain.  Equality needs
an additional support, indifference, or properness condition.  The example
does not challenge any upper-bound theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingNegativeSingletonChargeRegression

/-- Player `false` receives `-1` when quitting alone, `0` when only the
opponent quits, and `1` when both quit.  Player `true` always receives zero. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if who then 0
    else if false ∈ quitters.1 then
      if true ∈ quitters.1 then 1 else -1
    else 0

/-- The all-continue continuation equals the negative singleton payoff for
player `false`. -/
def tail : Payoff Bool := fun who => if who then 0 else -1

/-- Player `false` quits surely; player `true` mixes uniformly. -/
def root : Bool → PMF Bool := fun who =>
  if who then PMF.uniformOfFintype Bool else PMF.pure true

/-- A constant sequence, used only to express the one-stage opponent-survival
weight in the common telescope language. -/
def roots : ℕ → Bool → PMF Bool := fun _ => root

/-- Fubini expansion of a two-player Boolean product law. -/
theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first ↦
        expect (selectedRoot true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  StochasticGame.BigMatch.expect_pmfPi_bool selectedRoot f

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

/-- Explicit quitter set for a two-coordinate Boolean action. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool ↦ if who then second else first) =
      (if first = true then {false} else ∅) ∪
        (if second = true then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

@[simp] theorem reward_false_singleton :
    reward (quittingSingletonTerminal false) false = -1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem tail_false : tail false = -1 := by simp [tail]

@[simp] theorem tail_true : tail true = 0 := by simp [tail]

@[simp] theorem root_false : root false = PMF.pure true := by simp [root]

@[simp] theorem root_true : root true = PMF.uniformOfFintype Bool := by
  simp [root]

@[simp] theorem false_quitPayoff :
    quittingRootQuitPayoff reward tail root false = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp [root, quittingRootPayoff, reward, expect_uniform_bool]

@[simp] theorem false_continuePayoff :
    quittingRootContinuePayoff reward tail root false = -(1 / 2 : ℝ) := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp [root, tail, quittingRootPayoff, reward, expect_uniform_bool]
  norm_num

@[simp] theorem true_quitPayoff :
    quittingRootQuitPayoff reward tail root true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp [root, quittingRootPayoff, reward]

@[simp] theorem true_continuePayoff :
    quittingRootContinuePayoff reward tail root true = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp [root, quittingRootPayoff, reward]

/-- The prescribed root payoff is zero for both players. -/
@[simp] theorem root_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward tail root who = 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who <;> simp [root]

/-- The displayed product root is an exact Nash root.  Player `false`
strictly prefers its prescribed pure Quit action; player `true` is
indifferent. -/
theorem root_isExactNash :
    IsεQuittingRootNash reward tail 0 root := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  cases who <;> simp [quittingRootEndpointDifference, root]

/-- Player `false`'s best pure endpoint has exactly zero gain over the
prescribed root payoff. -/
theorem false_bestEndpointGain_eq_zero :
    max (quittingRootQuitPayoff reward tail root false)
          (quittingRootContinuePayoff reward tail root false) -
        quittingRootSuccessorPayoff reward tail root false = 0 := by
  norm_num

/-- The opponent survives the root with probability one half. -/
theorem false_oneStepOpponentSurvival_eq_half :
    quittingOpponentSurvivalWeight roots false 0 1 = 1 / 2 := by
  simp [quittingOpponentSurvivalWeight, quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass, quittingAllContinueAction, roots, root,
    pmfPi_apply]

/-- The negative-singleton survival charge is strictly positive, despite the
zero best endpoint gain. -/
theorem false_negativeSingletonSurvivalCharge_eq_half :
    quittingOpponentSurvivalWeight roots false 0 1 *
        max 0 (-reward (quittingSingletonTerminal false) false) = 1 / 2 := by
  rw [false_oneStepOpponentSurvival_eq_half]
  norm_num

/-- Final strict regression: exact rootwise deviation gain is strictly below
the survival-weighted negative-singleton charge. -/
theorem false_bestEndpointGain_lt_negativeSingletonSurvivalCharge :
    max (quittingRootQuitPayoff reward tail root false)
          (quittingRootContinuePayoff reward tail root false) -
        quittingRootSuccessorPayoff reward tail root false <
      quittingOpponentSurvivalWeight roots false 0 1 *
        max 0 (-reward (quittingSingletonTerminal false) false) := by
  rw [false_bestEndpointGain_eq_zero,
    false_negativeSingletonSurvivalCharge_eq_half]
  norm_num

end QuittingNegativeSingletonChargeRegression

end GameTheory
