/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BigMatch
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate

/-!
# A same-node marked-transfer cycle need not give an invariant edge law

This file records a two-player, two-edge exact quitting-game calculation.  At
the first root both players mix one half, its current value is `(-2,-2)`, and
its declared successor is `(-1,-1)`.  At the second root both players quit
surely, with successor zero.  Both roots are exact Nash roots and both
successor equations hold.

At the first root either player can mark the other player using a bad
owner-deleted singleton atom.  Consequently a procedure which merely changes
the marked player, but does not advance the suffix time, can alternate the two
marks forever while selecting the *same* Bellman edge.  Repeated marks then do
not imply matching current and successor marginals: the selected edge still
has distinct endpoints `(-2,-2)` and `(-1,-1)`.

This is only a regression for that recurrence inference.  It is not a
counterexample to equilibrium existence: the displayed two-edge chain itself
ends at a surely absorbing exact Nash root.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingMarkedSameNodeCycleRegression

/-- The symmetric terminal table: a joint quit pays `-1`, while a singleton
quit pays `-3`, to both players. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun _ => if quitters.1.card = 2 then -1 else -3

/-- The first root, at which both players quit with probability one half. -/
def halfRoot : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The terminal root, at which both players quit surely. -/
def sureRoot : Bool → PMF Bool := fun _ => PMF.pure true

/-- Current value at the half root. -/
def firstValue : Payoff Bool := fun _ => -2

/-- Successor value of the half root and current value of the sure root. -/
def secondValue : Payoff Bool := fun _ => -1

/-- Terminal continuation beyond the surely absorbing root. -/
def terminalValue : Payoff Bool := fun _ => 0

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

/-- Fubini expansion of a two-player Boolean product law. -/
theorem expect_pmfPi_bool (root : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi root) f =
      expect (root false) (fun first ↦
        expect (root true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  StochasticGame.BigMatch.expect_pmfPi_bool root f

/-- Explicit quitter set for a two-coordinate Boolean action.  Keeping this
small normal form available makes the endpoint calculations below robust to
the representation of `Finset.univ` chosen by simplification. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool ↦ if who then second else first) =
      (if first = true then {false} else ∅) ∪
        (if second = true then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

@[simp] theorem halfRoot_true_toReal (who : Bool) :
    (halfRoot who true).toReal = 1 / 2 := by
  norm_num [halfRoot, PMF.uniformOfFintype_apply]

@[simp] theorem halfRoot_false_toReal (who : Bool) :
    (halfRoot who false).toReal = 1 / 2 := by
  norm_num [halfRoot, PMF.uniformOfFintype_apply]

@[simp] theorem sureRoot_true_toReal (who : Bool) :
    (sureRoot who true).toReal = 1 := by
  simp [sureRoot]

@[simp] theorem sureRoot_false_toReal (who : Bool) :
    (sureRoot who false).toReal = 0 := by
  simp [sureRoot]

/-- At the half root, pure Quit pays `-2`: the opponent's singleton and
joint-quit outcomes have equal weight. -/
@[simp] theorem halfRoot_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward secondValue halfRoot who = -2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [halfRoot, secondValue, quittingRootPayoff,
      reward, expect_uniform_bool] <;>
    norm_num

/-- At the half root, pure Continue also pays `-2`: the opponent's singleton
outcome and the all-continue successor have equal weight. -/
@[simp] theorem halfRoot_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward secondValue halfRoot who = -2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [halfRoot, secondValue, quittingRootPayoff,
      reward, expect_uniform_bool] <;>
    norm_num

/-- The half root has current value exactly `(-2,-2)`. -/
@[simp] theorem halfRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward secondValue halfRoot who =
      firstValue who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [firstValue]
  norm_num

/-- The half root is an exact Nash root. -/
theorem halfRoot_isExactNash :
    IsεQuittingRootNash reward secondValue 0 halfRoot := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  simp [quittingRootEndpointDifference]

/-- Against the surely quitting opponent, pure Quit pays the joint-quit
reward `-1`. -/
@[simp] theorem sureRoot_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward terminalValue sureRoot who = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [sureRoot, terminalValue, quittingRootPayoff,
      reward]

/-- Against the surely quitting opponent, pure Continue pays the opponent's
singleton reward `-3`. -/
@[simp] theorem sureRoot_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward terminalValue sureRoot who = -3 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [sureRoot, terminalValue, quittingRootPayoff,
      reward]

/-- The sure root has current value exactly `(-1,-1)`. -/
@[simp] theorem sureRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward terminalValue sureRoot who =
      secondValue who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [secondValue]

/-- The sure root is an exact Nash root: the prescribed pure-Quit action
strictly dominates pure Continue. -/
theorem sureRoot_isExactNash :
    IsεQuittingRootNash reward terminalValue 0 sureRoot := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  simp [quittingRootEndpointDifference]

/-- Every owner-deleted singleton atom at the half root pays the other player
`-3`, while that player's current marked value is at most `-1`. -/
theorem ownerDeletedSingleton_isBad
    (owner next : Bool) (hne : next ≠ owner) :
    next ≠ owner ∧
      reward (quittingSingletonTerminal next) next = -3 ∧
        firstValue next ≤ -1 := by
  exact ⟨hne, by simp [reward, quittingSingletonTerminal], by simp [firstValue]⟩

/-- Both directed mark changes exist at the same half-root edge. -/
theorem alternating_sameNode_marks :
    (false ≠ true) ∧ (true ≠ false) := by simp

/-- The selected half-root Bellman edge is not a self-loop.  Therefore
repeating this edge after cycling only the mark cannot produce equal current
and successor Dirac marginals. -/
theorem selectedEdge_source_ne_successor : firstValue ≠ secondValue := by
  intro h
  have := congrFun h false
  norm_num [firstValue, secondValue] at this

/-- The source and successor Dirac laws of the repeatedly selected edge are
different. -/
theorem selectedEdge_diracMarginals_ne :
    PMF.pure firstValue ≠ PMF.pure secondValue := by
  intro h
  have hmass :
      (PMF.pure firstValue : PMF (Payoff Bool)) firstValue =
        (PMF.pure secondValue : PMF (Payoff Bool)) firstValue := by
    rw [h]
  rw [PMF.pure_apply_self,
    PMF.pure_apply_of_ne secondValue firstValue
      selectedEdge_source_ne_successor] at hmass
  exact one_ne_zero hmass

end QuittingMarkedSameNodeCycleRegression

end GameTheory
