/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.PositiveDynamicDebtProvenance
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.ExactDynamicDebtVanishingCounterexample

/-!
# Atomwise terminal regret does not transfer exact dynamic debt

This is a two-player, one-edge regression example.  At the
half--half zero-boundary root, player one has exact dynamic debt `1 / 2`.
Both atoms in that owner's terminal-live stopping law are noncredible for
player two: quitting alone has leaver regret one, while joining player one's
terminal solo action has joiner regret one.  Nevertheless player two has
zero exact debt at both endpoints.

The cancellation is simultaneous and ex ante.  Player two cannot condition
its action on player one's current action, so neither positive atomwise
regret creates a new dynamic-debt owner.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

namespace QuittingDynamicDebtOwnerTransferCounterexample

/-! We use `false` for the positive-debt owner and `true` for the player
whose two opposite atomwise regrets cancel. -/

/-- Payoffs `QC = (1,0)`, `CQ = (1,-1)`, and `QQ = (0,1)`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 1 else 0
      else
        if who then 0 else 1
    else
      if who then -1 else 1

/-- Both players independently Quit with probability one half. -/
def root : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The exact root value `(1/2,0)`. -/
def value : Payoff Bool := fun who => if who then 0 else 1 / 2

/-- Simplex presentation of `root`. -/
def simplexRoot : QuittingRootSimplex Bool :=
  fun who => stdSimplexEquiv (root who)

/-- The zero-boundary Nash--Bellman edge's current point. -/
def current : QuittingNashBellmanPoint Bool := (value, simplexRoot)

/-- Its zero terminal point. -/
def terminal : QuittingNashBellmanPoint Bool :=
  ((0 : Payoff Bool), quittingAllContinueSimplexRoot)

/-- The exact current debt `(1/2,0)`. -/
def currentDebt : Payoff Bool := fun who => if who then 0 else 1 / 2

theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first ↦
        expect (selectedRoot true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool
    selectedRoot f

@[simp] theorem root_apply (who : Bool) :
    root who = PMF.uniformOfFintype Bool := rfl

@[simp] theorem quittingRootOfSimplex_simplexRoot :
    quittingRootOfSimplex simplexRoot = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

@[simp] theorem value_false : value false = 1 / 2 := by
  simp [value]

@[simp] theorem value_true : value true = 0 := by
  simp [value]

@[simp] theorem currentDebt_false : currentDebt false = 1 / 2 := by
  simp [currentDebt]

@[simp] theorem currentDebt_true : currentDebt true = 0 := by
  simp [currentDebt]

/-! ## Exact endpoint calculations -/

theorem false_quitPayoff :
    quittingRootQuitPayoff reward (0 : Payoff Bool) root false = 1 / 2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem false_continuePayoff :
    quittingRootContinuePayoff reward (0 : Payoff Bool) root false = 1 / 2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem true_quitPayoff :
    quittingRootQuitPayoff reward (0 : Payoff Bool) root true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem true_continuePayoff :
    quittingRootContinuePayoff reward (0 : Payoff Bool) root true = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

/-- Both players are exactly indifferent, hence the root is endpoint Nash. -/
theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root := by
  intro who
  cases who
  · rw [quittingRootEndpointDifference, false_quitPayoff,
      false_continuePayoff]
    norm_num
  · rw [quittingRootEndpointDifference, true_quitPayoff,
      true_continuePayoff]
    norm_num

/-- The half--half root sends the zero tail to `(1/2,0)`. -/
theorem root_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Bool) root = value := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff]
    norm_num [root, PMF.uniformOfFintype_apply, value]
  · rw [true_quitPayoff, true_continuePayoff]
    norm_num [root, PMF.uniformOfFintype_apply, value]

/-- The displayed points form an exact zero-boundary Nash--Bellman edge. -/
theorem current_terminal_edge :
    IsQuittingNashBellmanEdge reward current terminal := by
  constructor
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_successor_zero.symm
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_isEndpointNash_zero

/-! ## Exact debt and failed owner transfer -/

@[simp] theorem singletonReward_false :
    reward (quittingSingletonTerminal false) false = 1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem singletonReward_true :
    reward (quittingSingletonTerminal true) true = -1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem terminalDebt_false :
    quittingPositiveSingletonDebtCap reward false = 1 := by
  simp [quittingPositiveSingletonDebtCap]

@[simp] theorem terminalDebt_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  simp [quittingPositiveSingletonDebtCap]

@[simp] theorem opponentContinueMass_false :
    quittingDebtOpponentContinueMass (current, currentDebt) false = 1 / 2 := by
  rw [quittingDebtOpponentContinueMass_eq_stationary]
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
    exact quittingRootOfSimplex_simplexRoot]
  norm_num [quittingStationaryContinueMass, pmfPi_apply,
    quittingAllContinueAction, root, PMF.uniformOfFintype_apply]

/-- Player one's exact debt at the current point is `1/2`. -/
theorem dynamicDebtUpdate_false :
    quittingDynamicDebtUpdate reward
        (current, currentDebt)
        (terminal, quittingPositiveSingletonDebtCap reward) false = 1 / 2 := by
  unfold quittingDynamicDebtUpdate
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
      exact quittingRootOfSimplex_simplexRoot]
  rw [show (terminal, quittingPositiveSingletonDebtCap reward).1.1 =
      (0 : Payoff Bool) by rfl]
  rw [false_quitPayoff, false_continuePayoff]
  rw [opponentContinueMass_false]
  change max (1 / 2) (1 / 2 + 1 / 2 *
      quittingPositiveSingletonDebtCap reward false) - value false = 1 / 2
  rw [terminalDebt_false, value_false]
  norm_num

/-- Player two's exact debt remains zero despite both atomwise regrets. -/
theorem dynamicDebtUpdate_true :
    quittingDynamicDebtUpdate reward
        (current, currentDebt)
        (terminal, quittingPositiveSingletonDebtCap reward) true = 0 := by
  unfold quittingDynamicDebtUpdate
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
      exact quittingRootOfSimplex_simplexRoot]
  rw [show (terminal, quittingPositiveSingletonDebtCap reward).1.1 =
      (0 : Payoff Bool) by rfl]
  rw [true_quitPayoff, true_continuePayoff]
  simp [terminalDebt_true, current]

/-- The edge carries the literal exact dynamic-debt annotation `(1/2,0)`. -/
theorem current_terminal_dynamicDebtEdge :
    IsQuittingDynamicDebtEdge reward
      (current, currentDebt)
      (terminal, quittingPositiveSingletonDebtCap reward) := by
  refine ⟨current_terminal_edge, ?_⟩
  intro who
  cases who
  · simpa using dynamicDebtUpdate_false.symm
  · simpa using dynamicDebtUpdate_true.symm

/-- Player two is genuinely active at the mixed root. -/
theorem markedPlayer_quitProbability :
    0 < (root true true).toReal := by
  norm_num [root, PMF.uniformOfFintype_apply]

/-- On the owner-deleted atom where player two quits alone, player two gains
one by leaving the quitter set and receiving Never payoff zero. -/
theorem activeLeaver_regret_eq_one :
    0 - reward (quittingSingletonTerminal true) true = 1 := by
  simp

/-- On player one's terminal solo atom, player two gains one by joining. -/
theorem inactiveJoiner_regret_eq_one :
    reward ⟨{false, true}, by simp⟩ true -
        reward (quittingSingletonTerminal false) true = 1 := by
  simp [reward, quittingSingletonTerminal]

/-- The regression packet: positive owner debt, positive activity and two
strict atomwise regrets coexist with zero exact debt for the marked player
at both the current and terminal endpoints. -/
theorem atomwise_regret_does_not_transfer_dynamicDebt :
    0 < currentDebt false ∧
    0 < (root true true).toReal ∧
    0 < 0 - reward (quittingSingletonTerminal true) true ∧
    0 < reward ⟨{false, true}, by simp⟩ true -
      reward (quittingSingletonTerminal false) true ∧
    currentDebt true = 0 ∧
    quittingPositiveSingletonDebtCap reward true = 0 := by
  constructor
  · norm_num
  constructor
  · exact markedPlayer_quitProbability
  constructor
  · rw [activeLeaver_regret_eq_one]
    norm_num
  constructor
  · rw [inactiveJoiner_regret_eq_one]
    norm_num
  exact ⟨currentDebt_true, terminalDebt_true⟩

end QuittingDynamicDebtOwnerTransferCounterexample

end GameTheory
