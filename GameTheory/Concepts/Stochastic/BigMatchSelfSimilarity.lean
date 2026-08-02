/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BigMatchPublicPhase

/-!
# The exact live-cycle core of Big Match self-similarity

This file formalizes the elementary structural part of Question 80, Part D.
In the repository's Boolean convention, player `false` is the maximizer,
whose actions are `false = Continue` and `true = Stop`; player `true` is the
minimizer, whose actions are `false = Left` and `true = Right`.

The explicit history below plays `(Continue, Left)` and then
`(Continue, Right)`.  Both transitions remain live, its maximizer rewards are
`0` and `1` in that order, and its complete two-player payoff is exactly twice
the target `(1/2, -1/2)`.  Its target debt is therefore zero, and restarting
from its endpoint is literally restarting from the original live state.

This is only the self-similarity calculation.  It does **not** formalize or
assume the external theorem that every finite public controller fails to
secure the Big Match target, and hence proves no universal routing-resistance
or atlas-rank statement.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace BigMatch

/-- The first joint action in the live cycle: Continue against Left. -/
def continueLeft : game.JointAct := fun _who => false

/-- The second joint action in the live cycle: Continue against Right. -/
def continueRight : game.JointAct := fun who => who

@[simp] theorem continueLeft_maximizer : continueLeft false = false := rfl

@[simp] theorem continueLeft_minimizer : continueLeft true = false := rfl

@[simp] theorem continueRight_maximizer : continueRight false = false := rfl

@[simp] theorem continueRight_minimizer : continueRight true = true := rfl

/-- The concrete two-stage history used in Question 80's self-similarity
argument.  The stored state at both completed stages and at the endpoint is
the live state. -/
def liveCycleHistory : game.Hist 2 :=
  (![((.live : State), continueLeft), (.live, continueRight)], .live)

@[simp] theorem liveCycleHistory_stage_zero :
    liveCycleHistory.1 0 = (.live, continueLeft) := rfl

@[simp] theorem liveCycleHistory_stage_one :
    liveCycleHistory.1 1 = (.live, continueRight) := rfl

@[simp] theorem nextState_continueLeft :
    nextState .live continueLeft = .live := rfl

@[simp] theorem nextState_continueRight :
    nextState .live continueRight = .live := rfl

@[simp] theorem liveCycleHistory_endpoint : liveCycleHistory.2 = .live := rfl

/-- The displayed history is legal from `.live`: its stored initial state is
`.live`, and both stored successor states agree with the actual deterministic
transition. -/
theorem liveCycleHistory_isLegal :
    (liveCycleHistory.1 0).1 = .live ∧
      nextState (liveCycleHistory.1 0).1 (liveCycleHistory.1 0).2 =
        (liveCycleHistory.1 1).1 ∧
      nextState (liveCycleHistory.1 1).1 (liveCycleHistory.1 1).2 =
        liveCycleHistory.2 := by
  simp

/-- Continue/Left gives zero to both players at the live state. -/
@[simp] theorem stagePayoff_continueLeft (who : Player) :
    game.stagePayoff .live continueLeft who = 0 := by
  cases who <;> norm_num [game, payoff, reward, continueLeft]

/-- Continue/Right gives `1` to the maximizer and `-1` to the minimizer. -/
@[simp] theorem stagePayoff_continueRight (who : Player) :
    game.stagePayoff .live continueRight who = if who then -1 else 1 := by
  cases who <;> rfl

/-- The corrected stage order in Question 80 is `0, 1` for the maximizer. -/
theorem maximizer_liveCycle_stagePayoffs :
    (game.stagePayoff .live continueLeft false,
        game.stagePayoff .live continueRight false) = (0, 1) := by
  norm_num [game, payoff, reward, continueLeft, continueRight]

/-- The two-stage accumulated payoff is `(1,-1)`. -/
@[simp] theorem totalPayoff_liveCycleHistory (who : Player) :
    game.totalPayoff who liveCycleHistory = if who then -1 else 1 := by
  cases who <;>
    norm_num [StochasticGame.totalPayoff, liveCycleHistory, Fin.sum_univ_two,
      game, payoff, reward, continueLeft, continueRight]

/-- Vector form of the payoff identity: the live cycle earns exactly twice
the Big Match target `(1/2,-1/2)`. -/
theorem liveCycle_totalPayoff_eq_two_smul_fairPayoff :
    (fun who => game.totalPayoff who liveCycleHistory) =
      (2 : ℝ) • fairPayoff := by
  funext who
  cases who <;> norm_num [fairPayoff]

/-- Target debt accumulated over the two-stage live cycle. -/
def liveCycleTargetDebt : Payoff Player :=
  fun who => game.totalPayoff who liveCycleHistory - 2 * fairPayoff who

/-- Both target-debt coordinates vanish exactly. -/
@[simp] theorem liveCycleTargetDebt_eq_zero :
    liveCycleTargetDebt = 0 := by
  funext who
  cases who <;> norm_num [liveCycleTargetDebt, fairPayoff]

/-- Suffix rebasing at the endpoint starts from definitionally the same empty
live history as at the root. -/
@[simp] theorem emptyHist_liveCycleEndpoint :
    game.emptyHist liveCycleHistory.2 = game.emptyHist .live := rfl

/-- For every continuation profile and horizon, the physical continuation law
from the cycle endpoint is exactly the law from the root live state. -/
theorem histDist_liveCycleEndpoint (profile : game.BehaviorProfile) (horizon : ℕ) :
    game.histDist profile liveCycleHistory.2 horizon =
      game.histDist profile .live horizon := rfl

/-- Consequently every player's finite-horizon continuation payoff functional
is exactly the root functional. -/
theorem finiteAveragePayoff_liveCycleEndpoint (profile : game.BehaviorProfile)
    (horizon : ℕ) (who : Player) :
    game.finiteAveragePayoff liveCycleHistory.2 horizon profile who =
      game.finiteAveragePayoff .live horizon profile who := rfl

end BigMatch
end StochasticGame
end GameTheory
