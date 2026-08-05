/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingLiveMassRecurrence
import GameTheory.Concepts.Stochastic.QuittingSimpleBranches

/-!
# Opponent-only survival dominates unilateral survival

Fix a player and replace only that player's behavior by always continuing.
The resulting live mass is the probability that no opponent has yet quit.
Every unilateral deviation has smaller live mass, stage by stage.  This is
the first uniform domination used in the terminal-to-uniform proof.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The profile obtained by making `who` always continue. -/
def quittingOpponentOnlyProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingAlwaysContinueStrategy reward who)

/-- Conditional all-continue mass under an arbitrary unilateral deviation
is no larger than when that player always continues. -/
theorem quittingJointContinueMass_update_le_opponentOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) (time : ℕ) :
    quittingJointContinueMass reward
        (Function.update profile who deviation) time ≤
      quittingJointContinueMass reward
        (quittingOpponentOnlyProfile reward profile who) time := by
  unfold quittingOpponentOnlyProfile quittingJointContinueMass
    StochasticGame.stageActionDist
  simp only [pmfPi_apply]
  let leftFactor : ι → ENNReal := fun player =>
    (Function.update profile who deviation player time
      (quittingLiveHist reward time)) false
  let rightFactor : ι → ENNReal := fun player =>
    (Function.update profile who (quittingAlwaysContinueStrategy reward who)
      player time (quittingLiveHist reward time)) false
  with_unfolding_all
    change (∏ player, leftFactor player).toReal ≤
      (∏ player, rightFactor player).toReal
  have hleft : (∏ player, leftFactor player) ≠ ⊤ :=
    ENNReal.prod_ne_top fun player _ => PMF.apply_ne_top _ _
  have hright : (∏ player, rightFactor player) ≠ ⊤ :=
    ENNReal.prod_ne_top fun player _ => PMF.apply_ne_top _ _
  rw [ENNReal.toReal_le_toReal hleft hright]
  apply Finset.prod_le_prod
  · intro player _
    exact bot_le
  · intro player _
    by_cases hp : player = who
    · subst player
      simp only [leftFactor, rightFactor, Function.update_self,
        quittingAlwaysContinueStrategy, PMF.pure_apply]
      exact PMF.coe_le_one _ _
    · simp [leftFactor, rightFactor, Function.update_of_ne hp]

/-- Every unilateral deviation's live mass is bounded by the probability
that the opponents have all continued. -/
theorem quittingLiveMass_update_le_opponentOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    ∀ time,
      quittingLiveMass reward (Function.update profile who deviation) time ≤
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, quittingLiveMass_succ]
      exact mul_le_mul ih
        (quittingJointContinueMass_update_le_opponentOnly
          reward profile who deviation time)
        (quittingJointContinueMass_nonneg reward
          (Function.update profile who deviation) time)
        (quittingLiveMass_nonneg reward
          (quittingOpponentOnlyProfile reward profile who) time)

end GameTheory
