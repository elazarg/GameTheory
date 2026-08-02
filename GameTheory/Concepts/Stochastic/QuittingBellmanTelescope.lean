/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPureTimeExtremality

/-!
# Bellman residual telescope along a quitting live path

Fix a sequence of product roots along the unique live path and one player.
The player's one-step Bellman operator compares quitting now with continuing
now and using a supplied value at the next live stage.  This file records the
prescribed residual, the gap to a Bellman cap, and their finite weighted
telescope.

The finite statements make no tail-contraction claim.  In particular, a
zero opponent-survival factor before the starting time is never used to infer
contraction after that time.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-step pure-action Bellman value against the supplied opponent
marginals at a live stage. -/
def quittingLiveBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (value : ℕ → ℝ) (time : ℕ) : ℝ :=
  max (quittingFixedOpponentsQuitValue reward roots who time)
    (quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * value (time + 1))

/-- Loss of the prescribed continuation value relative to the best pure
action at the current live stage. -/
def quittingPrescribedOneStepResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) : ℝ :=
  quittingLiveBellmanValue reward roots who prescribed time - prescribed time

/-- Pointwise difference between a Bellman cap and the prescribed value. -/
def quittingBellmanCapGap
    (prescribed cap : ℕ → ℝ) (time : ℕ) : ℝ :=
  cap time - prescribed time

/-- A supplied value sequence solves the pure-action Bellman maximum
recursion along the live path.  Its terminal selection is deliberately a
separate issue. -/
def IsQuittingLiveBellmanCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (cap : ℕ → ℝ) : Prop :=
  ∀ time, cap time = quittingLiveBellmanValue reward roots who cap time

/-- One Bellman step: the cap gap is at most the prescribed local residual
plus opponent survival times the next cap gap. -/
theorem quittingBellmanCapGap_le_residual_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (time : ℕ)
    (hnext : 0 ≤ quittingBellmanCapGap prescribed cap (time + 1)) :
    quittingBellmanCapGap prescribed cap time ≤
      quittingPrescribedOneStepResidual reward roots who prescribed time +
        quittingFixedOpponentsContinueMass roots who time *
          quittingBellmanCapGap prescribed cap (time + 1) := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots who time
  let continueValue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * prescribed (time + 1)
  let continueMass := quittingFixedOpponentsContinueMass roots who time
  let nextGap := quittingBellmanCapGap prescribed cap (time + 1)
  have hmass : 0 ≤ continueMass := by
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false))
  have hscaled : 0 ≤ continueMass * nextGap :=
    mul_nonneg hmass hnext
  have hcontinue :
      quittingFixedOpponentsContinueReward reward roots who time +
          continueMass * cap (time + 1) =
        continueValue + continueMass * nextGap := by
    dsimp [continueValue, nextGap, quittingBellmanCapGap]
    ring
  have hmax :
      max quitValue (continueValue + continueMass * nextGap) ≤
        max quitValue continueValue + continueMass * nextGap := by
    apply max_le
    · linarith [le_max_left quitValue continueValue]
    · linarith [le_max_right quitValue continueValue]
  unfold quittingBellmanCapGap quittingPrescribedOneStepResidual
  rw [hcap time]
  unfold quittingLiveBellmanValue
  change
    max quitValue
          (quittingFixedOpponentsContinueReward reward roots who time +
            continueMass * cap (time + 1)) - prescribed time ≤
      (max quitValue continueValue - prescribed time) +
        continueMass * nextGap
  rw [hcontinue]
  linarith

end GameTheory
