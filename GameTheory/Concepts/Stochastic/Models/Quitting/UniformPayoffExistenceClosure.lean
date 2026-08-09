/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Models.Quitting.Game
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform.PayoffExistenceClosure

/-!
# Uniform-payoff existence under limits of quitting reward tables

All quitting games on a fixed finite player type have the same states,
actions, transition kernel, and discount field; only their terminal reward
tables vary.  This module specializes fixed-skeleton stage-payoff closure to
that natural parameterization.

Uniform convergence is required only on nonempty quitter sets and players.
The active-state payoff is identically zero, so this is exactly uniform
convergence of the induced stage-payoff tables.  No density or stability of
the transition kernel is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι]

/-- Replacing the stage payoff of a quitting game by the stage payoff induced
by another terminal reward table recovers the latter quitting game. -/
@[simp] theorem quittingGame_withStagePayoff_eq
    (base nearby : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame base).withStagePayoff (quittingGame nearby).stagePayoff =
      quittingGame nearby :=
  rfl

/-- Uniform-equilibrium-payoff existence is closed under uniform limits of
quitting terminal reward tables.  The equilibrium payoff may vary along the
approximating sequence; finite-dimensional compactness selects a limit. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_uniform_reward_limit
    [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (approximation : ℕ → {S : Finset ι // S.Nonempty} → Payoff ι)
    (happroximation : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ S who, |approximation n S who - reward S who| ≤ η)
    (hUE : ∀ n, ∃ w : Payoff ι,
      (quittingGame (approximation n)).IsUniformEquilibriumPayoff none w) :
    ∃ v : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none v := by
  haveI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  haveI : ∀ i : ι, Finite ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  apply StochasticGame.exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit
    (quittingGame reward) none
      (fun n => (quittingGame (approximation n)).stagePayoff)
  · intro η hη
    obtain ⟨N, hN⟩ := happroximation η hη
    refine ⟨N, fun n hn s a who => ?_⟩
    cases s with
    | none => simpa [quittingGame] using hη.le
    | some S => simpa [quittingGame] using hN n hn S who
  · intro n
    simpa using hUE n

/-- If arbitrarily close quitting reward tables admit uniform-equilibrium
payoffs, then the original quitting game admits one as well.  This is the
direct approximation form of uniform reward-table closure. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards
    [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (happroximation : ∀ η : ℝ, 0 < η →
      ∃ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) ∧
        ∃ w : Payoff ι,
          (quittingGame nearby).IsUniformEquilibriumPayoff none w) :
    ∃ v : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none v := by
  haveI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  haveI : ∀ i : ι, Finite ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  apply StochasticGame.exists_uniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs
    (quittingGame reward) none
  intro η hη
  obtain ⟨nearby, hnearby, w, hw⟩ := happroximation η hη
  refine ⟨(quittingGame nearby).stagePayoff, ?_, w, ?_⟩
  · intro s a who
    cases s with
    | none => simpa [quittingGame] using hη.le
    | some S => simpa [quittingGame] using hnearby S who
  · simpa using hw

end GameTheory
