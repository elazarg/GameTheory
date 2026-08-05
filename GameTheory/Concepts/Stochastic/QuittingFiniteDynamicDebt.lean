/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteChainTerminalCompiler
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits

/-!
# Exact dynamic debt on a finite quitting chain

The surviving singleton debt used by the finite-chain compiler is a useful
upper envelope, but it is not the actual dynamic exploitability.  Local
strictness can discharge some or all of that envelope before the root.

This file records the exact backward scalar recursion.  Starting with a
nonnegative terminal debt `terminalDebt`, `quittingFiniteDynamicDebt` applies
the player's pure-action Bellman maximum backwards through a supplied root
sequence and subtracts the prescribed value.  Under genuine prescribed
policy evaluation the debt is nonnegative, so the recursion is exactly a
positive-part Bellman recursion.  It is bounded above
by the familiar survival-weighted terminal debt when every local residual is
zero.

The definition is a finite Bellman quantity.  No compactness, recurrence, or
infinite-tail conclusion is encoded in it.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact finite backward Bellman debt above a supplied prescribed value.
At zero fuel the supplied terminal debt is returned. -/
def quittingFiniteDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => terminalDebt
  | start, fuel + 1 =>
      max (quittingFixedOpponentsQuitValue reward roots who start)
          (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              (prescribed (start + 1) +
                quittingFiniteDynamicDebt reward roots who prescribed
                  terminalDebt (start + 1) fuel)) -
        prescribed start

@[simp] theorem quittingFiniteDynamicDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ) (start : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
      start 0 = terminalDebt := rfl

/-- The defining one-step exact dynamic-debt recursion. -/
theorem quittingFiniteDynamicDebt_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      max (quittingFixedOpponentsQuitValue reward roots who start)
          (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              (prescribed (start + 1) +
                quittingFiniteDynamicDebt reward roots who prescribed
                  terminalDebt (start + 1) fuel)) -
        prescribed start := rfl

/-- Dynamic debt is nonnegative when the prescribed sequence is an actual
policy value and the terminal debt is nonnegative. -/
theorem quittingFiniteDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt) :
    ∀ start fuel,
      0 ≤ quittingFiniteDynamicDebt reward roots who prescribed
        terminalDebt start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      simpa using hterminalDebt
  | succ fuel ih =>
      have hnext := ih (start + 1)
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hcontinue :
          quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                prescribed (start + 1) ≤
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                (prescribed (start + 1) +
                  quittingFiniteDynamicDebt reward roots who prescribed
                    terminalDebt (start + 1) fuel) := by
        nlinarith
      have hmax :
          quittingLiveBellmanValue reward roots who prescribed start ≤
            max (quittingFixedOpponentsQuitValue reward roots who start)
              (quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  (prescribed (start + 1) +
                    quittingFiniteDynamicDebt reward roots who prescribed
                      terminalDebt (start + 1) fuel)) := by
        unfold quittingLiveBellmanValue
        exact max_le_max le_rfl hcontinue
      have hpolicy : prescribed start ≤
          quittingLiveBellmanValue reward roots who prescribed start := by
        rw [hprescribed start]
        exact quittingRootSuccessorPayoff_le_liveBellmanValue
          reward roots who prescribed start
      rw [quittingFiniteDynamicDebt_succ]
      linarith

/-- Exact positive-part form of the recursion.  The outer maximum
does not change the value because genuine dynamic debt is nonnegative. -/
theorem quittingFiniteDynamicDebt_succ_eq_positivePart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      max
        (max (quittingFixedOpponentsQuitValue reward roots who start)
            (quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                (prescribed (start + 1) +
                  quittingFiniteDynamicDebt reward roots who prescribed
                    terminalDebt (start + 1) fuel)) -
          prescribed start)
        0 := by
  rw [quittingFiniteDynamicDebt_succ]
  exact (max_eq_left
    (quittingFiniteDynamicDebt_nonneg reward roots who prescribed
      hprescribed hterminalDebt start (fuel + 1))).symm

/-- One exact Bellman step is bounded by the prescribed local residual plus
opponent survival times the next exact debt. -/
theorem quittingFiniteDynamicDebt_succ_le_residual_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) ≤
      quittingPrescribedOneStepResidual reward roots who prescribed start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
            (start + 1) fuel := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots who start
  let continueValue :=
    quittingFixedOpponentsContinueReward reward roots who start +
      quittingFixedOpponentsContinueMass roots who start *
        prescribed (start + 1)
  let continueMass := quittingFixedOpponentsContinueMass roots who start
  let nextDebt := quittingFiniteDynamicDebt reward roots who prescribed
    terminalDebt (start + 1) fuel
  have hnext : 0 ≤ nextDebt :=
    quittingFiniteDynamicDebt_nonneg reward roots who prescribed
      hprescribed hterminalDebt (start + 1) fuel
  have hmass : 0 ≤ continueMass :=
    quittingStationaryContinueMass_nonneg
      (Function.update (roots start) who (PMF.pure false))
  have hscaled : 0 ≤ continueMass * nextDebt := mul_nonneg hmass hnext
  have hmax :
      max quitValue (continueValue + continueMass * nextDebt) ≤
        max quitValue continueValue + continueMass * nextDebt := by
    apply max_le
    · linarith [le_max_left quitValue continueValue]
    · linarith [le_max_right quitValue continueValue]
  rw [quittingFiniteDynamicDebt_succ]
  unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue
  dsimp only [quitValue, continueValue, continueMass, nextDebt] at hmax ⊢
  convert sub_le_sub_right hmax (prescribed start) using 1 <;> ring_nf

/-- If every displayed local residual vanishes, exact dynamic debt is at
most the coarse survival-weighted terminal envelope. -/
theorem quittingFiniteDynamicDebt_le_survival_mul_terminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel ≤
      quittingOpponentSurvivalWeight roots who start fuel * terminalDebt := by
  induction fuel generalizing start with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep := quittingFiniteDynamicDebt_succ_le_residual_add
        reward roots who prescribed hprescribed hterminalDebt start fuel
      rw [hresidual start, zero_add] at hstep
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hscaled := mul_le_mul_of_nonneg_left (ih (start + 1)) hmass
      calc
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
            start (fuel + 1) ≤
          quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
              (start + 1) fuel := hstep
        _ ≤ quittingFixedOpponentsContinueMass roots who start *
            (quittingOpponentSurvivalWeight roots who (start + 1) fuel *
              terminalDebt) := hscaled
        _ = quittingOpponentSurvivalWeight roots who start (fuel + 1) *
            terminalDebt := by
          rw [show quittingOpponentSurvivalWeight roots who start (fuel + 1) =
              quittingOpponentSurvivalWeight roots who start 1 *
                quittingOpponentSurvivalWeight roots who (start + 1) fuel by
            simpa [Nat.add_comm] using quittingOpponentSurvivalWeight_add
              roots who start 1 fuel]
          simp [quittingOpponentSurvivalWeight]
          ring

end GameTheory
