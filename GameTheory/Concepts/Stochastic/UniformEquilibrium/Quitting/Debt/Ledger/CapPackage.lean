/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Ledger.TruncationLedgerFold
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Phase-switch ledger-cap packages

This module defines the quantitative interface consumed by the phase-switch
construction.  It combines a controlled planning prefix with a continuation
plan that bounds every player's unilateral payoff after the switch.  The
assembled profile is terminal approximate Nash, and packages at every
positive tolerance yield a uniform-equilibrium payoff.

This interface is sufficient but not necessary.  For existence of an
unspecified uniform payoff, `HasQuittingTruncatedLedgerCapPackage` retains
only the planning prefix and is better suited as a producer target.  The
present interface remains useful when a phase-switch continuation or its
explicit deviation cap is required.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Data sufficient for the phase-switch deviation bound: a controlled plan
prefix, a shared continuation plan, their caps, and the assembled playerwise
error inequality. -/
def HasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan punish : ℕ → ι → PMF Bool) (switch : ℕ)
      (ledgerCap quitRegretCap reach punishError : ℝ) (punishCap : ι → ℝ),
    0 ≤ quitRegretCap ∧
    (∀ (who : ι) (index : ℕ), index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap) ∧
    (∀ (who : ι) (stage : ℕ), stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap) ∧
    (∀ who : ι, quittingOpponentSurvivalWeight plan who 0 switch ≤ reach) ∧
    (∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap who + punishError) ∧
    (∀ who : ι,
      (ledgerCap + quitRegretCap + reach * (5 * quittingRewardBound reward)) +
        reach * (max (punishCap who + punishError) 0 + quittingRewardBound reward) ≤ ε)

/-- A phase-switch ledger package yields a terminal `ε`-Nash profile against
arbitrary behavioral deviations. -/
theorem exists_isεAsymptoticNash_of_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingLedgerCapPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach, punishError, punishCap,
    hquitRegretCap, hledger, hregret, hreach, hpunish, herror⟩ := hpackage
  refine ⟨quittingPhaseSwitchProfile reward plan punish switch, ?_⟩
  refine isεAsymptoticNash_quittingPhaseSwitchProfile reward plan punish switch
    (planError := ledgerCap + quitRegretCap + reach * (5 * quittingRewardBound reward))
    (survivalCap := reach) (bound := quittingRewardBound reward)
    (quittingRewardBound_nonneg reward) (abs_reward_le_quittingRewardBound reward)
    (fun who g => ?_) hpunish hreach herror
  exact quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
    reward plan who switch (quittingRewardBound_nonneg reward) hquitRegretCap
    (abs_reward_le_quittingRewardBound reward) (hledger who) (hregret who) (hreach who) g

/-- Phase-switch ledger packages at every positive tolerance imply a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε → HasQuittingLedgerCapPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    fun ε hε =>
      exists_isεAsymptoticNash_of_hasQuittingLedgerCapPackage reward (hpackage ε hε)

end GameTheory
