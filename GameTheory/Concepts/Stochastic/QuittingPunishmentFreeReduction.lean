/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingLedgerCapPackage

/-!
# Truncated ledger-cap packages

This module isolates the ledger data needed by the finite truncation fold.
Such a package consists of a root sequence, a truncation index, bounds for its
ledger and quit regret, a deleted opponent-survival bound, and the resulting
error inequality.  The truncated sequence itself is terminal approximate
Nash against every behavioral deviation.

Packages at every positive tolerance therefore yield a uniform-equilibrium
payoff by compact payoff selection.  In particular, no continuation chosen to
punish every possible deviator is needed for this existence conclusion.

`HasQuittingLedgerCapPackage` is a stronger phase-switch interface.  The final
theorem shows that every phase-switch package contains a truncated package;
its punishment plan and its second reach-weighted error term can be discarded.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Ledger and reach data sufficient to make a finite truncation terminal
`ε`-Nash.  The error condition is playerwise to match the unilateral Nash
conclusion and to remain meaningful for an empty player type. -/
def HasQuittingTruncatedLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan : ℕ → ι → PMF Bool) (switch : ℕ)
      (ledgerCap quitRegretCap reach : ℝ),
    0 ≤ quitRegretCap ∧
    (∀ (who : ι) (index : ℕ), index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap) ∧
    (∀ (who : ι) (stage : ℕ), stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap) ∧
    (∀ who : ι,
      quittingOpponentSurvivalWeight plan who 0 switch ≤ reach) ∧
    (∀ _ : ι, ledgerCap + quitRegretCap +
      reach * (5 * quittingRewardBound reward) ≤ ε)

/-- A truncated ledger-cap package produces a terminal `ε`-Nash profile
against arbitrary behavioral deviations. -/
theorem exists_isεAsymptoticNash_of_hasQuittingTruncatedLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingTruncatedLedgerCapPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨plan, switch, ledgerCap, quitRegretCap, reach,
    hquitRegretCap, hledger, hregret, hreach, herror⟩ := hpackage
  refine ⟨quittingRootSequenceProfile reward
    (quittingTruncatedRoots plan switch) 0, ?_⟩
  intro who deviation
  have hcap :=
    quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
      reward plan who switch
      (quittingRewardBound_nonneg reward) hquitRegretCap
      (abs_reward_le_quittingRewardBound reward)
      (hledger who) (hregret who) (hreach who)
      (quittingBehaviorLiveHazard reward deviation)
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  simp only [quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  exact hcap.trans (add_le_add_right (herror who) _)

/-- Truncated ledger-cap packages at every positive tolerance yield a single
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_truncatedLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε →
      HasQuittingTruncatedLedgerCapPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    fun ε hε =>
      exists_isεAsymptoticNash_of_hasQuittingTruncatedLedgerCapPackage
        reward (hpackage ε hε)

/-- Every phase-switch ledger package contains a truncated ledger package.
The punishment bound and the second reach-weighted error term are unnecessary
for the truncation conclusion. -/
theorem hasQuittingTruncatedLedgerCapPackage_of_hasQuittingLedgerCapPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingLedgerCapPackage reward ε) :
    HasQuittingTruncatedLedgerCapPackage reward ε := by
  obtain ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach,
    punishError, punishCap, hquitRegretCap, hledger, hregret, hreach,
    hpunish, herror⟩ := hpackage
  refine ⟨plan, switch, ledgerCap, quitRegretCap, reach,
    hquitRegretCap, hledger, hregret, hreach, ?_⟩
  intro who
  have hreachNonneg : 0 ≤ reach :=
    (quittingOpponentSurvivalWeight_nonneg plan who 0 switch).trans
      (hreach who)
  have htailFactorNonneg :
      0 ≤ max (punishCap who + punishError) 0 +
        quittingRewardBound reward :=
    add_nonneg (le_max_right _ _) (quittingRewardBound_nonneg reward)
  have htailNonneg :
      0 ≤ reach *
        (max (punishCap who + punishError) 0 +
          quittingRewardBound reward) :=
    mul_nonneg hreachNonneg htailFactorNonneg
  linarith [herror who]

end GameTheory
