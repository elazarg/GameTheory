/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import GameTheory.Concepts.Stochastic.QuittingPunishmentFreeReduction

/-!
# The one-player obstruction to ledger-cap producers

For a one-player quitting game, deleting the designated player's action leaves
an empty opponent set, whose survival weight is identically one.  Consequently
the reach term in either ledger-cap interface cannot tend to zero.

For the constant singleton reward `1`, a truncated package at error `ε`
would force `5 ≤ ε`; a phase-switch package would force `6 ≤ ε`.
Both interfaces therefore fail at `ε = 1`, although the underlying
one-player game plainly has an equilibrium.  The obstruction belongs to the
quantitative package, not to finite-quitting equilibrium existence.
-/

noncomputable section

namespace GameTheory

/-- The one-player quitting reward whose unique terminal payoff is `1`. -/
def quittingLedgerCapPackageUnitReward :
    {S : Finset Unit // S.Nonempty} → Payoff Unit :=
  fun _ _ => 1

/-- Deleted opponent survival is one in every one-player plan. -/
theorem quittingOpponentSurvivalWeight_unit
    (plan : ℕ → Unit → PMF Bool) (switch : ℕ) :
    quittingOpponentSurvivalWeight plan () 0 switch = 1 := by
  simp [quittingOpponentSurvivalWeight, quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass, quittingAllContinueAction]

/-- Any one-player phase-switch package pays at least six reward-bound units
in its assembled error. -/
theorem six_mul_quittingRewardBound_le_of_hasQuittingLedgerCapPackage_unit
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) (ε : ℝ)
    (hpackage : HasQuittingLedgerCapPackage reward ε) :
    6 * quittingRewardBound reward ≤ ε := by
  obtain ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach, punishError, punishCap,
    hquitRegretCap, hledger, hregret, hreach, hpunish, herror⟩ := hpackage
  have hledgerCap : 0 ≤ ledgerCap := by
    simpa using hledger () 0 (Nat.zero_le switch)
  have hreachOne : 1 ≤ reach := by
    simpa [quittingOpponentSurvivalWeight_unit plan switch] using hreach ()
  have hbound : 0 ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
  have htail : 0 ≤ max (punishCap () + punishError) 0 +
      quittingRewardBound reward := by
    exact add_nonneg (le_max_right _ _) hbound
  have htailLower : quittingRewardBound reward ≤
      max (punishCap () + punishError) 0 + quittingRewardBound reward := by
    linarith [le_max_right (punishCap () + punishError) 0]
  have hreachTail : quittingRewardBound reward ≤ reach *
      (max (punishCap () + punishError) 0 + quittingRewardBound reward) := by
    have hmul := mul_le_mul htailLower hreachOne (by positivity) htail
    simpa [mul_comm] using hmul
  have hreachFive : 5 * quittingRewardBound reward ≤ reach *
      (5 * quittingRewardBound reward) := by
    have hmul := mul_le_mul_of_nonneg_right hreachOne
      (by positivity : 0 ≤ 5 * quittingRewardBound reward)
    simpa using hmul
  have herror' := herror ()
  linarith

/-- The constant-one one-player reward has no phase-switch package at error
one. -/
theorem not_hasQuittingLedgerCapPackage_unit_one :
    ¬ HasQuittingLedgerCapPackage quittingLedgerCapPackageUnitReward 1 := by
  intro hpackage
  have h := six_mul_quittingRewardBound_le_of_hasQuittingLedgerCapPackage_unit
    quittingLedgerCapPackageUnitReward 1 hpackage
  have hbound : 1 ≤ quittingRewardBound quittingLedgerCapPackageUnitReward := by
    have h' := abs_reward_le_quittingRewardBound
      quittingLedgerCapPackageUnitReward (quittingSingletonTerminal ()) ()
    change |(1 : ℝ)| ≤ quittingRewardBound quittingLedgerCapPackageUnitReward at h'
    norm_num at h' ⊢
    exact h'
  linarith

/-- Phase-switch ledger packages do not exist at every positive tolerance for
arbitrary finite player types. -/
theorem not_forall_hasQuittingLedgerCapPackage :
    ¬ (∀ (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
        (ε : ℝ), 0 < ε → HasQuittingLedgerCapPackage reward ε) := by
  intro h
  exact not_hasQuittingLedgerCapPackage_unit_one
    (h quittingLedgerCapPackageUnitReward 1 (by norm_num))

/-- Any one-player truncated package pays at least five reward-bound units in
its error estimate. -/
theorem five_mul_quittingRewardBound_le_of_hasQuittingTruncatedLedgerCapPackage_unit
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) (ε : ℝ)
    (hpackage : HasQuittingTruncatedLedgerCapPackage reward ε) :
    5 * quittingRewardBound reward ≤ ε := by
  obtain ⟨plan, switch, ledgerCap, quitRegretCap, reach,
    hquitRegretCap, hledger, _hregret, hreach, herror⟩ := hpackage
  have hledgerCap : 0 ≤ ledgerCap := by
    simpa using hledger () 0 (Nat.zero_le switch)
  have hreachOne : 1 ≤ reach := by
    simpa [quittingOpponentSurvivalWeight_unit plan switch] using hreach ()
  have hbound : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward
  have hreachFive : 5 * quittingRewardBound reward ≤
      reach * (5 * quittingRewardBound reward) := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hreachOne
        (by positivity : 0 ≤ 5 * quittingRewardBound reward))
  linarith [herror ()]

/-- The constant-one one-player reward has no truncated ledger package at
error one. -/
theorem not_hasQuittingTruncatedLedgerCapPackage_unit_one :
    ¬ HasQuittingTruncatedLedgerCapPackage
      quittingLedgerCapPackageUnitReward 1 := by
  intro hpackage
  have h :=
    five_mul_quittingRewardBound_le_of_hasQuittingTruncatedLedgerCapPackage_unit
      quittingLedgerCapPackageUnitReward 1 hpackage
  have hbound : 1 ≤ quittingRewardBound quittingLedgerCapPackageUnitReward := by
    have h' := abs_reward_le_quittingRewardBound
      quittingLedgerCapPackageUnitReward (quittingSingletonTerminal ()) ()
    change |(1 : ℝ)| ≤ quittingRewardBound quittingLedgerCapPackageUnitReward at h'
    norm_num at h' ⊢
    exact h'
  linarith

/-- Truncated ledger-cap packages do not exist at every positive tolerance
for arbitrary finite player types. -/
theorem not_forall_hasQuittingTruncatedLedgerCapPackage :
    ¬ (∀ (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
        (ε : ℝ), 0 < ε → HasQuittingTruncatedLedgerCapPackage reward ε) := by
  intro h
  exact not_hasQuittingTruncatedLedgerCapPackage_unit_one
    (h quittingLedgerCapPackageUnitReward 1 (by norm_num))

end GameTheory
