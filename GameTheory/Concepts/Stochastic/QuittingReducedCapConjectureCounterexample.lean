/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingReducedCapConjecture

/-!
# The ledger-cap package fails for a one-player quitting game

For a one-player game the deleted, opponent-only survival weight is identically
one: there are no opponents who can make it small. Consequently clause (A) of
`HasQuittingLedgerCapPackage` pays at least six copies of the canonical reward
bound, independently of the plan and punishment. The proposed all-tolerances
theorem is therefore false as stated.
-/

noncomputable section

namespace GameTheory

/-- In a one-player game, the opponent-only survival product is the empty
opponent product at every stage, hence is always one. -/
theorem quittingOpponentSurvivalWeight_unit
    (roots : ℕ → Unit → PMF Bool) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots () start fuel = 1 := by
  simp [quittingOpponentSurvivalWeight, quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]

/-- The constant-one terminal reward on the one-player quitting game. -/
def quittingLedgerCapPackageUnitReward
    (_ : {S : Finset Unit // S.Nonempty}) : Payoff Unit :=
  fun _ => 1

/-- The proposed package cannot exist even at tolerance one for the
constant-one one-player quitting game. -/
theorem not_hasQuittingLedgerCapPackage_unit_one :
    ¬ HasQuittingLedgerCapPackage quittingLedgerCapPackageUnitReward 1 := by
  rintro ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach, punishError,
    punishCap, hquitRegretCap, hledger, _hregret, hreach, _hpunish, herror⟩

  have hledgerCap : 0 ≤ ledgerCap := by
    simpa using hledger () 0 (Nat.zero_le switch)

  have hreachOne : 1 ≤ reach := by
    simpa [quittingOpponentSurvivalWeight_unit] using hreach ()

  have hboundNonneg :
      0 ≤ quittingRewardBound quittingLedgerCapPackageUnitReward :=
    quittingRewardBound_nonneg quittingLedgerCapPackageUnitReward

  have hboundOne :
      1 ≤ quittingRewardBound quittingLedgerCapPackageUnitReward := by
    simpa [quittingLedgerCapPackageUnitReward] using
      (abs_reward_le_quittingRewardBound quittingLedgerCapPackageUnitReward
        (⟨{()}, by simp⟩ : {S : Finset Unit // S.Nonempty}) ())

  let punishmentTerm : ℝ := max (punishCap () + punishError) 0
  have hpunishmentTerm : 0 ≤ punishmentTerm := by
    dsimp [punishmentTerm]
    exact le_max_right _ _

  have hreachFive :
      5 * quittingRewardBound quittingLedgerCapPackageUnitReward ≤
        reach * (5 * quittingRewardBound quittingLedgerCapPackageUnitReward) := by
    have hproduct :
        0 ≤ (reach - 1) *
          (5 * quittingRewardBound quittingLedgerCapPackageUnitReward) :=
      mul_nonneg (sub_nonneg.mpr hreachOne)
        (mul_nonneg (by norm_num) hboundNonneg)
    nlinarith

  have hreachPunishment :
      quittingRewardBound quittingLedgerCapPackageUnitReward ≤
        reach *
          (punishmentTerm +
            quittingRewardBound quittingLedgerCapPackageUnitReward) := by
    have hsum :
        0 ≤ punishmentTerm +
          quittingRewardBound quittingLedgerCapPackageUnitReward :=
      add_nonneg hpunishmentTerm hboundNonneg
    have hproduct :
        0 ≤ (reach - 1) *
          (punishmentTerm +
            quittingRewardBound quittingLedgerCapPackageUnitReward) :=
      mul_nonneg (sub_nonneg.mpr hreachOne) hsum
    nlinarith

  have herr := herror ()
  change
    (ledgerCap + quitRegretCap +
        reach * (5 * quittingRewardBound quittingLedgerCapPackageUnitReward)) +
      reach *
        (punishmentTerm +
          quittingRewardBound quittingLedgerCapPackageUnitReward) ≤ 1 at herr
  nlinarith

/-- Hence the universal reduced conjecture itself is false at `Unit`, reward
one, and tolerance one. -/
theorem not_quittingGame_hasQuittingLedgerCapPackage_as_stated :
    ¬ (∀ (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit)
        (ε : ℝ), 0 < ε → HasQuittingLedgerCapPackage reward ε) := by
  intro hall
  exact not_hasQuittingLedgerCapPackage_unit_one
    (hall quittingLedgerCapPackageUnitReward 1 (by norm_num))

end GameTheory
