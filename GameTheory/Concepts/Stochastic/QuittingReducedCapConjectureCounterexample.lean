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

/-- Any one-player ledger-cap package has tolerance at least six times the
canonical reward bound. This is forced before using the punishment-cap clause:
the ledger and regret caps are nonnegative, deleted reach is at least one,
and the two reward-range terms in clause `(A)` contribute `5 * bound` and
`bound`. -/
theorem six_mul_quittingRewardBound_le_of_hasQuittingLedgerCapPackage_unit
    (reward : {S : Finset Unit // S.Nonempty} → Payoff Unit) (ε : ℝ)
    (hpackage : HasQuittingLedgerCapPackage reward ε) :
    6 * quittingRewardBound reward ≤ ε := by
  obtain ⟨plan, punish, switch, ledgerCap, quitRegretCap, reach, punishError,
    punishCap, hquitRegretCap, hledger, _hregret, hreach, _hpunish, herror⟩ := hpackage

  have hledgerCap : 0 ≤ ledgerCap := by
    simpa using hledger () 0 (Nat.zero_le switch)

  have hreachOne : 1 ≤ reach := by
    simpa only [quittingOpponentSurvivalWeight_unit] using hreach ()

  have hboundNonneg : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward

  have hreachFive :
      5 * quittingRewardBound reward ≤
        reach * (5 * quittingRewardBound reward) := by
    have hfiveNonneg : 0 ≤ 5 * quittingRewardBound reward :=
      mul_nonneg (by norm_num) hboundNonneg
    calc
      5 * quittingRewardBound reward =
          1 * (5 * quittingRewardBound reward) := by ring
      _ ≤ reach * (5 * quittingRewardBound reward) :=
        mul_le_mul_of_nonneg_right hreachOne hfiveNonneg

  have hmaxNonneg : 0 ≤ max (punishCap () + punishError) 0 :=
    le_max_right _ _

  have hreachPunishment :
      quittingRewardBound reward ≤
        reach *
          (max (punishCap () + punishError) 0 +
            quittingRewardBound reward) := by
    have hsumNonneg :
        0 ≤ max (punishCap () + punishError) 0 +
          quittingRewardBound reward :=
      add_nonneg hmaxNonneg hboundNonneg
    calc
      quittingRewardBound reward ≤
          max (punishCap () + punishError) 0 +
            quittingRewardBound reward := by
        linarith
      _ = 1 *
          (max (punishCap () + punishError) 0 +
            quittingRewardBound reward) := by ring
      _ ≤ reach *
          (max (punishCap () + punishError) 0 +
            quittingRewardBound reward) :=
        mul_le_mul_of_nonneg_right hreachOne hsumNonneg

  nlinarith [herror ()]

/-- The constant-one terminal reward on the one-player quitting game. -/
def quittingLedgerCapPackageUnitReward
    (_ : {S : Finset Unit // S.Nonempty}) : Payoff Unit :=
  fun _ => 1

/-- The proposed package cannot exist even at tolerance one for the
constant-one one-player quitting game. -/
theorem not_hasQuittingLedgerCapPackage_unit_one :
    ¬ HasQuittingLedgerCapPackage quittingLedgerCapPackageUnitReward 1 := by
  intro hpackage
  have hboundOne :
      1 ≤ quittingRewardBound quittingLedgerCapPackageUnitReward := by
    simpa [quittingLedgerCapPackageUnitReward] using
      (abs_reward_le_quittingRewardBound quittingLedgerCapPackageUnitReward
        (⟨{()}, by simp⟩ : {S : Finset Unit // S.Nonempty}) ())
  have hsix :=
    six_mul_quittingRewardBound_le_of_hasQuittingLedgerCapPackage_unit
      quittingLedgerCapPackageUnitReward 1 hpackage
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
