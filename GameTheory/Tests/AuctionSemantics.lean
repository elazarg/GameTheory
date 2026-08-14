/-
# Quasilinear auction certificates

The allocation responds to reports, assigns one winner, and uses zero
transfers.  This exercises the quasilinear IR, transfer, and balance predicates
on a nonconstant rule rather than merely checking that their names elaborate.
-/

import GameTheory.Mechanism.Auction
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.Tests.AuctionSemantics

open GameTheory.Mechanism.Auction

def binaryAllocation (reports : Fin 2 → Bool) : Fin 2 :=
  if reports 0 then 0 else 1

def zeroPayment (_reports : Fin 2 → Bool) (_who : Fin 2) : ℝ := 0

def winnerValue (who : Fin 2) (winner : Fin 2) : ℝ :=
  if winner = who then 1 else 0

abbrev binaryGame : UtilityGame (Fin 2) :=
  auctionGame binaryAllocation zeroPayment winnerValue

abbrev binaryQuasiLinear : QuasiLinear binaryGame :=
  auctionGame_quasiLinear binaryAllocation zeroPayment winnerValue

theorem allocation_responds_to_reports :
    binaryAllocation ![true, false] = 0 ∧
      binaryAllocation ![false, false] = 1 := by
  decide

theorem binary_nonnegativeUtility_everyOutcome :
    binaryQuasiLinear.HasNonnegativeUtilityAtEveryOutcome := by
  intro reports who
  simp only [binaryQuasiLinear, auctionGame_quasiLinear, zeroPayment,
    winnerValue]
  split <;> norm_num

theorem binary_noPositiveTransfers :
    binaryQuasiLinear.NoPositiveTransfers := by
  intro reports who
  norm_num [binaryQuasiLinear, auctionGame_quasiLinear, zeroPayment]

theorem binary_isStronglyBudgetBalanced :
    binaryQuasiLinear.IsStronglyBudgetBalanced := by
  intro reports
  norm_num [binaryQuasiLinear, auctionGame_quasiLinear, zeroPayment,
    Fin.sum_univ_two]

/-! ## Nonzero-transfer discrimination -/

/-- A positive, report-sensitive fee. Valuations below are deliberately high
enough that the fee remains individually rational. -/
def positiveFee (reports : Fin 2 → Bool) (who : Fin 2) : ℝ :=
  if reports who then 1 else 1 / 2

def highValue (_who : Fin 2) (_winner : Fin 2) : ℝ := 2

abbrev feeGame : UtilityGame (Fin 2) :=
  auctionGame binaryAllocation positiveFee highValue

abbrev feeQuasiLinear : QuasiLinear feeGame :=
  auctionGame_quasiLinear binaryAllocation positiveFee highValue

theorem positiveFee_is_nonzero :
    positiveFee ![true, false] 0 = 1 ∧
      positiveFee ![true, false] 1 = 1 / 2 := by
  norm_num [positiveFee]

theorem fee_nonnegativeUtility_everyOutcome :
    feeQuasiLinear.HasNonnegativeUtilityAtEveryOutcome := by
  intro reports who
  show positiveFee reports who ≤ highValue who (binaryAllocation reports)
  cases hreport : reports who <;> norm_num [positiveFee, highValue, hreport]

theorem fee_noPositiveTransfers : feeQuasiLinear.NoPositiveTransfers := by
  intro reports who
  show 0 ≤ positiveFee reports who
  cases hreport : reports who <;> norm_num [positiveFee, hreport]

/-- Collecting strictly positive fees cannot be strongly budget balanced. -/
theorem fee_not_isStronglyBudgetBalanced :
    ¬ feeQuasiLinear.IsStronglyBudgetBalanced := by
  intro hbalanced
  have h := hbalanced ![true, true]
  have h' : (∑ who, positiveFee ![true, true] who) = 0 := h
  norm_num [positiveFee, Fin.sum_univ_two] at h'

/-- A genuine balanced transfer: player zero pays one and player one receives
one. This independently exercises budget balance away from zero. -/
def balancedTransfer (_reports : Fin 2 → Bool) (who : Fin 2) : ℝ :=
  if who = 0 then 1 else -1

abbrev balancedGame : UtilityGame (Fin 2) :=
  auctionGame binaryAllocation balancedTransfer highValue

abbrev balancedQuasiLinear : QuasiLinear balancedGame :=
  auctionGame_quasiLinear binaryAllocation balancedTransfer highValue

theorem balancedTransfer_is_nonzero :
    balancedTransfer ![false, true] 0 = 1 ∧
      balancedTransfer ![false, true] 1 = -1 := by
  norm_num [balancedTransfer]

theorem balanced_nonnegativeUtility_everyOutcome :
    balancedQuasiLinear.HasNonnegativeUtilityAtEveryOutcome := by
  intro reports who
  show balancedTransfer reports who ≤ highValue who (binaryAllocation reports)
  fin_cases who <;>
    norm_num [balancedTransfer, highValue]

theorem balanced_isStronglyBudgetBalanced :
    balancedQuasiLinear.IsStronglyBudgetBalanced := by
  intro reports
  show (∑ who, balancedTransfer reports who) = 0
  norm_num [balancedTransfer, Fin.sum_univ_two]

/-- Budget balance does not imply no positive transfers: player one receives
a unit subsidy. -/
theorem balanced_not_noPositiveTransfers :
    ¬ balancedQuasiLinear.NoPositiveTransfers := by
  intro htransfer
  have h := htransfer (fun _ => false) 1
  have h' : 0 ≤ balancedTransfer (fun _ => false) 1 := h
  norm_num [balancedTransfer] at h'

def overcharge (_reports : Fin 2 → Bool) (who : Fin 2) : ℝ :=
  if who = 0 then 3 else 0

abbrev overchargeGame : UtilityGame (Fin 2) :=
  auctionGame binaryAllocation overcharge highValue

abbrev overchargeQuasiLinear : QuasiLinear overchargeGame :=
  auctionGame_quasiLinear binaryAllocation overcharge highValue

/-- A payment above value falsifies ex-post individual rationality. -/
theorem overcharge_has_negativeUtility_outcome :
    ¬ overchargeQuasiLinear.HasNonnegativeUtilityAtEveryOutcome := by
  intro hir
  have h := hir (fun _ => false) 0
  have h' : overcharge (fun _ => false) 0 ≤
      highValue 0 (binaryAllocation (fun _ => false)) := h
  norm_num [overcharge, highValue] at h'

end GameTheory.Tests.AuctionSemantics
