/-
# Quasilinear auction certificates

The allocation responds to reports, assigns one winner, and uses zero
transfers.  This exercises the quasilinear IR, transfer, and balance predicates
on a nonconstant rule rather than merely checking that their names elaborate.
-/

import GameTheory.Mechanism.Auction

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

theorem binary_isExPostIR : binaryQuasiLinear.IsExPostIR := by
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

end GameTheory.Tests.AuctionSemantics
