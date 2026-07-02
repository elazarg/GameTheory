/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Auctions.Basic

/-!
# Vickrey Auction with a Reserve Price

In a second-price sealed-bid auction with reserve `reserve`, the item is
allocated only when a bid strictly exceeds both the reserve and every other
bid.  The winner pays the larger of the reserve and the highest opposing bid.

The main result is that truthful bidding is a weakly dominant strategy.
-/

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ReserveVickrey

open Classical in
/-- The bid threshold faced by `who`: the larger of the reserve price and the
highest bid among opponents. -/
noncomputable def reserveVickreyClearingPrice (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) : ℝ :=
  max reserve (maxOtherBid bids who)

open Classical in
/-- Player `who` wins the reserve Vickrey auction exactly when their bid
strictly exceeds their reserve-inclusive threshold. -/
def reserveVickreyWins (reserve : ℝ) (bids : ι → ℝ) (who : ι) : Prop :=
  bids who > reserveVickreyClearingPrice reserve bids who

open Classical in
/-- The clearing price faced by `who` is independent of `who`'s own bid. -/
theorem reserveVickreyClearingPrice_update_self (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) (b : ℝ) :
    reserveVickreyClearingPrice reserve (Function.update bids who b) who =
      reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyClearingPrice, maxOtherBid_update_self]

open Classical in
/-- Every opponent's bid is bounded by the maximum bid among opponents. -/
theorem bid_le_maxOtherBid_of_ne (bids : ι → ℝ) {who other : ι}
    (hne : other ≠ who) :
    bids other ≤ maxOtherBid bids who := by
  unfold maxOtherBid
  let others := Finset.univ.filter (· ≠ who)
  have hmem : other ∈ others := by
    simp [others, hne]
  have hnonempty : others.Nonempty := ⟨other, hmem⟩
  rw [dif_pos hnonempty]
  exact Finset.le_sup' bids hmem

open Classical in
/-- At most one player can strictly beat their reserve-inclusive threshold. -/
theorem reserveVickreyWins_unique (reserve : ℝ) (bids : ι → ℝ) {i j : ι}
    (hi : reserveVickreyWins reserve bids i)
    (hj : reserveVickreyWins reserve bids j) :
    i = j := by
  by_contra hne
  have hji : j ≠ i := fun h => hne h.symm
  have hj_le_other : bids j ≤ maxOtherBid bids i :=
    bid_le_maxOtherBid_of_ne bids hji
  have hi_le_other : bids i ≤ maxOtherBid bids j :=
    bid_le_maxOtherBid_of_ne bids hne
  have hj_le_price : bids j ≤ reserveVickreyClearingPrice reserve bids i :=
    le_trans hj_le_other (le_max_right reserve (maxOtherBid bids i))
  have hi_le_price : bids i ≤ reserveVickreyClearingPrice reserve bids j :=
    le_trans hi_le_other (le_max_right reserve (maxOtherBid bids j))
  unfold reserveVickreyWins at hi hj
  linarith

open Classical in
/-- The winner of the reserve Vickrey auction, if one exists.  Ties at the top
do not clear because no bidder strictly beats their highest opposing bid. -/
noncomputable def reserveVickreyAllocation (reserve : ℝ) (bids : ι → ℝ) :
    Option ι :=
  if h : ∃ who, reserveVickreyWins reserve bids who then
    some h.choose
  else
    none

open Classical in
/-- A player is returned by the allocation rule iff they strictly beat the
reserve-inclusive threshold. -/
theorem allocation_eq_some_iff (reserve : ℝ) (bids : ι → ℝ) (who : ι) :
    reserveVickreyAllocation reserve bids = some who ↔
      reserveVickreyWins reserve bids who := by
  constructor
  · intro halloc
    unfold reserveVickreyAllocation at halloc
    by_cases h : ∃ i, reserveVickreyWins reserve bids i
    · rw [dif_pos h] at halloc
      injection halloc with hchoose
      simpa [hchoose] using h.choose_spec
    · rw [dif_neg h] at halloc
      contradiction
  · intro hw
    unfold reserveVickreyAllocation
    have h : ∃ i, reserveVickreyWins reserve bids i := ⟨who, hw⟩
    rw [dif_pos h]
    have hchoose : h.choose = who :=
      reserveVickreyWins_unique reserve bids h.choose_spec hw
    simp [hchoose]

open Classical in
/-- The allocation rule returns `none` iff no bidder clears the reserve-inclusive
threshold. -/
theorem allocation_eq_none_iff (reserve : ℝ) (bids : ι → ℝ) :
    reserveVickreyAllocation reserve bids = none ↔
      ∀ who, ¬ reserveVickreyWins reserve bids who := by
  constructor
  · intro hnone who hw
    have hsome := (allocation_eq_some_iff reserve bids who).2 hw
    rw [hnone] at hsome
    contradiction
  · intro hno
    unfold reserveVickreyAllocation
    by_cases h : ∃ who, reserveVickreyWins reserve bids who
    · exact False.elim (hno h.choose h.choose_spec)
    · simp [h]

/-- The clearing price is definitionally the maximum of the reserve and the
highest bid excluding `who`. -/
theorem clearingPrice_eq_max_reserve_excluding
    (reserve : ℝ) (bids : ι → ℝ) (who : ι) :
    reserveVickreyClearingPrice reserve bids who =
      max reserve (maxOtherBid bids who) := by
  rfl

open Classical in
/-- A winner's clearing price is strictly below their bid. -/
theorem clearingPrice_lt_bid_of_allocation_eq_some (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyClearingPrice reserve bids who < bids who := by
  have hwin := (allocation_eq_some_iff reserve bids who).1 halloc
  simpa [reserveVickreyWins] using hwin

open Classical in
/-- A winner's clearing price is no more than their bid. -/
theorem clearingPrice_le_bid_of_allocation_eq_some (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyClearingPrice reserve bids who ≤ bids who :=
  le_of_lt (clearingPrice_lt_bid_of_allocation_eq_some reserve bids who halloc)

/-- A player's value for the single-item allocation. -/
def reserveVickreyValue (v : ι → ℝ) (who : ι) : Option ι → ℝ
  | some winner => if winner = who then v who else 0
  | none => 0

open Classical in
/-- Payments in the reserve Vickrey auction.  Only the winner pays, and the
winner pays their reserve-inclusive threshold. -/
noncomputable def reserveVickreyPayment (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) : ℝ :=
  if reserveVickreyAllocation reserve bids = some who then
    reserveVickreyClearingPrice reserve bids who
  else
    0

open Classical in
/-- The allocated bidder pays the reserve-inclusive clearing price. -/
theorem payment_of_allocation_eq_some (reserve : ℝ) (bids : ι → ℝ) (who : ι)
    (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyPayment reserve bids who =
      reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyPayment, halloc]

open Classical in
/-- A bidder who is not allocated the item pays zero. -/
theorem payment_of_allocation_ne_some (reserve : ℝ) (bids : ι → ℝ) (who : ι)
    (halloc : reserveVickreyAllocation reserve bids ≠ some who) :
    reserveVickreyPayment reserve bids who = 0 := by
  simp [reserveVickreyPayment, halloc]

open Classical in
/-- The allocated bidder never pays more than their reported bid. -/
theorem payment_le_bid_of_allocation_eq_some (reserve : ℝ) (bids : ι → ℝ)
    (who : ι) (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyPayment reserve bids who ≤ bids who := by
  rw [payment_of_allocation_eq_some reserve bids who halloc]
  exact clearingPrice_le_bid_of_allocation_eq_some reserve bids who halloc

open Classical in
/-- Quasi-linear utility in the reserve Vickrey auction. -/
noncomputable def reserveVickreyUtility (v : ι → ℝ) (reserve : ℝ)
    (bids : ι → ℝ) (who : ι) : ℝ :=
  reserveVickreyValue v who (reserveVickreyAllocation reserve bids) -
    reserveVickreyPayment reserve bids who

open Classical in
/-- If `who` wins, their utility is value minus the reserve-inclusive clearing
price. -/
theorem utility_winner (v : ι → ℝ) (reserve : ℝ) (bids : ι → ℝ) (who : ι)
    (hwin : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyUtility v reserve bids who =
      v who - reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, hwin]

open Classical in
/-- If `who` does not win, their utility is zero. -/
theorem utility_loser (v : ι → ℝ) (reserve : ℝ) (bids : ι → ℝ) (who : ι)
    (hlose : reserveVickreyAllocation reserve bids ≠ some who) :
    reserveVickreyUtility v reserve bids who = 0 := by
  cases halloc : reserveVickreyAllocation reserve bids with
  | none =>
      simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, halloc]
  | some winner =>
      have hne : winner ≠ who := by
        intro h
        apply hlose
        simp [halloc, h]
      simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, halloc, hne]

open Classical in
/-- Utility can be read directly from the threshold-winning predicate. -/
theorem reserveVickreyUtility_eq_if_wins (v : ι → ℝ) (reserve : ℝ)
    (bids : ι → ℝ) (who : ι) :
    reserveVickreyUtility v reserve bids who =
      if reserveVickreyWins reserve bids who then
        v who - reserveVickreyClearingPrice reserve bids who
      else
        0 := by
  by_cases hwin : reserveVickreyWins reserve bids who
  · have halloc := (allocation_eq_some_iff reserve bids who).2 hwin
    simp [hwin, utility_winner v reserve bids who halloc]
  · have halloc : reserveVickreyAllocation reserve bids ≠ some who := by
      intro hsome
      exact hwin ((allocation_eq_some_iff reserve bids who).1 hsome)
    simp [hwin, utility_loser v reserve bids who halloc]

open Classical in
/-- A truthful bidder has non-negative utility. -/
theorem utility_nonneg (v : ι → ℝ) (reserve : ℝ) (bids : ι → ℝ) (who : ι)
    (htruth : bids who = v who) :
    0 ≤ reserveVickreyUtility v reserve bids who := by
  by_cases halloc : reserveVickreyAllocation reserve bids = some who
  · rw [utility_winner v reserve bids who halloc, sub_nonneg]
    simpa [htruth] using
      clearingPrice_le_bid_of_allocation_eq_some reserve bids who halloc
  · rw [utility_loser v reserve bids who halloc]

open Classical in
/-- Truthful bidding weakly dominates every alternative bid in the reserve
Vickrey auction. -/
theorem truthful_weakly_dominant (v : ι → ℝ) (reserve : ℝ)
    (who : ι) (bids : ι → ℝ) (b' : ℝ) :
    reserveVickreyUtility v reserve (Function.update bids who (v who)) who ≥
      reserveVickreyUtility v reserve (Function.update bids who b') who := by
  rw [reserveVickreyUtility_eq_if_wins, reserveVickreyUtility_eq_if_wins]
  simp only [reserveVickreyWins, Function.update_self,
    reserveVickreyClearingPrice_update_self]
  set p := reserveVickreyClearingPrice reserve bids who
  by_cases htruth : v who > p
  · simp [htruth]
    by_cases hdev : b' > p
    · simp [hdev]
    · simp [hdev]
      linarith
  · simp [htruth]
    by_cases hdev : b' > p
    · simp [hdev]
      linarith
    · simp [hdev]

open Classical in
/-- The reserve Vickrey auction as a deterministic quasi-linear `KernelGame`.
Strategies are bids, and outcomes are bid profiles. -/
noncomputable def reserveVickreyGame (v : ι → ℝ) (reserve : ℝ) :
    KernelGame ι :=
  KernelGame.auctionGame (reserveVickreyAllocation reserve)
    (reserveVickreyPayment reserve) (reserveVickreyValue v)

open Classical in
/-- Expected utility in `reserveVickreyGame` is the reserve Vickrey utility. -/
@[simp] theorem reserveVickreyGame_eu (v : ι → ℝ) (reserve : ℝ)
    (bids : ι → ℝ) (who : ι) :
    (reserveVickreyGame v reserve).eu bids who =
      reserveVickreyUtility v reserve bids who := by
  simp [reserveVickreyGame, reserveVickreyUtility]

open Classical in
/-- Truthful bidding is a dominant strategy for each valuation in the reserve
Vickrey game. -/
theorem valuation_is_dominant (v : ι → ℝ) (reserve : ℝ) (who : ι) :
    (reserveVickreyGame v reserve).IsDominant who (v who) := by
  intro σ s'
  simp only [reserveVickreyGame_eu]
  exact truthful_weakly_dominant v reserve who σ s'

open Classical in
/-- The reserve Vickrey mechanism is dominant-strategy incentive compatible. -/
theorem mechanism_isDSIC (v : ι → ℝ) (reserve : ℝ) :
    ∀ who, (reserveVickreyGame v reserve).IsDominant who (v who) :=
  valuation_is_dominant v reserve

open Classical in
/-- The truthful bid profile is a Nash equilibrium of the reserve Vickrey game. -/
theorem reserveVickrey_truthful_isNash (v : ι → ℝ) (reserve : ℝ) :
    (reserveVickreyGame v reserve).IsNash v := by
  exact KernelGame.dominant_is_nash _ _ (mechanism_isDSIC v reserve)

end ReserveVickrey

end GameTheory
