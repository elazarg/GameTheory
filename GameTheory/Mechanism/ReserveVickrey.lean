/-
# Reserve-price Vickrey auction

This opt-in single-item auction uses a strict-clear rule: a tied
top bid does not allocate.  It is built entirely from the generic deterministic
auction constructor and the canonical response predicates.
-/

import GameTheory.Mechanism.Auction

noncomputable section

namespace GameTheory.Mechanism.Auction

namespace ReserveVickrey

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The reserve-inclusive bid threshold faced by `who`. -/
def reserveVickreyClearingPrice (reserve : ℝ) (bids : BidProfile ι) (who : ι) : ℝ :=
  max reserve (maxOtherBid bids who)

/-- A bidder clears precisely when their bid strictly exceeds the reserve and
all opposing bids. -/
def reserveVickreyWins (reserve : ℝ) (bids : BidProfile ι) (who : ι) : Prop :=
  bids who > reserveVickreyClearingPrice reserve bids who

/-- The reserve-inclusive threshold is independent of the bidder's own bid. -/
theorem reserveVickreyClearingPrice_update_self (reserve : ℝ) (bids : BidProfile ι)
    (who : ι) (bid : ℝ) :
    reserveVickreyClearingPrice reserve (Profile.update bids who bid) who =
      reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyClearingPrice, maxOtherBid_update_self]

/-- Every other bid is bounded by the maximum faced by `who`. -/
theorem bid_le_maxOtherBid_of_ne (bids : BidProfile ι) {who other : ι}
    (hne : other ≠ who) : bids other ≤ maxOtherBid bids who := by
  unfold maxOtherBid
  dsimp
  have hmem : other ∈ Finset.univ.erase who :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hnonempty : (Finset.univ.erase who).Nonempty := ⟨other, hmem⟩
  rw [dif_pos hnonempty]
  exact Finset.le_sup' bids hmem

/-- Strict clearing makes the winning bidder unique. -/
theorem reserveVickreyWins_unique (reserve : ℝ) (bids : BidProfile ι) {i j : ι}
    (hi : reserveVickreyWins reserve bids i) (hj : reserveVickreyWins reserve bids j) :
    i = j := by
  by_contra hne
  have hji : j ≠ i := fun h => hne h.symm
  have hj_le_other : bids j ≤ maxOtherBid bids i := bid_le_maxOtherBid_of_ne bids hji
  have hi_le_other : bids i ≤ maxOtherBid bids j := bid_le_maxOtherBid_of_ne bids hne
  have hj_le_price : bids j ≤ reserveVickreyClearingPrice reserve bids i :=
    le_trans hj_le_other (le_max_right _ _)
  have hi_le_price : bids i ≤ reserveVickreyClearingPrice reserve bids j :=
    le_trans hi_le_other (le_max_right _ _)
  unfold reserveVickreyWins at hi hj
  linarith

local instance reserveVickreyWins_decidable (reserve : ℝ) (bids : BidProfile ι) :
    DecidablePred (reserveVickreyWins reserve bids) :=
  fun _ => Classical.propDecidable _

/-- The strictly clearing bidder, if there is one.  Ties do not clear. -/
noncomputable def reserveVickreyAllocation (reserve : ℝ) (bids : BidProfile ι) : Option ι := by
  classical
  exact if h : ∃ who, reserveVickreyWins reserve bids who then some h.choose else none

/-- Allocation selects `who` exactly when `who` strictly clears. -/
theorem allocation_eq_some_iff (reserve : ℝ) (bids : BidProfile ι) (who : ι) :
    reserveVickreyAllocation reserve bids = some who ↔ reserveVickreyWins reserve bids who := by
  classical
  constructor
  · intro halloc
    unfold reserveVickreyAllocation at halloc
    by_cases h : ∃ i, reserveVickreyWins reserve bids i
    · rw [dif_pos h] at halloc
      injection halloc with hchoose
      simpa [hchoose] using h.choose_spec
    · rw [dif_neg h] at halloc
      contradiction
  · intro hwin
    unfold reserveVickreyAllocation
    have h : ∃ i, reserveVickreyWins reserve bids i := ⟨who, hwin⟩
    rw [dif_pos h]
    have hchoose : h.choose = who := reserveVickreyWins_unique reserve bids h.choose_spec hwin
    simp [hchoose]

/-- Non-allocation is exactly the absence of a strictly clearing bidder. -/
theorem allocation_eq_none_iff (reserve : ℝ) (bids : BidProfile ι) :
    reserveVickreyAllocation reserve bids = none ↔
      ∀ who, ¬ reserveVickreyWins reserve bids who := by
  classical
  constructor
  · intro hnone who hwin
    have hsome := (allocation_eq_some_iff reserve bids who).2 hwin
    rw [hnone] at hsome
    contradiction
  · intro hnone
    unfold reserveVickreyAllocation
    by_cases h : ∃ who, reserveVickreyWins reserve bids who
    · exact False.elim (hnone h.choose h.choose_spec)
    · simp [h]

/-- The clearing price is the maximum of the reserve and the other-bid maximum. -/
theorem clearingPrice_eq_max_reserve_excluding (reserve : ℝ) (bids : BidProfile ι) (who : ι) :
    reserveVickreyClearingPrice reserve bids who = max reserve (maxOtherBid bids who) := rfl

/-- A selected bidder bid strictly above their clearing price. -/
theorem clearingPrice_lt_bid_of_allocation_eq_some (reserve : ℝ) (bids : BidProfile ι)
    (who : ι) (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyClearingPrice reserve bids who < bids who := by
  simpa [reserveVickreyWins] using (allocation_eq_some_iff reserve bids who).1 halloc

/-- A selected bidder bid at least their clearing price. -/
theorem clearingPrice_le_bid_of_allocation_eq_some (reserve : ℝ) (bids : BidProfile ι)
    (who : ι) (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyClearingPrice reserve bids who ≤ bids who :=
  le_of_lt (clearingPrice_lt_bid_of_allocation_eq_some reserve bids who halloc)

/-- Value from the single-item allocation. -/
def reserveVickreyValue (value : ι → ℝ) (who : ι) : Option ι → ℝ
  | some winner => if winner = who then value who else 0
  | none => 0

/-- Only the allocated bidder pays their reserve-inclusive clearing price. -/
def reserveVickreyPayment (reserve : ℝ) (bids : BidProfile ι) (who : ι) : ℝ :=
  if reserveVickreyAllocation reserve bids = some who then
    reserveVickreyClearingPrice reserve bids who
  else 0

theorem payment_of_allocation_eq_some (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyPayment reserve bids who = reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyPayment, halloc]

theorem payment_of_allocation_ne_some (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (halloc : reserveVickreyAllocation reserve bids ≠ some who) :
    reserveVickreyPayment reserve bids who = 0 := by
  simp [reserveVickreyPayment, halloc]

theorem payment_le_bid_of_allocation_eq_some (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (halloc : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyPayment reserve bids who ≤ bids who := by
  rw [payment_of_allocation_eq_some reserve bids who halloc]
  exact clearingPrice_le_bid_of_allocation_eq_some reserve bids who halloc

/-- Quasilinear payoff of the reserve-price Vickrey allocation and payment. -/
def reserveVickreyUtility (value : ι → ℝ) (reserve : ℝ) (bids : BidProfile ι) (who : ι) : ℝ :=
  reserveVickreyValue value who (reserveVickreyAllocation reserve bids) -
    reserveVickreyPayment reserve bids who

theorem utility_winner (value : ι → ℝ) (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (hwin : reserveVickreyAllocation reserve bids = some who) :
    reserveVickreyUtility value reserve bids who =
      value who - reserveVickreyClearingPrice reserve bids who := by
  simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, hwin]

theorem utility_loser (value : ι → ℝ) (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (hlose : reserveVickreyAllocation reserve bids ≠ some who) :
    reserveVickreyUtility value reserve bids who = 0 := by
  cases halloc : reserveVickreyAllocation reserve bids with
  | none => simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, halloc]
  | some winner =>
    have hne : winner ≠ who := by
      intro h
      apply hlose
      simp [halloc, h]
    simp [reserveVickreyUtility, reserveVickreyPayment, reserveVickreyValue, halloc, hne]

/-- Utility is value less threshold exactly when the bidder strictly clears. -/
theorem reserveVickreyUtility_eq_if_wins (value : ι → ℝ) (reserve : ℝ)
    (bids : BidProfile ι) (who : ι) :
    reserveVickreyUtility value reserve bids who =
      if reserveVickreyWins reserve bids who then
        value who - reserveVickreyClearingPrice reserve bids who
      else 0 := by
  classical
  by_cases hwin : reserveVickreyWins reserve bids who
  · have halloc := (allocation_eq_some_iff reserve bids who).2 hwin
    rw [if_pos hwin, utility_winner value reserve bids who halloc]
  · have halloc : reserveVickreyAllocation reserve bids ≠ some who := fun hsome =>
      hwin ((allocation_eq_some_iff reserve bids who).1 hsome)
    rw [if_neg hwin, utility_loser value reserve bids who halloc]

/-- At zero reserve, when the opponents' maximum is nonnegative, the explicit
allocation-and-payment presentation has exactly the payoff of the generic
strict-winner second-price presentation. -/
theorem utility_zeroReserve_eq_secondPricePayoff (value : ι → ℝ)
    (bids : BidProfile ι) (who : ι) (hother : 0 ≤ maxOtherBid bids who) :
    reserveVickreyUtility value 0 bids who =
      secondPricePayoff value bids who := by
  rw [reserveVickreyUtility_eq_if_wins]
  simp only [reserveVickreyWins, reserveVickreyClearingPrice,
    max_eq_right hother, secondPricePayoff]

/-- A truthful bidder's reserve-price Vickrey payoff is nonnegative. -/
theorem utility_nonneg (value : ι → ℝ) (reserve : ℝ) (bids : BidProfile ι) (who : ι)
    (htruth : bids who = value who) : 0 ≤ reserveVickreyUtility value reserve bids who := by
  by_cases halloc : reserveVickreyAllocation reserve bids = some who
  · rw [utility_winner value reserve bids who halloc, sub_nonneg]
    simpa [htruth] using clearingPrice_le_bid_of_allocation_eq_some reserve bids who halloc
  · rw [utility_loser value reserve bids who halloc]

/-- Truthful bidding weakly dominates every alternative bid against fixed opponents. -/
theorem truthful_weakly_dominant (value : ι → ℝ) (reserve : ℝ)
    (who : ι) (bids : BidProfile ι) (alternative : ℝ) :
    reserveVickreyUtility value reserve (Profile.update bids who (value who)) who ≥
      reserveVickreyUtility value reserve (Profile.update bids who alternative) who := by
  classical
  rw [reserveVickreyUtility_eq_if_wins, reserveVickreyUtility_eq_if_wins]
  simp only [reserveVickreyWins, Profile.update_same, reserveVickreyClearingPrice_update_self]
  set price := reserveVickreyClearingPrice reserve bids who
  by_cases htruth : value who > price
  · simp [htruth]
    by_cases hdeviation : alternative > price
    · simp [hdeviation]
    · simp [hdeviation]
      linarith
  · simp [htruth]
    by_cases hdeviation : alternative > price
    · simp [hdeviation]
      linarith
    · simp [hdeviation]

/-- The deterministic canonical utility game induced by the reserve Vickrey rules. -/
def reserveVickreyGame (value : ι → ℝ) (reserve : ℝ) : UtilityGame ι :=
  auctionGame (reserveVickreyAllocation reserve) (reserveVickreyPayment reserve)
    (reserveVickreyValue value)

/-- Expected utility in the deterministic game is the displayed reserve payoff. -/
@[simp]
theorem reserveVickreyGame_expectedUtility (value : ι → ℝ) (reserve : ℝ)
    (bids : BidProfile ι) (who : ι) :
    expectedUtility (reserveVickreyGame value reserve).utility who
      ((reserveVickreyGame value reserve).form.play bids) =
        reserveVickreyUtility value reserve bids who := by
  simp [reserveVickreyGame, reserveVickreyUtility, auctionGame_expectedUtility]

/-- Truthful bidding is dominant under the canonical expected-utility preference. -/
theorem valuation_is_dominant (value : ι → ℝ) (reserve : ℝ) (who : ι) :
    IsDominant (reserveVickreyGame value reserve).form
      (euPreference (reserveVickreyGame value reserve).utility) who (value who) := by
  intro alternative bids
  simp only [euPreference_apply, reserveVickreyGame_expectedUtility]
  exact truthful_weakly_dominant value reserve who bids alternative

/-- The reserve-price Vickrey mechanism is dominant-strategy incentive compatible. -/
theorem mechanism_isDSIC (value : ι → ℝ) (reserve : ℝ) :
    ∀ who, IsDominant (reserveVickreyGame value reserve).form
      (euPreference (reserveVickreyGame value reserve).utility) who (value who) :=
  valuation_is_dominant value reserve

/-- Truthful bidding is Nash because every truthful bid is dominant. -/
theorem reserveVickrey_truthful_isNash (value : ι → ℝ) (reserve : ℝ) :
    IsNash (reserveVickreyGame value reserve).form
      (euPreference (reserveVickreyGame value reserve).utility) value :=
  IsDominantProfile.isNash (mechanism_isDSIC value reserve)

end ReserveVickrey

end GameTheory.Mechanism.Auction
