/-
# Finite-bidder sealed-bid auctions

This module is an opt-in coordinated domain layer over the canonical game-form
and response concepts.  Its generic constructor records allocation and payment
data explicitly.  The concrete second-price specialization is instead a
payoff-only strict-winner presentation, so ties give every bidder zero and it
makes no allocation or revenue claim.  The concrete first-price specialization
faithfully uses an arbitrary maximal-bid tie breaker.
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory.Mechanism.Auction

open Probability

/-- The common real-bid signature for a finite-bidder sealed-bid auction. -/
@[reducible]
def bidSignature (ι : Type) : GameSignature.{0, 0, 0} ι where
  Strategy := fun _ : ι => ℝ
  Outcome := ∀ _ : ι, ℝ

/-- A bid profile, bound to the auction signature so unilateral changes always
use `Profile.update`. -/
abbrev BidProfile (ι : Type) := Profile (bidSignature ι)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The largest bid made by a player other than `who`, or zero when there are
no other bidders. -/
def maxOtherBid (bids : BidProfile ι) (who : ι) : ℝ :=
  let others := Finset.univ.erase who
  if h : others.Nonempty then others.sup' h bids else 0

/-- A bidder's own replacement cannot change the maximum of the other bids. -/
theorem maxOtherBid_update_self (bids : BidProfile ι) (who : ι) (bid : ℝ) :
    maxOtherBid (Profile.update bids who bid) who = maxOtherBid bids who := by
  simp only [maxOtherBid]
  split <;> rename_i h
  · refine Finset.sup'_congr h rfl ?_
    intro bidder hbidder
    exact Profile.update_of_ne _ _ (Finset.mem_erase.mp hbidder).1
  · rfl

/-- A quasi-linear decomposition of a canonical utility game.  Finiteness is
required only by aggregate predicates, never by the decomposition itself. -/
structure QuasiLinear (G : UtilityGame ι) where
  /-- Allocation carrier. -/
  Alloc : Type*
  /-- Allocation selected by an outcome. -/
  allocation : G.form.sig.Outcome → Alloc
  /-- Monetary transfer charged to each bidder. -/
  payment : G.form.sig.Outcome → ι → ℝ
  /-- Valuation of allocations. -/
  valuation : ι → Alloc → ℝ
  /-- Utility is valuation less payment. -/
  utility_eq : ∀ outcome bidder,
    G.utility outcome bidder = valuation bidder (allocation outcome) - payment outcome bidder

namespace QuasiLinear

variable {G : UtilityGame ι} (ql : QuasiLinear G)

/-- Every realized allocation gives each bidder nonnegative utility. -/
def IsExPostIR : Prop :=
  ∀ outcome bidder, ql.payment outcome bidder ≤ ql.valuation bidder (ql.allocation outcome)

/-- Transfers are never paid to bidders. -/
def NoPositiveTransfers : Prop :=
  ∀ outcome bidder, 0 ≤ ql.payment outcome bidder

/-- The selected allocation maximizes total reported valuation. -/
def IsEfficient : Prop :=
  ∀ outcome alternative,
    (∑ bidder, ql.valuation bidder (ql.allocation outcome)) ≥
      ∑ bidder, ql.valuation bidder alternative

/-- The total transfer collected at every outcome is zero. -/
def IsStronglyBudgetBalanced : Prop :=
  ∀ outcome, ∑ bidder, ql.payment outcome bidder = 0

end QuasiLinear

/-- Construct the deterministic utility game induced by an allocation rule,
payments, and valuations.  This is the generic quasilinear construction; an
auction-specific payoff model need not pretend to expose all of this data. -/
def auctionGame {Bid : ι → Type} {Alloc : Type}
    (allocation : (∀ bidder, Bid bidder) → Alloc)
    (payment : (∀ bidder, Bid bidder) → ι → ℝ)
    (valuation : ι → Alloc → ℝ) : UtilityGame ι where
  form :=
    { sig := { Strategy := Bid, Outcome := ∀ bidder, Bid bidder }
      play := fun bids => FinDist.pure bids }
  utility := fun bids bidder => valuation bidder (allocation bids) - payment bids bidder

omit [Fintype ι] [DecidableEq ι] in
/-- Expected utility in a deterministic quasilinear auction is its displayed
valuation-minus-payment expression. -/
@[simp]
theorem auctionGame_expectedUtility {Bid : ι → Type} {Alloc : Type}
    (allocation : (∀ bidder, Bid bidder) → Alloc)
    (payment : (∀ bidder, Bid bidder) → ι → ℝ)
    (valuation : ι → Alloc → ℝ) (bids : ∀ bidder, Bid bidder) (bidder : ι) :
    expectedUtility (auctionGame allocation payment valuation).utility bidder
      ((auctionGame allocation payment valuation).form.play bids) =
        valuation bidder (allocation bids) - payment bids bidder :=
  expectedUtility_pure ..

/-- The canonical quasilinear witness on `auctionGame`. -/
def auctionGame_quasiLinear {Bid : ι → Type} {Alloc : Type}
    (allocation : (∀ bidder, Bid bidder) → Alloc)
    (payment : (∀ bidder, Bid bidder) → ι → ℝ)
    (valuation : ι → Alloc → ℝ) :
    QuasiLinear (auctionGame allocation payment valuation) where
  Alloc := Alloc
  allocation := allocation
  payment := payment
  valuation := valuation
  utility_eq := fun _ _ => rfl

omit [Fintype ι] in
/-- A pointwise incentive-compatibility inequality implies that the designated
bid profile is Nash.  The proof packages the inequality as the canonical
dominant-profile predicate; it does not introduce an auction-specific solution
concept. -/
theorem auctionGame_ic_isNash {Bid : ι → Type} {Alloc : Type}
    (allocation : (∀ bidder, Bid bidder) → Alloc)
    (payment : (∀ bidder, Bid bidder) → ι → ℝ)
    (valuation : ι → Alloc → ℝ) (bids : ∀ bidder, Bid bidder)
    (hIC : ∀ (bidder : ι)
      (profile : Profile (auctionGame allocation payment valuation).form.sig)
      (alternative : (auctionGame allocation payment valuation).form.sig.Strategy bidder),
      valuation bidder (allocation (Profile.update profile bidder (bids bidder))) -
          payment (Profile.update profile bidder (bids bidder)) bidder ≥
        valuation bidder (allocation (Profile.update profile bidder alternative)) -
          payment (Profile.update profile bidder alternative) bidder) :
    IsNash (auctionGame allocation payment valuation).form
      (euPreference (auctionGame allocation payment valuation).utility) bids := by
  apply IsDominantProfile.isNash
  intro bidder alternative profile
  simpa only [euPreference_apply, auctionGame_expectedUtility] using
    hIC bidder profile alternative

/-- The payoff of the strict-winner second-price presentation.  The price is
independent of the bidder's own bid. -/
def secondPricePayoff (value : ι → ℝ) (bids : BidProfile ι) (who : ι) : ℝ :=
  if bids who > maxOtherBid bids who then value who - maxOtherBid bids who else 0

/-- The deterministic utility game underlying `secondPricePayoff`. -/
def secondPriceGame (value : ι → ℝ) : UtilityGame ι where
  form :=
    { sig := bidSignature ι
      play := fun bids => FinDist.pure bids }
  utility := secondPricePayoff value

/-- Truthful bidding gives at least the payoff of any alternative bid against
the same opponents' bids.  This is the pointwise inequality underlying the
canonical dominance theorem. -/
theorem secondPrice_truthful_payoff_ge (value : ι → ℝ) (who : ι)
    (bids : BidProfile ι) (alternative : ℝ) :
    secondPricePayoff value (Profile.update bids who alternative) who ≤
      secondPricePayoff value (Profile.update bids who (value who)) who := by
  simp only [secondPricePayoff, Profile.update_same, maxOtherBid_update_self]
  split_ifs <;> linarith

/-- In the payoff-only strict-winner second-price presentation, truthful
bidding weakly dominates every alternative bid. -/
theorem secondPrice_truthful_isDominant (value : ι → ℝ) (who : ι) :
    IsDominant (secondPriceGame value).form (euPreference (secondPriceGame value).utility)
      who (value who) := by
  intro alternative bids
  simp only [euPreference_apply, secondPriceGame, expectedUtility_pure,
    secondPricePayoff]
  exact secondPrice_truthful_payoff_ge value who bids alternative

/-- Truthful bidding is a Nash profile because every truthful bid is dominant. -/
theorem secondPrice_truthful_isNash (value : ι → ℝ) :
    IsNash (secondPriceGame value).form (euPreference (secondPriceGame value).utility) value :=
  IsDominantProfile.isNash (fun bidder => secondPrice_truthful_isDominant value bidder)

section FirstPrice

variable [Nonempty ι]

/-- Highest bid in a nonempty finite bid profile. -/
def maxBid (bids : BidProfile ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty bids

omit [DecidableEq ι] in
/-- Some bidder attains the highest bid. -/
theorem exists_maxBid (bids : BidProfile ι) : ∃ bidder, bids bidder = maxBid bids := by
  obtain ⟨bidder, _, hbidder⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty bids
  exact ⟨bidder, by simpa [maxBid] using hbidder.symm⟩

/-- An arbitrary bidder attaining the highest bid.  This is explicit
tie-breaking data only through the choice function; the payoff theorem below
does not claim any particular allocation rule for ties. -/
noncomputable def winner (bids : BidProfile ι) : ι :=
  Classical.choose (exists_maxBid bids)

omit [DecidableEq ι] in
/-- The chosen winner's bid is maximal. -/
theorem bid_winner_eq_maxBid (bids : BidProfile ι) : bids (winner bids) = maxBid bids :=
  Classical.choose_spec (exists_maxBid bids)

omit [DecidableEq ι] in
/-- Every bid is no greater than the chosen winner's bid. -/
theorem bid_le_bid_winner (bids : BidProfile ι) (bidder : ι) :
    bids bidder ≤ bids (winner bids) := by
  rw [bid_winner_eq_maxBid bids]
  simpa [maxBid] using Finset.le_sup' bids (Finset.mem_univ bidder)

omit [DecidableEq ι] in
/-- A strictly highest bidder is the chosen winner. -/
theorem eq_winner_of_bid_gt (bids : BidProfile ι) (bidder : ι)
    (hhighest : ∀ other, other ≠ bidder → bids other < bids bidder) :
    bidder = winner bids := by
  contrapose! hhighest
  exact ⟨winner bids, hhighest.symm, not_lt.mpr (bid_le_bid_winner bids bidder)⟩

/-- First-price payoff with an arbitrary highest-bid tie breaker: the winner
pays their own bid and every other bidder receives zero. -/
def firstPricePayoff (value : ι → ℝ) (bids : BidProfile ι) (who : ι) : ℝ :=
  if who = winner bids then value who - bids who else 0

theorem firstPricePayoff_winner (value : ι → ℝ) (bids : BidProfile ι) (who : ι)
    (hwin : who = winner bids) :
    firstPricePayoff value bids who = value who - bids who := by
  simp [firstPricePayoff, hwin]

theorem firstPricePayoff_loser (value : ι → ℝ) (bids : BidProfile ι) (who : ι)
    (hlose : who ≠ winner bids) : firstPricePayoff value bids who = 0 := by
  simp [firstPricePayoff, hlose]

/-- The deterministic utility game underlying `firstPricePayoff`. -/
def firstPriceGame (value : ι → ℝ) : UtilityGame ι where
  form :=
    { sig := bidSignature ι
      play := fun bids => FinDist.pure bids }
  utility := firstPricePayoff value

/-- No bid is weakly dominant in the first-price game: against a profile in
which every opponent bids two less, bidding one less still wins and strictly
improves the winner's payoff. -/
theorem firstPrice_not_isDominant (value : ι → ℝ) (who : ι) (bid : ℝ) :
    ¬ IsDominant (firstPriceGame value).form (euPreference (firstPriceGame value).utility)
      who bid := by
  intro hdominant
  let bids : BidProfile ι := fun _ => bid - 2
  have h := hdominant (bid - 1) bids
  simp only [euPreference_apply, firstPriceGame, expectedUtility_pure] at h
  have hwinBid : who = winner (Profile.update bids who bid) := by
    apply eq_winner_of_bid_gt
    intro other hother
    rw [Profile.update_of_ne _ _ hother, Profile.update_same]
    simp [bids]
  have hwinLower : who = winner (Profile.update bids who (bid - 1)) := by
    apply eq_winner_of_bid_gt
    intro other hother
    rw [Profile.update_of_ne _ _ hother, Profile.update_same]
    simp [bids]
  rw [firstPricePayoff_winner value _ _ hwinLower,
    firstPricePayoff_winner value _ _ hwinBid] at h
  simp only [Profile.update_same] at h
  linarith

end FirstPrice

end GameTheory.Mechanism.Auction
