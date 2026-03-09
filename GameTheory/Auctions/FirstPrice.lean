import Math.Probability
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.OfEUProperties

/-!
# First-Price Auction

First-price sealed-bid auction primitives and a no-dominant-strategy result.

This file formalizes a deterministic first-price auction:
- winner is the bidder with maximal bid,
- winner pays own bid,
- losers get zero utility.

Main result:
- `firstPrice_no_dominant_strategy` — no bid is dominant (for any player).
-/

namespace GameTheory

open Math.Probability

variable {n : ℕ}
variable [Nonempty (Fin n)]

open Classical in
/-- Highest bid in a profile. -/
noncomputable def maxBid (bids : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty bids

open Classical in
/-- Some bidder attains the highest bid. -/
lemma exists_maxBid (bids : Fin n → ℝ) : ∃ i : Fin n, bids i = maxBid bids := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty bids
  exact ⟨i, by simpa [maxBid] using hi.symm⟩

open Classical in
/-- Winner: an arbitrary bidder attaining the highest bid. -/
noncomputable def winner (bids : Fin n → ℝ) : Fin n :=
  Classical.choose (exists_maxBid bids)

open Classical in
/-- Winner's bid equals the maximum bid. -/
lemma bid_winner_eq_maxBid (bids : Fin n → ℝ) :
    bids (winner bids) = maxBid bids :=
  Classical.choose_spec (exists_maxBid bids)

open Classical in
/-- Every bid is bounded above by the winner's bid. -/
lemma bid_le_bid_winner (bids : Fin n → ℝ) (j : Fin n) :
    bids j ≤ bids (winner bids) := by
  rw [bid_winner_eq_maxBid bids]
  simpa [maxBid] using (Finset.le_sup' bids (Finset.mem_univ j))

open Classical in
/-- If bidder `i` strictly outbids everyone else, then `i` is the winner. -/
lemma eq_winner_of_bid_gt (bids : Fin n → ℝ) (i : Fin n)
    (h : ∀ j, j ≠ i → bids j < bids i) :
    i = winner bids := by
  contrapose! h
  exact ⟨winner bids, h.symm, bid_le_bid_winner bids i⟩

open Classical in
/-- First-price utility: winner gets value minus own bid, losers get zero. -/
noncomputable def firstPricePayoff (v : Fin n → ℝ) (bids : Fin n → ℝ) (who : Fin n) : ℝ :=
  if who = winner bids then v who - bids who else 0

open Classical in
lemma firstPricePayoff_winner (v : Fin n → ℝ) (bids : Fin n → ℝ) (who : Fin n)
    (h : who = winner bids) :
    firstPricePayoff v bids who = v who - bids who := by
  simp [firstPricePayoff, h]

open Classical in
lemma firstPricePayoff_loser (v : Fin n → ℝ) (bids : Fin n → ℝ) (who : Fin n)
    (h : who ≠ winner bids) :
    firstPricePayoff v bids who = 0 := by
  simp [firstPricePayoff, h]

open Classical in
/-- First-price auction as a deterministic kernel game on bid profiles. -/
noncomputable def firstPriceGame (v : Fin n → ℝ) : KernelGame (Fin n) :=
  KernelGame.ofEU (fun _ => ℝ) (firstPricePayoff v)

/-- No single bid is dominant in first-price auction (finite, nontrivial bidder set). -/
theorem firstPrice_no_dominant_strategy_ofEU
    [Nontrivial (Fin n)]
    (v : Fin n → ℝ) (who : Fin n) (b : ℝ) :
    ¬ (KernelGame.ofEU (fun _ : Fin n => ℝ) (firstPricePayoff v)).IsDominant who b := by
  intro hdom
  have hdom' := (ofEU_isDominant_iff (fun _ : Fin n => ℝ) (firstPricePayoff v) who b).1 hdom
  let σ : Fin n → ℝ := fun _ => b - 2
  have h := hdom' σ (b - 1)
  -- Identify winners in both compared profiles.
  have hWb : who = winner (Function.update σ who b) := by
    apply eq_winner_of_bid_gt (bids := Function.update σ who b) who
    intro j hj
    simp [σ, Function.update, hj]
  have hWb1 : who = winner (Function.update σ who (b - 1)) := by
    apply eq_winner_of_bid_gt (bids := Function.update σ who (b - 1)) who
    intro j hj
    simp [σ, Function.update, hj]
  -- Rewrite payoffs in the two compared profiles.
  have hL :
      firstPricePayoff v (Function.update σ who b) who = v who - b := by
    simpa [Function.update] using firstPricePayoff_winner v (Function.update σ who b) who hWb
  have hR :
      firstPricePayoff v (Function.update σ who (b - 1)) who = v who - (b - 1) := by
    simpa [Function.update] using
      firstPricePayoff_winner v (Function.update σ who (b - 1)) who hWb1
  rw [ge_iff_le] at h
  have hnum : v who - (b - 1) ≤ v who - b := by
    calc
      v who - (b - 1) = firstPricePayoff v (Function.update σ who (b - 1)) who := by
        symm
        exact hR
      _ ≤ firstPricePayoff v (Function.update σ who b) who := h
      _ = v who - b := hL
  linarith [hnum]

/-- No single bid is dominant in first-price auction (finite, nontrivial bidder set). -/
theorem firstPrice_no_dominant_strategy
    [Nontrivial (Fin n)]
    (v : Fin n → ℝ) (who : Fin n) (b : ℝ) :
    ¬ (firstPriceGame v).IsDominant who b := by
  simpa [firstPriceGame] using firstPrice_no_dominant_strategy_ofEU v who b

end GameTheory
