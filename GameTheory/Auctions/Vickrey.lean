import Math.Probability
import GameTheory.Concepts.SolutionConcepts
import Math.FinsetUpdate

/-!
# Vickrey (Second-Price) Auction

In a second-price sealed-bid auction, the highest bidder wins and pays
the second-highest bid. Vickrey (1961) proved that truthful bidding
(bidding one's true valuation) is a weakly dominant strategy.

## Main definitions

* `maxOtherBid` — maximum bid among opponents
* `vickreyPayoff` — payoff function for a second-price auction

## Main results

* `vickrey_truthful_dominant` — truthful bidding is weakly dominant
-/

namespace GameTheory

open Math.Probability

variable {n : ℕ}

open Classical in
/-- The maximum bid among all players other than `who`.
    Returns 0 if `who` is the only player. -/
noncomputable def maxOtherBid (bids : Fin n → ℝ) (who : Fin n) : ℝ :=
  let others := Finset.univ.filter (· ≠ who)
  if h : others.Nonempty then others.sup' h bids else 0

open Classical in
/-- The max-other-bid is independent of `who`'s own bid. -/
theorem maxOtherBid_update_self (bids : Fin n → ℝ) (who : Fin n) (b : ℝ) :
    maxOtherBid (Function.update bids who b) who = maxOtherBid bids who := by
  simp only [maxOtherBid]
  split <;> simp_all only [ne_eq]
  rename_i h
  exact Math.Finset.Update.sup'_update_eq_of_not_mem
    (S := Finset.univ.filter (· ≠ who)) h who (by simp) bids b

open Classical in
/-- Payoff in a second-price auction with valuations `v`.
    If your bid exceeds the max other bid, you get `v(who) - maxOtherBid`;
    otherwise you get 0. -/
noncomputable def vickreyPayoff (v : Fin n → ℝ) (bids : Fin n → ℝ) (who : Fin n) : ℝ :=
  if bids who > maxOtherBid bids who then v who - maxOtherBid bids who else 0

open Classical in
/-- Truthful bidding is weakly dominant in a Vickrey auction. -/
theorem vickrey_truthful_dominant (v : Fin n → ℝ)
    (who : Fin n) (bids : Fin n → ℝ) (b' : ℝ) :
    vickreyPayoff v (Function.update bids who (v who)) who ≥
    vickreyPayoff v (Function.update bids who b') who := by
  simp only [vickreyPayoff, Function.update_self,
    maxOtherBid_update_self]
  set m := maxOtherBid bids who
  by_cases hwin_t : v who > m
  · simp only [hwin_t, ↓reduceIte]
    by_cases hwin_d : b' > m
    · simp [hwin_d]
    · simp [hwin_d]; linarith
  · simp only [hwin_t, ↓reduceIte]
    by_cases hwin_d : b' > m
    · simp [hwin_d]; linarith
    · simp [hwin_d]

open Classical in
/-- The Vickrey auction as a `KernelGame`: strategies are bids (ℝ),
    utility is the Vickrey payoff. -/
noncomputable def vickreyGame (v : Fin n → ℝ) : KernelGame (Fin n) :=
  KernelGame.ofEU (fun _ => ℝ) (vickreyPayoff v)

open Classical in
/-- Truthful bidding is a dominant strategy in the Vickrey game. -/
theorem vickrey_truthful_isDominant (v : Fin n → ℝ) (who : Fin n) :
    (vickreyGame v).IsDominant who (v who) := by
  intro σ s'
  simp only [vickreyGame, KernelGame.eu_ofEU]
  convert vickrey_truthful_dominant v who σ s'

open Classical in
/-- Truthful bidding is a Nash equilibrium of the Vickrey game. -/
theorem vickrey_truthful_isNash (v : Fin n → ℝ) :
    (vickreyGame v).IsNash v := by
  exact KernelGame.dominant_is_nash _ _ (fun i => vickrey_truthful_isDominant v i)

end GameTheory
