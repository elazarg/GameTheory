import GameTheory.SolutionConcepts

/-!
# All-Pay Auction

In an all-pay auction, every bidder pays their bid regardless of whether
they win. This models contests, lobbying, and rent-seeking.

## Main results

* `allPay_overbid_unprofitable` — bidding above the prize value is dominated
    by bidding zero
* `allPay_winner_profit` — the winner's profit is value minus bid
-/

namespace GameTheory

/-- In an all-pay auction, bidding more than the prize value `v` is strictly
    worse than bidding 0, regardless of the outcome. The bidder either:
    - Loses: pays `b > v` and gets nothing → payoff = `-b < 0`
    - Wins: pays `b > v` and gets `v` → payoff = `v - b < 0`
    In both cases, bidding 0 gives payoff ≥ 0. -/
theorem allPay_overbid_unprofitable (v b : ℝ) (hv : v ≥ 0) (hb : b > v) :
    (0 : ℝ) > v - b ∧ (0 : ℝ) > -b := by
  constructor <;> linarith

/-- In an all-pay auction, the winner's profit is `v - bid`, which is
    positive iff the bid is below the prize value.
    This is the core tension: bidding high wins but costs; bidding low
    preserves value but may lose. -/
theorem allPay_winner_profit (v bid : ℝ) (_hwin : bid > 0) (hbid : bid < v) :
    v - bid > 0 := by linarith

/-- In an all-pay contest with two players, if player 1 bids `b₁` and
    player 2 bids `b₂ < b₁`, player 1 wins and gets `v - b₁` while
    player 2 gets `-b₂`. The total surplus is `v - b₁ - b₂ < v`,
    showing that all-pay auctions dissipate rent. -/
theorem allPay_rent_dissipation (v b₁ b₂ : ℝ) (hb₁ : b₁ > 0) (hb₂ : b₂ > 0) :
    (v - b₁) + (-b₂) < v := by linarith

/-- In a symmetric all-pay auction, if both players bid `b > 0`, the expected
    payoff for each (assuming fair tie-breaking) is `v/2 - b`. This is
    negative when `b > v/2`, so no symmetric pure equilibrium exists with
    positive bids above `v/2`. -/
theorem allPay_symmetric_negative (v b : ℝ) (hb : b > v / 2) :
    v / 2 - b < 0 := by linarith

end GameTheory
