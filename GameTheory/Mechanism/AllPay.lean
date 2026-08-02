/-
# All-pay auction arithmetic

Every bidder in an all-pay auction pays their bid.  These are the elementary
real-arithmetic facts used by an eventual allocation model; they make no
dominance or equilibrium claim by themselves.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace GameTheory.Mechanism.Auction

/-- Overbidding a nonnegative prize makes both displayed all-pay payoffs
strictly negative. -/
theorem allPay_overbid_unprofitable (v b : ℝ) (hv : v ≥ 0) (hb : b > v) :
    (0 : ℝ) > v - b ∧ (0 : ℝ) > -b := by
  constructor <;> linarith

/-- A winning bid below the prize has strictly positive displayed payoff. -/
theorem allPay_winner_profit_of_lt (v bid : ℝ) (hbid : bid < v) :
    v - bid > 0 := by
  linarith

/-- Strictly positive bids dissipate part of the displayed prize value. -/
theorem allPay_rent_dissipation (v b₁ b₂ : ℝ) (hb₁ : b₁ > 0) (hb₂ : b₂ > 0) :
    (v - b₁) + (-b₂) < v := by
  linarith

/-- A symmetric fair-tie bid above half the prize has negative payoff. -/
theorem allPay_symmetric_negative (v b : ℝ) (hb : b > v / 2) :
    v / 2 - b < 0 := by
  linarith

end GameTheory.Mechanism.Auction
