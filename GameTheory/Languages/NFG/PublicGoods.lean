import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# Public Goods Game

The public goods game models voluntary contribution to a shared resource.
When the marginal per-capita return (MPCR) is less than 1, not contributing
is a dominant strategy — the classic free-rider problem. But when MPCR > 0,
universal contribution yields higher payoff than universal defection.

## Main results

* `publicGoods_freeRide_dominant` — zero contribution dominates any positive amount
* `publicGoods_cooperation_pareto` — full cooperation beats full defection
-/

namespace GameTheory

open Math.Probability

/-- In a public goods game, zero contribution dominates when mpcr < 1. -/
theorem publicGoods_freeRide_dominant {n : ℕ}
    (endowment mpcr : ℝ) (hmpcr : mpcr < 1)
    (contribs : Fin n → ℝ) (who : Fin n) (hc : contribs who ≥ 0) :
    let payoff (c : Fin n → ℝ) (i : Fin n) := endowment + mpcr * ∑ j, c j - c i
    payoff (Function.update contribs who 0) who ≥ payoff contribs who := by
  intro payoff
  simp only [payoff, Function.update_self]
  suffices h : endowment + mpcr * ∑ j, Function.update contribs who 0 j - 0 -
      (endowment + mpcr * ∑ j, contribs j - contribs who) ≥ 0 by linarith
  have hsum : ∑ j, Function.update contribs who 0 j =
      ∑ j, contribs j - contribs who := by
    have h1 := Finset.sum_update_of_mem (Finset.mem_univ who) (f := contribs) (b := (0 : ℝ))
    have h2 := Finset.add_sum_erase Finset.univ contribs (Finset.mem_univ who)
    rw [Finset.sdiff_singleton_eq_erase] at h1
    linarith
  rw [hsum]
  nlinarith

/-- Full cooperation gives strictly higher payoff than full defection
    when `mpcr * n > 1` and `c > 0`. -/
theorem publicGoods_cooperation_pareto {n : ℕ}
    (endowment mpcr c : ℝ) (hc : c > 0) (hmn : mpcr * n > 1) (who : Fin n) :
    let payoff (contrib : Fin n → ℝ) (i : Fin n) := endowment + mpcr * ∑ j, contrib j - contrib i
    payoff (fun _ => c) who > payoff (fun _ => 0) who := by
  intro payoff
  simp only [payoff, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  linarith [mul_pos (by linarith : mpcr * ↑n - 1 > 0) hc]

end GameTheory
