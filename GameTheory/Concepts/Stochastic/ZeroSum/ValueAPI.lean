/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.ZeroSum.Basic

/-!
# Basic Value API for Discounted Two-Player Zero-Sum Stochastic Games

`GameTheory.Concepts.Stochastic.ZeroSum.Basic` builds the normalized discounted
Shapley value `StochasticGame.discountedShapleyValue` and shows that the
selected stationary row/column actions form an exact discounted Nash
equilibrium.  This file supplies the remaining basic API around that value:
it does not exist in a vacuum, so no *other* discounted Nash equilibrium can
have a different payoff; it is exactly a fixed point of the Shapley operator;
it inherits a bound from any bound on the stage payoff; and it is `1`-
Lipschitz in the row stage payoff, holding the transition kernel fixed.

The general Lipschitz estimate is proved once, for the abstract
`Math.ShapleyOperator.discountedValue`, by the same fixed-point comparison
technique already used there for varying the discount's continuation value
(`Math.ShapleyOperator.lipschitzWith_shapleyOperator`) — here it is instead
the *reward* that varies, using Mathlib's
`ContractingWith.fixedPoint_lipschitz_in_map`.

## Main results

* `Math.ShapleyOperator.dist_discountedValue_le` — the discounted value is
  `1`-Lipschitz in the payoff matrix, holding the kernel fixed
* `StochasticGame.discountedShapleyValue_isFixedPt` — the Shapley equation
  `v β = ShapleyOp β (v β)` in game-semantic form
* `StochasticGame.abs_discountedShapleyValue_le` — a stage payoff bound
  bounds the normalized discounted Shapley value by the same constant
* `StochasticGame.dist_discountedShapleyValue_le` — `1`-Lipschitz dependence
  of the value on the row stage payoff
* `StochasticGame.discountedPayoff_eq_discountedShapleyValue_of_isDiscountedNash`
  — **uniqueness of the value**: every exact discounted Nash equilibrium has
  row payoff equal to the normalized discounted Shapley value
-/

noncomputable section

open scoped NNReal

namespace Math
namespace ShapleyOperator

open Math.Probability MinimaxLoomis

/-- **`1`-Lipschitz dependence on the reward.**  Holding the transition
kernel `q` fixed, the discounted value is `1`-Lipschitz in the payoff matrix
`u` under the sup metric: entries uniformly within `C` of each other give
discounted values within `C / (1 - β)` of each other.  Dual to
`lipschitzWith_shapleyOperator`, which is Lipschitz in the continuation
value holding the payoff fixed. -/
theorem dist_discountedValue_le {S I J : Type*}
    [Fintype S] [Nonempty S] [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (u u' : S → I → J → ℝ) (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1)
    {C : ℝ} (hC : ∀ s i j, |u s i j - u' s i j| ≤ C) :
    dist (discountedValue u q hβ) (discountedValue u' q hβ) ≤ C / (1 - (β : ℝ)) := by
  have hC0 : 0 ≤ C :=
    (abs_nonneg _).trans
      (hC (Classical.arbitrary S) (Classical.arbitrary I) (Classical.arbitrary J))
  have hfg : ∀ v : S → ℝ, dist (shapleyOperator u q (β : ℝ) v)
      (shapleyOperator u' q (β : ℝ) v) ≤ C := by
    intro v
    rw [dist_pi_le_iff hC0]
    intro s
    rw [Real.dist_eq]
    apply abs_lam0_sub_le_of_entrywise_abs_le
    intro i j
    have heq : (u s i j + (β : ℝ) * expect (q s i j) v) -
        (u' s i j + (β : ℝ) * expect (q s i j) v) = u s i j - u' s i j := by
      ring
    rw [heq]
    exact hC s i j
  unfold discountedValue
  exact (contractingWith_shapleyOperator u q hβ).fixedPoint_lipschitz_in_map
    (contractingWith_shapleyOperator u' q hβ) hfg

end ShapleyOperator
end Math

namespace GameTheory
namespace StochasticGame

/-- **The Shapley equation, game-semantic form.**  The normalized discounted
Shapley value is a fixed point of the discounted Shapley operator built from
the normalized row payoff and the row/column transition kernel: `v β =
ShapleyOp β (v β)`. -/
theorem discountedShapleyValue_isFixedPt
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) :
    Math.ShapleyOperator.shapleyOperator (G.normalizedRowStagePayoff (β : ℝ))
        G.pairTransition (β : ℝ) (G.discountedShapleyValue hβ) =
      G.discountedShapleyValue hβ := by
  unfold discountedShapleyValue
  exact Math.ShapleyOperator.shapleyOperator_discountedValue
    (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ

/-- A uniform bound on row stage payoffs bounds the normalized discounted
Shapley value by the same constant.  No extra `1 / (1 - β)` factor appears,
since the value is already the fixed point of the *normalized* Shapley
operator `(1 - β) * stagePayoff + β * continuation`. -/
theorem abs_discountedShapleyValue_le
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1) {U : ℝ}
    (hpay : ∀ s a, |G.stagePayoff s a 0| ≤ U) (s : G.State) :
    |G.discountedShapleyValue hβ s| ≤ U := by
  have hβ1 : (β : ℝ) < 1 := by exact_mod_cast hβ
  have h1β : (1 : ℝ) - (β : ℝ) ≠ 0 := by linarith
  have hbd := Math.ShapleyOperator.abs_discountedValue_le
    (G.normalizedRowStagePayoff (β : ℝ)) G.pairTransition hβ
    (U := (1 - (β : ℝ)) * U) (by
      intro s' i j
      unfold normalizedRowStagePayoff rowStagePayoff
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (β : ℝ))]
      exact mul_le_mul_of_nonneg_left (hpay s' (G.pairJointAct i j)) (by linarith)) s
  unfold discountedShapleyValue
  rwa [mul_div_cancel_left₀ _ h1β] at hbd

/-- **`1`-Lipschitz dependence on the reward.**  Replacing `G`'s row stage
payoff by any other statewise matrix payoff that is uniformly within `C`
moves the normalized discounted Shapley value by at most `C` in sup
distance, holding the transition kernel fixed. -/
theorem dist_discountedShapleyValue_le
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [Nonempty G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {β : ℝ≥0} (hβ : β < 1)
    (payoff' : G.State → G.Act 0 → G.Act 1 → ℝ) {C : ℝ}
    (hC : ∀ s i j, |G.rowStagePayoff s i j - payoff' s i j| ≤ C) :
    dist (G.discountedShapleyValue hβ)
        (Math.ShapleyOperator.discountedValue
          (fun s i j => (1 - (β : ℝ)) * payoff' s i j) G.pairTransition hβ) ≤ C := by
  have hβ1 : (β : ℝ) < 1 := by exact_mod_cast hβ
  have h1β : (1 : ℝ) - (β : ℝ) ≠ 0 := by linarith
  have hbd := Math.ShapleyOperator.dist_discountedValue_le
    (G.normalizedRowStagePayoff (β : ℝ))
    (fun s i j => (1 - (β : ℝ)) * payoff' s i j)
    G.pairTransition hβ (C := (1 - (β : ℝ)) * C) (by
      intro s i j
      unfold normalizedRowStagePayoff
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (β : ℝ))]
      exact mul_le_mul_of_nonneg_left (hC s i j) (by linarith))
  unfold discountedShapleyValue
  rwa [mul_div_cancel_left₀ _ h1β] at hbd

/-- **Uniqueness of the discounted value.**  Every exact discounted Nash
equilibrium of a two-player zero-sum stochastic game has row payoff equal to
the normalized discounted Shapley value: the value does not depend on which
equilibrium is chosen, only on the game. -/
theorem discountedPayoff_eq_discountedShapleyValue_of_isDiscountedNash
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (hzs : G.IsZeroSum)
    {β : ℝ≥0} (hβ : β < 1) {σ : G.BehaviorProfile} (s₀ : G.State)
    (hN : G.IsDiscountedεNash (β : ℝ) s₀ 0 σ) :
    G.discountedPayoff (β : ℝ) σ s₀ 0 = G.discountedShapleyValue hβ s₀ := by
  have hupd0 : Function.update σ 0 (G.rowShapleyBehaviorStrategy hβ) =
      G.pairBehaviorProfile (G.rowShapleyBehaviorStrategy hβ) (σ 1) := by
    funext i; fin_cases i <;> simp
  have hupd1 : Function.update σ 1 (G.colShapleyBehaviorStrategy hβ) =
      G.pairBehaviorProfile (σ 0) (G.colShapleyBehaviorStrategy hβ) := by
    funext i; fin_cases i <;> simp
  have h0 := hN 0 (G.rowShapleyBehaviorStrategy hβ)
  have h1 := hN 1 (G.colShapleyBehaviorStrategy hβ)
  rw [add_zero, hupd0] at h0
  rw [add_zero, hupd1] at h1
  have hlow0 := G.discountedShapleyValue_le_row_discountedPayoff hβ (σ 1) s₀
  have hlow1 := G.neg_discountedShapleyValue_le_col_discountedPayoff hzs hβ (σ 0) s₀
  have hzero := hzs.discountedPayoff_one_eq_neg_zero (β : ℝ) σ s₀
  linarith

end StochasticGame
end GameTheory
