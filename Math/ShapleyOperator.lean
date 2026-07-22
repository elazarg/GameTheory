/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Topology.MetricSpace.Contracting
import Math.Minimax.MinimaxLoomis
import Math.Probability

/-!
# The Shapley Operator and Discounted Values

The Shapley operator of a two-player zero-sum stochastic game in matrix
form: for a continuation value `v`, play at each state the one-shot matrix
game whose entries are the stage payoff plus `β` times the expected
continuation value, and take its maxmin value (`MinimaxLoomis.lam0`).

Nonexpansiveness of the matrix-game value in its entries
(`MinimaxLoomis.abs_lam0_sub_le_of_entrywise_abs_le`) makes the operator a
`β`-contraction in the sup metric, so for `β < 1` the discounted value
equation has a unique solution by the Banach fixed point theorem — the
existence and uniqueness of discounted values (Shapley 1953).  Optimal
stationary strategies and the vanishing-discount analysis toward uniform
values (Mertens–Neyman 1981) build on this.

## Main definitions

* `Math.ShapleyOperator.shapleyOperator` — the discounted one-shot
  evaluation operator

## Main results

* `Math.ShapleyOperator.lipschitzWith_shapleyOperator` — the operator is
  `β`-Lipschitz in the continuation value
* `Math.ShapleyOperator.existsUnique_fixedPoint_shapleyOperator` —
  **Shapley's theorem**: the discounted value equation has a unique
  solution for every discount factor `β < 1`
-/

namespace Math
namespace ShapleyOperator

open Math.Probability MinimaxLoomis
open scoped NNReal

variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J]
  [Nonempty I] [Nonempty J]

/-- The Shapley operator of the stochastic matrix game with stage payoffs
`u` and transitions `q` at discount factor `β`: evaluate at each state the
one-shot matrix game of current payoff plus discounted expected
continuation value. -/
noncomputable def shapleyOperator (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) (β : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => lam0 (fun i j => u s i j + β * expect (q s i j) v)

/-- Statewise Lipschitz bound for the Shapley operator. -/
theorem abs_shapleyOperator_sub_le (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ} (hβ0 : 0 ≤ β) (v w : S → ℝ) (s : S) :
    |shapleyOperator u q β v s - shapleyOperator u q β w s| ≤
      β * dist v w := by
  apply abs_lam0_sub_le_of_entrywise_abs_le
  intro i j
  have hE : |expect (q s i j) v - expect (q s i j) w| ≤ dist v w := by
    rw [← expect_sub]
    refine abs_expect_le_of_abs_le _ _ fun s' => ?_
    have hcoord := dist_le_pi_dist v w s'
    rwa [Real.dist_eq] at hcoord
  calc |(u s i j + β * expect (q s i j) v) -
        (u s i j + β * expect (q s i j) w)|
      = β * |expect (q s i j) v - expect (q s i j) w| := by
        rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0]
    _ ≤ β * dist v w := mul_le_mul_of_nonneg_left hE hβ0

/-- The Shapley operator is `β`-Lipschitz in the continuation value under
the sup metric. -/
theorem lipschitzWith_shapleyOperator (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) (β : ℝ≥0) :
    LipschitzWith β (shapleyOperator u q (β : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [Real.dist_eq]
  exact abs_shapleyOperator_sub_le u q β.coe_nonneg v w s

/-- The Shapley operator is a contraction for `β < 1`. -/
theorem contractingWith_shapleyOperator (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) :
    ContractingWith β (shapleyOperator u q (β : ℝ)) :=
  ⟨hβ, lipschitzWith_shapleyOperator u q β⟩

omit [Fintype S] in
/-- **Shapley's theorem (1953), value-equation form**: for every discount
factor `β < 1` the discounted value equation of a finite two-player
zero-sum stochastic game has a unique solution. -/
theorem existsUnique_fixedPoint_shapleyOperator [Finite S]
    (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) :
    ∃! v : S → ℝ, shapleyOperator u q (β : ℝ) v = v := by
  letI : Fintype S := Fintype.ofFinite S
  have hc := contractingWith_shapleyOperator u q hβ
  exact ⟨ContractingWith.fixedPoint (shapleyOperator u q (β : ℝ)) hc,
    hc.fixedPoint_isFixedPt,
    fun v hv => hc.fixedPoint_unique hv⟩

/-- The discounted value: the unique fixed point of the Shapley operator. -/
noncomputable def discountedValue (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) : S → ℝ :=
  ContractingWith.fixedPoint (shapleyOperator u q (β : ℝ))
    (contractingWith_shapleyOperator u q hβ)

/-- The discounted value solves the Shapley equation. -/
theorem shapleyOperator_discountedValue (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) :
    shapleyOperator u q (β : ℝ) (discountedValue u q hβ) =
      discountedValue u q hβ :=
  (contractingWith_shapleyOperator u q hβ).fixedPoint_isFixedPt

end ShapleyOperator
end Math
