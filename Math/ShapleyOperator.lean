/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Topology.MetricSpace.Contracting
import Math.Minimax.MinimaxLoomis
import Math.Minimax.Loomis
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

/-- The discounted value at a state is the maxmin value of its auxiliary
one-shot matrix game. -/
theorem discountedValue_eq_lam0 (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) (s : S) :
    discountedValue u q hβ s =
      lam0 (fun i j =>
        u s i j + (β : ℝ) * expect (q s i j) (discountedValue u q hβ)) :=
  (congrFun (shapleyOperator_discountedValue u q hβ) s).symm

/-- Row player's one-shot optimality certificate at the discounted value:
a mixed action guaranteeing the value against every column of the
auxiliary game. -/
theorem exists_row_optimal_discountedValue (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) (s : S) :
    ∃ xx : stdSimplex ℝ I, ∀ j : J,
      discountedValue u q hβ s ≤
        wsum xx (fun i =>
          u s i j + (β : ℝ) * expect (q s i j) (discountedValue u q hβ)) := by
  obtain ⟨xx, hxx⟩ := exists_xx_lam0
    (fun i j => u s i j + (β : ℝ) * expect (q s i j) (discountedValue u q hβ))
  refine ⟨xx, fun j => ?_⟩
  rw [discountedValue_eq_lam0 u q hβ s]
  exact hxx j

/-- Column player's one-shot optimality certificate at the discounted
value: a mixed action capping the payoff by the value against every row of
the auxiliary game. -/
theorem exists_col_optimal_discountedValue (u : S → I → J → ℝ)
    (q : S → I → J → PMF S) {β : ℝ≥0} (hβ : β < 1) (s : S) :
    ∃ yy : stdSimplex ℝ J, ∀ i : I,
      wsum yy (fun j =>
        u s i j + (β : ℝ) * expect (q s i j) (discountedValue u q hβ)) ≤
        discountedValue u q hβ s := by
  obtain ⟨yy, hyy⟩ := exists_yy_mu0
    (fun i j => u s i j + (β : ℝ) * expect (q s i j) (discountedValue u q hβ))
  refine ⟨yy, fun i => ?_⟩
  rw [discountedValue_eq_lam0 u q hβ s, Loomis.minmax_from_general]
  exact hyy i

/-- A stage payoff bound bounds the (unnormalized) discounted value by the
geometric-series total `U / (1 - β)`. -/
theorem abs_discountedValue_le (u : S → I → J → ℝ) (q : S → I → J → PMF S)
    {β : ℝ≥0} (hβ : β < 1) {U : ℝ} (hU : ∀ s i j, |u s i j| ≤ U) (s : S) :
    |discountedValue u q hβ s| ≤ U / (1 - (β : ℝ)) := by
  set v := discountedValue u q hβ
  have hβ1 : (β : ℝ) < 1 := by exact_mod_cast hβ
  have h1β : (0 : ℝ) < 1 - (β : ℝ) := by linarith
  have hU0 : 0 ≤ U :=
    (abs_nonneg _).trans (hU s (Classical.arbitrary I) (Classical.arbitrary J))
  have hstep : ∀ s' : S, |v s'| ≤ U + (β : ℝ) * ‖v‖ := by
    intro s'
    have hpt : v s' =
        lam0 (fun i j => u s' i j + (β : ℝ) * expect (q s' i j) v) :=
      (congrFun (shapleyOperator_discountedValue u q hβ) s').symm
    rw [hpt]
    refine abs_lam0_le fun i j => ?_
    have hE : |expect (q s' i j) v| ≤ ‖v‖ := by
      refine abs_expect_le_of_abs_le _ _ fun s'' => ?_
      have hc := norm_le_pi_norm v s''
      rwa [Real.norm_eq_abs] at hc
    calc |u s' i j + (β : ℝ) * expect (q s' i j) v|
        ≤ |u s' i j| + |(β : ℝ) * expect (q s' i j) v| := abs_add_le _ _
      _ ≤ U + (β : ℝ) * ‖v‖ := by
          rw [abs_mul, abs_of_nonneg β.coe_nonneg]
          exact add_le_add (hU s' i j)
            (mul_le_mul_of_nonneg_left hE β.coe_nonneg)
  have hnorm : ‖v‖ ≤ U + (β : ℝ) * ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg
      (add_nonneg hU0 (mul_nonneg β.coe_nonneg (norm_nonneg v)))).mpr
      fun s' => ?_
    rw [Real.norm_eq_abs]
    exact hstep s'
  have hMU : ‖v‖ * (1 - (β : ℝ)) ≤ U := by nlinarith [hnorm]
  have hvs : |v s| ≤ ‖v‖ := by
    have hc := norm_le_pi_norm v s
    rwa [Real.norm_eq_abs] at hc
  exact hvs.trans ((le_div_iff₀ h1β).mpr hMU)

end ShapleyOperator
end Math
