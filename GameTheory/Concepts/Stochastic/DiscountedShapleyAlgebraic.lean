/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ZeroSum
import Math.Minimax.DiscountedShapleySystem

/-!
# Algebraic relations for discounted stochastic-game values

This module connects the normalized discounted Shapley value of a finite
two-player zero-sum stochastic game to its coupled polynomial system.

The rate `λ` is the weight of the current-stage payoff, while the Shapley
operator uses the continuation discount `β = 1 - λ`. The definitions below
extend this correspondence to a total function of `λ`; on `Set.Ioc 0 1` it
is exactly the canonical fixed point already defined in `ZeroSum`.

The main theorem packages all statewise Shapley--Snow kernel choices into a
single fixed nonzero multivariate polynomial. Its variables are `λ` and one
discounted-value coordinate per state.

## Main declarations

* `discountFactorOfRate`: the continuation discount associated to a
  current-stage rate.
* `discountedShapleyRateValue`: the discounted Shapley value as a total
  function of the current-stage rate.
* `exists_nonzero_mvPolynomial_discountedShapleyRateValue`: the polynomial
  relation along the coupled discounted-value vector.
-/

noncomputable section

open scoped NNReal

namespace GameTheory
namespace StochasticGame

/-- The continuation discount corresponding to current-stage rate `λ`.
Truncation at zero makes the definition total on `ℝ`. -/
def discountFactorOfRate (l : ℝ) : ℝ≥0 :=
  ⟨max (1 - l) 0, le_max_right _ _⟩

/-- A positive current-stage rate gives a continuation discount below one. -/
theorem discountFactorOfRate_lt_one {l : ℝ} (hl : 0 < l) :
    discountFactorOfRate l < 1 := by
  change max (1 - l) 0 < 1
  exact max_lt (by linarith) zero_lt_one

/-- On rates at most one, truncation does not change `1 - λ`. -/
@[simp]
theorem coe_discountFactorOfRate {l : ℝ} (hl : l ≤ 1) :
    (discountFactorOfRate l : ℝ) = 1 - l := by
  change max (1 - l) 0 = 1 - l
  exact max_eq_left (sub_nonneg.mpr hl)

/-- The canonical normalized discounted Shapley value, parameterized by the
current-stage rate. The zero branch only supplies a total extension outside
the positive-rate domain. -/
noncomputable def discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (l : ℝ) : G.State → ℝ :=
  if hl : 0 < l then
    G.discountedShapleyValue (discountFactorOfRate_lt_one hl)
  else
    0

/-- At a positive rate, `discountedShapleyRateValue` is the canonical
discounted Shapley fixed point with continuation discount `1 - λ`. -/
theorem discountedShapleyRateValue_eq
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    {l : ℝ} (hl : 0 < l) :
    G.discountedShapleyRateValue l =
      G.discountedShapleyValue (discountFactorOfRate_lt_one hl) := by
  simp [discountedShapleyRateValue, hl]

/-- Every coordinate of the canonical discounted Shapley value satisfies a
fixed nonzero multivariate polynomial relation in the rate and the full
finite-state value vector. -/
theorem exists_nonzero_mvPolynomial_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (target : G.State) :
    ∃ Q : MvPolynomial (Option G.State) ℝ, Q ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        MvPolynomial.eval
          (fun x => Option.casesOn x l
            (G.discountedShapleyRateValue l)) Q = 0 := by
  apply ShapleySnow.exists_nonzero_mvPolynomial_of_discountedShapleySystem
    G.rowStagePayoff
    (fun s i j z => (G.pairTransition s i j z).toReal)
    G.discountedShapleyRateValue
    (Set.Ioc (0 : ℝ) 1)
    _ target
  intro l hl s
  have hl0 : 0 < l := hl.1
  have hl1 : l ≤ 1 := hl.2
  have hβ := discountFactorOfRate_lt_one hl0
  rw [discountedShapleyRateValue_eq G hl0]
  change
    Math.ShapleyOperator.discountedValue
        (G.normalizedRowStagePayoff
          (discountFactorOfRate l : ℝ))
        G.pairTransition hβ s =
      _
  rw [Math.ShapleyOperator.discountedValue_eq_lam0]
  apply congrArg MinimaxLoomis.lam0
  funext i j
  rw [Math.Probability.expect_eq_sum]
  simp only [normalizedRowStagePayoff]
  rw [coe_discountFactorOfRate hl1]
  congr 1
  · ring
  · congr 1
    apply Finset.sum_congr rfl
    intro z _
    unfold discountedShapleyValue
    rw [coe_discountFactorOfRate hl1]

end StochasticGame
end GameTheory
