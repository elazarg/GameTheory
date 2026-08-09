/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ZeroSum.Basic
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
* `discountedShapleyRatePayoff`: the canonical two-coordinate zero-sum payoff
  family built from `discountedShapleyRateValue`.
* `exists_nonzero_mvPolynomial_discountedShapleyRateValue`: the polynomial
  relation along the coupled discounted-value vector.
* `discountedShapleyKernelIdeal`: the canonical coupled kernel ideal over
  `ℝ[λ]`.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_kernelIdeal_moduleFinite`:
  zero-dimensionality of that ideal over `ℝ(λ)` gives a fixed bivariate
  relation for every value coordinate.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_activeBranches`:
  the same conclusion from fixed active-branch zero-dimensionality.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_nonvanishingActiveBranches`:
  the denominator-nonvanishing fixed-branch boundary.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_branchMonicRelations`:
  the same boundary expressed by checkable monic coordinate certificates.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_branchFiniteOrNilpotent`:
  a branchwise finite-or-denominator-nilpotent discharge criterion.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_uniqueState`:
  unconditional saturated-branch elimination for one-state games.
* `moduleFinite_discountedShapleyNonvanishingKernelBranchIdeal_of_forall_size_eq_one`:
  unconditional saturated-branch finiteness for every size-one kernel branch.
* `exists_nonzero_bivariate_discountedShapleyRateValue_of_activeKernelShapes_size_one`:
  a game-level bivariate relation when all active local kernels have size one.
* `discountedShapleyRateValue_twoState_elimination_dichotomy`: the bivariate
  relation/resultant-degeneracy dichotomy for a two-state game.
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

/-- The canonical two-player zero-sum payoff vector associated with the
rate-parameterized discounted Shapley value. -/
noncomputable def discountedShapleyRatePayoff
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (l : ℝ) : G.State → Payoff (Fin 2) :=
  fun s who =>
    if who = 0 then G.discountedShapleyRateValue l s
    else -G.discountedShapleyRateValue l s

@[simp]
theorem discountedShapleyRatePayoff_zero
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (l : ℝ) (s : G.State) :
    G.discountedShapleyRatePayoff l s 0 =
      G.discountedShapleyRateValue l s := by
  simp [discountedShapleyRatePayoff]

@[simp]
theorem discountedShapleyRatePayoff_one
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (l : ℝ) (s : G.State) :
    G.discountedShapleyRatePayoff l s 1 =
      -G.discountedShapleyRateValue l s := by
  simp [discountedShapleyRatePayoff]

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

/-- Normalized nonnegative row payoffs give a nonnegative canonical
rate-parameterized Shapley value, including its total zero extension. -/
theorem discountedShapleyRateValue_nonneg
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSum)
    (hpayLower : ∀ s a, 0 ≤ G.stagePayoff s a 0)
    (l : ℝ) (s : G.State) :
    0 ≤ G.discountedShapleyRateValue l s := by
  by_cases hl : 0 < l
  · rw [G.discountedShapleyRateValue_eq hl]
    exact G.discountedShapleyValue_nonneg hzs
      (discountFactorOfRate_lt_one hl) hpayLower s
  · simp [discountedShapleyRateValue, hl]

/-- Normalized row payoffs bounded above by one give the same upper bound for
the canonical rate-parameterized Shapley value. -/
theorem discountedShapleyRateValue_le_one
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSum)
    (hpayLower : ∀ s a, 0 ≤ G.stagePayoff s a 0)
    (hpayUpper : ∀ s a, G.stagePayoff s a 0 ≤ 1)
    (l : ℝ) (s : G.State) :
    G.discountedShapleyRateValue l s ≤ 1 := by
  by_cases hl : 0 < l
  · rw [G.discountedShapleyRateValue_eq hl]
    exact G.discountedShapleyValue_le_one hzs
      (discountFactorOfRate_lt_one hl) hpayLower hpayUpper s
  · simp [discountedShapleyRateValue, hl]

/-- The rate-parameterized discounted Shapley value satisfies the coupled
normalized Shapley equation on `0 < λ ≤ 1`. -/
theorem discountedShapleyRateValue_eq_lam0
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    {l : ℝ} (hl : l ∈ Set.Ioc (0 : ℝ) 1)
    (s : G.State) :
    G.discountedShapleyRateValue l s =
      MinimaxLoomis.lam0
        (fun i j =>
          l * G.rowStagePayoff s i j +
            (1 - l) * ∑ z,
              (G.pairTransition s i j z).toReal *
                G.discountedShapleyRateValue l z) := by
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

/-- The canonical normalized value is locally Lipschitz in the positive
rate. The explicit asymmetric modulus is useful near a fixed positive rate;
no uniform estimate is asserted as the rate approaches zero. -/
theorem dist_discountedShapleyRateValue_le
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSum)
    (hpayLower : ∀ s a, 0 ≤ G.stagePayoff s a 0)
    (hpayUpper : ∀ s a, G.stagePayoff s a 0 ≤ 1)
    {l m : ℝ} (hl : l ∈ Set.Ioc (0 : ℝ) 1)
    (hm : m ∈ Set.Ioc (0 : ℝ) 1) :
    dist (G.discountedShapleyRateValue l)
        (G.discountedShapleyRateValue m) ≤
      |l - m| / l := by
  let vl := G.discountedShapleyRateValue l
  let vm := G.discountedShapleyRateValue m
  have hcoord (s : G.State) :
      |vl s - vm s| ≤
        (1 - l) * dist vl vm + |l - m| := by
    have hvl :
        vl s =
          MinimaxLoomis.lam0 fun i j =>
            l * G.rowStagePayoff s i j +
              (1 - l) *
                Math.Probability.expect
                  (G.pairTransition s i j) vl := by
      simpa only [vl, Math.Probability.expect_eq_sum] using
        G.discountedShapleyRateValue_eq_lam0 hl s
    have hvm :
        vm s =
          MinimaxLoomis.lam0 fun i j =>
            m * G.rowStagePayoff s i j +
              (1 - m) *
                Math.Probability.expect
                  (G.pairTransition s i j) vm := by
      simpa only [vm, Math.Probability.expect_eq_sum] using
        G.discountedShapleyRateValue_eq_lam0 hm s
    rw [hvl, hvm]
    apply MinimaxLoomis.abs_lam0_sub_le_of_entrywise_abs_le
    intro i j
    let d := G.pairTransition s i j
    let El := Math.Probability.expect d vl
    let Em := Math.Probability.expect d vm
    have hEsub : |El - Em| ≤ dist vl vm := by
      rw [← Math.Probability.expect_sub]
      refine Math.Probability.abs_expect_le_of_abs_le
        _ _ fun z => ?_
      have hz := dist_le_pi_dist vl vm z
      rwa [Real.dist_eq] at hz
    have hEm0 : 0 ≤ Em := by
      apply Math.Probability.expect_nonneg
      intro z
      exact G.discountedShapleyRateValue_nonneg
        hzs hpayLower m z
    have hEm1 : Em ≤ 1 := by
      calc
        Em ≤
            Math.Probability.expect d (fun _ => (1 : ℝ)) := by
          apply Math.Probability.expect_mono
          intro z
          exact G.discountedShapleyRateValue_le_one
            hzs hpayLower hpayUpper m z
        _ = 1 := by simp
    have hr0 : 0 ≤ G.rowStagePayoff s i j :=
      hpayLower s (G.pairJointAct i j)
    have hr1 : G.rowStagePayoff s i j ≤ 1 :=
      hpayUpper s (G.pairJointAct i j)
    have hrE :
        |G.rowStagePayoff s i j - Em| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hid :
        (l * G.rowStagePayoff s i j + (1 - l) * El) -
            (m * G.rowStagePayoff s i j + (1 - m) * Em) =
          (1 - l) * (El - Em) +
            (l - m) *
              (G.rowStagePayoff s i j - Em) := by
      ring
    rw [hid]
    calc
      |(1 - l) * (El - Em) +
          (l - m) * (G.rowStagePayoff s i j - Em)|
          ≤ |(1 - l) * (El - Em)| +
              |(l - m) *
                (G.rowStagePayoff s i j - Em)| :=
        abs_add_le _ _
      _ = (1 - l) * |El - Em| +
            |l - m| *
              |G.rowStagePayoff s i j - Em| := by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (sub_nonneg.mpr hl.2)]
      _ ≤ (1 - l) * dist vl vm + |l - m| := by
        have hleft :=
          mul_le_mul_of_nonneg_left hEsub
            (sub_nonneg.mpr hl.2)
        have hright :=
          mul_le_mul_of_nonneg_left hrE
            (abs_nonneg (l - m))
        linarith
  have hnorm :
      dist vl vm ≤
        (1 - l) * dist vl vm + |l - m| := by
    rw [dist_pi_le_iff
      (add_nonneg
        (mul_nonneg (sub_nonneg.mpr hl.2) dist_nonneg)
        (abs_nonneg _))]
    intro s
    rw [Real.dist_eq]
    exact hcoord s
  apply (le_div_iff₀ hl.1).2
  change dist vl vm * l ≤ |l - m|
  calc
    dist vl vm * l =
        dist vl vm - (1 - l) * dist vl vm := by ring
    _ ≤ |l - m| := by linarith

/-- The canonical normalized discounted value varies continuously throughout
the positive-rate domain. -/
theorem continuousOn_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSum)
    (hpayLower : ∀ s a, 0 ≤ G.stagePayoff s a 0)
    (hpayUpper : ∀ s a, G.stagePayoff s a 0 ≤ 1) :
    ContinuousOn G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro l hl ε hε
  refine ⟨ε * l, mul_pos hε hl.1, ?_⟩
  intro m hm hml
  calc
    dist (G.discountedShapleyRateValue m)
        (G.discountedShapleyRateValue l) =
        dist (G.discountedShapleyRateValue l)
          (G.discountedShapleyRateValue m) := dist_comm _ _
    _ ≤ |l - m| / l :=
      G.dist_discountedShapleyRateValue_le
        hzs hpayLower hpayUpper hl hm
    _ < ε := by
      apply (div_lt_iff₀ hl.1).2
      simpa only [Real.dist_eq, abs_sub_comm] using hml

/-- Coordinate form of positive-rate continuity for use by scalar algebraic
selection theorems. -/
theorem continuousOn_discountedShapleyRateValue_apply
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSum)
    (hpayLower : ∀ s a, 0 ≤ G.stagePayoff s a 0)
    (hpayUpper : ∀ s a, G.stagePayoff s a 0 ≤ 1)
    (z : G.State) :
    ContinuousOn (fun l => G.discountedShapleyRateValue l z)
      (Set.Ioc (0 : ℝ) 1) :=
  (continuous_apply z).comp_continuousOn
    (G.continuousOn_discountedShapleyRateValue
      hzs hpayLower hpayUpper)

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
  exact fun l hl s =>
    G.discountedShapleyRateValue_eq_lam0 hl s

/-- The canonical coupled bordered-kernel ideal for a finite zero-sum
stochastic game, with the discount rate in the coefficient ring `ℝ[λ]`. -/
noncomputable def discountedShapleyKernelIdeal
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)] :
    Ideal (MvPolynomial G.State (Polynomial ℝ)) :=
  ShapleySnow.discountedShapleyActiveSystemIdeal
    G.rowStagePayoff
    (fun s i j z => (G.pairTransition s i j z).toReal)

/-- The localized coupled ideal obtained from a fixed kernel-shape choice at
each state. An inactive choice makes this the unit ideal. -/
noncomputable def discountedShapleyKernelBranchIdeal
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    (branch : G.State →
      ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1)) :
    Ideal
      (MvPolynomial G.State (FractionRing (Polynomial ℝ))) :=
  ShapleySnow.discountedShapleyActiveBranchIdeal
    G.rowStagePayoff
    (fun s i j z => (G.pairTransition s i j z).toReal)
    branch

/-- The fixed branch ideal with one extra variable witnessing the inverse of
the product of its selected bordered denominators. -/
noncomputable def discountedShapleyNonvanishingKernelBranchIdeal
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    (branch : G.State →
      ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1)) :
    Ideal
      (MvPolynomial (Option G.State) (Polynomial ℝ)) :=
  ShapleySnow.discountedShapleyNonvanishingBranchIdeal
    G.rowStagePayoff
    (fun s i j z => (G.pairTransition s i j z).toReal)
    branch

/-- The selected branch denominator product after extending coefficients to
`ℝ(λ)`. -/
noncomputable def discountedShapleyKernelBranchDenominator
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    (branch : G.State →
      ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1)) :
    MvPolynomial G.State (FractionRing (Polynomial ℝ)) :=
  MvPolynomial.map
    (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))
    (ShapleySnow.discountedShapleyBranchDenominator
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      branch)

/-- Every branch that selects one pure row action and one pure column action
at each state has finite-dimensional denominator-nonvanishing quotient. -/
theorem moduleFinite_discountedShapleyNonvanishingKernelBranchIdeal_of_pure
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [Nonempty (G.Act 0)]
    (row : G.State → G.Act 0)
    (col : G.State → G.Act 1) :
    Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial (Option G.State)
          (FractionRing (Polynomial ℝ)) ⧸
        (G.discountedShapleyNonvanishingKernelBranchIdeal
          (ShapleySnow.pureActionKernelBranch row col)).map
            (MvPolynomial.map
              (algebraMap (Polynomial ℝ)
                (FractionRing (Polynomial ℝ))))) := by
  exact
    ShapleySnow.moduleFinite_discountedShapleyNonvanishingBranchIdeal_of_pure
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      row col

/-- Every game-level branch whose selected kernels all have size one has
finite-dimensional denominator-nonvanishing quotient. -/
theorem moduleFinite_discountedShapleyNonvanishingKernelBranchIdeal_of_forall_size_eq_one
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [Nonempty (G.Act 0)]
    (branch : G.State →
      ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1))
    (hsize : ∀ s, (branch s).1.val = 1) :
    Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial (Option G.State)
          (FractionRing (Polynomial ℝ)) ⧸
        (G.discountedShapleyNonvanishingKernelBranchIdeal branch).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ))))) := by
  exact
    ShapleySnow.moduleFinite_discountedShapleyNonvanishingBranchIdeal_of_forall_size_eq_one
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      branch hsize

/-- If the canonical coupled kernel ideal is zero-dimensional over `ℝ(λ)`,
the canonical discounted Shapley value has a fixed nonzero bivariate relation
in the rate and each chosen state value. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_kernelIdeal_moduleFinite
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    [Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial G.State (FractionRing (Polynomial ℝ)) ⧸
        (ShapleySnow.discountedShapleyActiveSystemIdeal
          G.rowStagePayoff
          (fun s i j z =>
            (G.pairTransition s i j z).toReal)).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))]
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_discountedShapleyActiveSystemIdeal_moduleFinite
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      target

/-- Fixed active-branch zero-dimensionality is sufficient for the canonical
discounted Shapley value to satisfy a nonzero bivariate relation. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_activeBranches
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hbranch : ∀ branch : G.State →
        ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1),
      (∀ s, ShapleySnow.IsActiveKernelShape
        (ShapleySnow.discountedStochasticEntry
          (G.rowStagePayoff s)
          (fun i j z => (G.pairTransition s i j z).toReal))
        (branch s)) →
      Module.Finite (FractionRing (Polynomial ℝ))
        (MvPolynomial G.State (FractionRing (Polynomial ℝ)) ⧸
          G.discountedShapleyKernelBranchIdeal branch))
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  letI : Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial G.State (FractionRing (Polynomial ℝ)) ⧸
        (ShapleySnow.discountedShapleyActiveSystemIdeal
          G.rowStagePayoff
          (fun s i j z =>
            (G.pairTransition s i j z).toReal)).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ))))) :=
    ShapleySnow.moduleFinite_discountedShapleyActiveSystemIdeal_of_activeBranches
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      (fun branch hactive => hbranch branch hactive)
  exact
    G.exists_nonzero_bivariate_discountedShapleyRateValue_of_kernelIdeal_moduleFinite
      target

/-- Zero-dimensionality of every fixed active branch after enforcing
nonvanishing of its selected bordered denominators gives a fixed bivariate
relation for the canonical discounted Shapley value. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_nonvanishingActiveBranches
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hfinite : ∀ branch : G.State →
        ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1),
      (∀ s, ShapleySnow.IsActiveKernelShape
        (ShapleySnow.discountedStochasticEntry
          (G.rowStagePayoff s)
          (fun i j z => (G.pairTransition s i j z).toReal))
        (branch s)) →
      Module.Finite (FractionRing (Polynomial ℝ))
        (MvPolynomial (Option G.State) (FractionRing (Polynomial ℝ)) ⧸
          (G.discountedShapleyNonvanishingKernelBranchIdeal branch).map
            (MvPolynomial.map
              (algebraMap (Polynomial ℝ)
                (FractionRing (Polynomial ℝ))))))
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_nonvanishingActiveBranches_moduleFinite
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      hfinite target

/-- Every active fixed branch may be discharged either by
finite-dimensionality before saturation or by nilpotence of its selected
denominator product. Either certificate gives a fixed bivariate relation for
the canonical discounted Shapley value. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_branchFiniteOrNilpotent
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hbranch : ∀ branch : G.State →
        ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1),
      (∀ s, ShapleySnow.IsActiveKernelShape
        (ShapleySnow.discountedStochasticEntry
          (G.rowStagePayoff s)
          (fun i j z => (G.pairTransition s i j z).toReal))
        (branch s)) →
      Module.Finite (FractionRing (Polynomial ℝ))
          (MvPolynomial G.State (FractionRing (Polynomial ℝ)) ⧸
            G.discountedShapleyKernelBranchIdeal branch) ∨
        G.discountedShapleyKernelBranchDenominator branch ∈
          (G.discountedShapleyKernelBranchIdeal branch).radical)
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_activeBranches_finite_or_denominatorNilpotent
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      hbranch target

/-- Monic relations for every coordinate of every saturated active branch
are an explicit certificate for a fixed bivariate relation satisfied by the
canonical discounted Shapley value. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_branchMonicRelations
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hrelations : ∀ branch : G.State →
        ShapleySnow.ActionKernelShape (G.Act 0) (G.Act 1),
      (∀ s, ShapleySnow.IsActiveKernelShape
        (ShapleySnow.discountedStochasticEntry
          (G.rowStagePayoff s)
          (fun i j z => (G.pairTransition s i j z).toReal))
        (branch s)) →
      ∃ p : Option G.State →
          Polynomial (FractionRing (Polynomial ℝ)),
        (∀ i, (p i).Monic) ∧
        ∀ i,
          Polynomial.aeval (MvPolynomial.X i) (p i) ∈
            (G.discountedShapleyNonvanishingKernelBranchIdeal branch).map
              (MvPolynomial.map
                (algebraMap (Polynomial ℝ)
                  (FractionRing (Polynomial ℝ)))))
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_nonvanishingActiveBranches_monicRelations
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      hrelations target

/-- If every denominator-active local Shapley--Snow kernel has size one, every
saturated branch is affine-linear and the canonical discounted value satisfies
a fixed nonzero bivariate relation at every state. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_activeKernelShapes_size_one
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hsize : ∀ s k,
      ShapleySnow.IsActiveKernelShape
          (ShapleySnow.discountedStochasticEntry
            (G.rowStagePayoff s)
            (fun i j z => (G.pairTransition s i j z).toReal)) k →
        k.1.val = 1)
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_activeKernelShapes_size_one
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      hsize target

/-- In a one-state zero-sum stochastic game, the saturated fixed-branch
argument gives a fixed bivariate relation with no algebraic hypothesis. -/
theorem exists_nonzero_bivariate_discountedShapleyRateValue_of_uniqueState
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [Unique G.State]
    [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (target : G.State) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ Set.Ioc (0 : ℝ) 1,
        Polynomial.eval
          (G.discountedShapleyRateValue l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.exists_nonzero_bivariateRelation_of_uniqueState
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      target

/-- For a two-state game, pairwise elimination of local kernel candidates
either produces a nonzero bivariate relation for the target discounted value
or identifies a specific active nonzero kernel pair with zero formal
resultant. -/
theorem discountedShapleyRateValue_twoState_elimination_dichotomy
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (target other : G.State) (hne : target ≠ other)
    (hcover : ∀ z : G.State, z = target ∨ z = other) :
    (∃ l ∈ Set.Ioc (0 : ℝ) 1,
      ∃ kt ko : ShapleySnow.ActionKernelShape
        (G.Act 0) (G.Act 1),
      ShapleySnow.mvBorderedKernelPoly
          (ShapleySnow.discountedStochasticEntry
            (G.rowStagePayoff target)
            (fun i j z =>
              (G.pairTransition target i j z).toReal))
          (some target) kt ≠ 0 ∧
      ShapleySnow.mvBorderedKernelPoly
          (ShapleySnow.discountedStochasticEntry
            (G.rowStagePayoff other)
            (fun i j z =>
              (G.pairTransition other i j z).toReal))
          (some other) ko ≠ 0 ∧
      MvPolynomial.eval
          (fun x => Option.casesOn x l
            (G.discountedShapleyRateValue l))
          (ShapleySnow.mvBorderedKernelPoly
            (ShapleySnow.discountedStochasticEntry
              (G.rowStagePayoff target)
              (fun i j z =>
                (G.pairTransition target i j z).toReal))
            (some target) kt) = 0 ∧
      MvPolynomial.eval
          (fun x => Option.casesOn x l
            (G.discountedShapleyRateValue l))
          (ShapleySnow.mvBorderedKernelPoly
            (ShapleySnow.discountedStochasticEntry
              (G.rowStagePayoff other)
              (fun i j z =>
                (G.pairTransition other i j z).toReal))
            (some other) ko) = 0 ∧
      (Polynomial.resultant
          (Math.MultivariateElimination.isolateVariable
            (some other)
            (ShapleySnow.mvBorderedKernelPoly
              (ShapleySnow.discountedStochasticEntry
                (G.rowStagePayoff target)
                (fun i j z =>
                  (G.pairTransition target i j z).toReal))
              (some target) kt))
          (Math.MultivariateElimination.isolateVariable
            (some other)
            (ShapleySnow.mvBorderedKernelPoly
              (ShapleySnow.discountedStochasticEntry
                (G.rowStagePayoff other)
                (fun i j z =>
                  (G.pairTransition other i j z).toReal))
              (some other) ko)) = 0)) ∨
      ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
        ∀ l ∈ Set.Ioc (0 : ℝ) 1,
          Polynomial.eval
            (G.discountedShapleyRateValue l target)
            (Polynomial.map
              (Polynomial.evalRingHom l) R) = 0 := by
  exact
    ShapleySnow.discountedShapleySystem_twoState_kernelPair_elimination_dichotomy
      G.rowStagePayoff
      (fun s i j z => (G.pairTransition s i j z).toReal)
      G.discountedShapleyRateValue
      (Set.Ioc (0 : ℝ) 1)
      (fun l hl s =>
        G.discountedShapleyRateValue_eq_lam0 hl s)
      target other hne hcover

end StochasticGame
end GameTheory
