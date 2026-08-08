/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PredecessorCharts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Root selection for the quadratic block-pair charts

The support-11 and support-13 predecessor charts leave one quadratic
compatibility equation.  This file gives the small root-selection consumer
used by both charts: opposite endpoint signs give a root, and positivity of
the exact quadratic derivative throughout the isolating interval makes that
root unique.
-/

noncomputable section

namespace GameTheory.BlockPairCharts

def quadraticValue (a b c z : ℝ) : ℝ :=
  a * z ^ 2 + b * z + c

def quadraticDerivative (a b z : ℝ) : ℝ :=
  2 * a * z + b

theorem quadratic_difference (a b c x y : ℝ) :
    quadraticValue a b c y - quadraticValue a b c x =
      (y - x) * (a * (x + y) + b) := by
  simp only [quadraticValue]
  ring

theorem quadratic_roots_eq_of_derivatives_positive
    {a b c x y : ℝ}
    (hx : quadraticValue a b c x = 0)
    (hy : quadraticValue a b c y = 0)
    (hdx : 0 < quadraticDerivative a b x)
    (hdy : 0 < quadraticDerivative a b y) :
    x = y := by
  have hsecant : 0 < a * (x + y) + b := by
    simp only [quadraticDerivative] at hdx hdy
    linarith
  have hproduct : (y - x) * (a * (x + y) + b) = 0 := by
    rw [← quadratic_difference, hy, hx]
    ring
  rcases mul_eq_zero.mp hproduct with hxy | hsecantZero
  · linarith
  · exact (hsecant.ne' hsecantZero).elim

/-- A sign bracket and positive quadratic derivative select exactly one root
in the closed bracket. -/
theorem existsUnique_quadratic_root_Icc
    (a b c lower upper : ℝ)
    (hlowerUpper : lower ≤ upper)
    (hlower : quadraticValue a b c lower ≤ 0)
    (hupper : 0 ≤ quadraticValue a b c upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < quadraticDerivative a b z) :
    ∃! z : ℝ, z ∈ Set.Icc lower upper ∧ quadraticValue a b c z = 0 := by
  have hcontinuous : ContinuousOn (quadraticValue a b c)
      (Set.Icc lower upper) := by
    unfold quadraticValue
    fun_prop
  have hzero : (0 : ℝ) ∈
      Set.Icc (quadraticValue a b c lower)
        (quadraticValue a b c upper) := ⟨hlower, hupper⟩
  obtain ⟨z, hzInterval, hzRoot⟩ :=
    intermediate_value_Icc hlowerUpper hcontinuous hzero
  refine ⟨z, ⟨hzInterval, hzRoot⟩, ?_⟩
  intro y hy
  exact quadratic_roots_eq_of_derivatives_positive hy.2 hzRoot
    (hderivative y hy.1) (hderivative z hzInterval)

/-- Strict endpoint signs put the selected root in the open bracket. -/
theorem existsUnique_quadratic_root_Ioo
    (a b c lower upper : ℝ)
    (hlowerUpper : lower < upper)
    (hlower : quadraticValue a b c lower < 0)
    (hupper : 0 < quadraticValue a b c upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < quadraticDerivative a b z) :
    ∃! z : ℝ, z ∈ Set.Ioo lower upper ∧ quadraticValue a b c z = 0 := by
  obtain ⟨z, ⟨hzInterval, hzRoot⟩, hzUnique⟩ :=
    existsUnique_quadratic_root_Icc a b c lower upper hlowerUpper.le
      hlower.le hupper.le hderivative
  have hzOpen : z ∈ Set.Ioo lower upper := by
    constructor
    · exact lt_of_le_of_ne hzInterval.1 fun hzeq ↦ by
        subst z
        linarith
    · exact lt_of_le_of_ne hzInterval.2 fun hzeq ↦ by
        subst z
        linarith
  refine ⟨z, ⟨hzOpen, hzRoot⟩, ?_⟩
  intro y hy
  apply hzUnique y
  exact ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2⟩

def supportThirteenDerivative
    (successor : BlockPairK11.Player → ℝ) (z : ℝ) : ℝ :=
  quadraticDerivative (supportThirteenA successor)
    (supportThirteenB successor) z

@[simp] theorem supportThirteenPolynomial_eq_quadratic
    (successor : BlockPairK11.Player → ℝ) (z : ℝ) :
    supportThirteenPolynomial successor z =
      quadraticValue (supportThirteenA successor)
        (supportThirteenB successor) (supportThirteenC successor) z := rfl

theorem existsUnique_supportThirteen_root_Ioo
    (successor : BlockPairK11.Player → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower < upper)
    (hlower : supportThirteenPolynomial successor lower < 0)
    (hupper : 0 < supportThirteenPolynomial successor upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < supportThirteenDerivative successor z) :
    ∃! z : ℝ, z ∈ Set.Ioo lower upper ∧
      supportThirteenPolynomial successor z = 0 := by
  exact existsUnique_quadratic_root_Ioo
    (supportThirteenA successor) (supportThirteenB successor)
    (supportThirteenC successor) lower upper hlowerUpper hlower hupper
    hderivative

/-- A rational isolating interval selects a unique support-13 chart point,
including its active indifference and predecessor-value semantics. -/
theorem existsUnique_supportThirteen_chart_Ioo
    (successor : BlockPairK11.Player → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower < upper)
    (hlower : supportThirteenPolynomial successor lower < 0)
    (hupper : 0 < supportThirteenPolynomial successor upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < supportThirteenDerivative successor z)
    (hzeroDenominator : ∀ z ∈ Set.Ioo lower upper,
      supportThirteenZeroDenominator successor z ≠ 0)
    (htwoDenominator : ∀ z ∈ Set.Ioo lower upper,
      supportThirteenTwoDenominator successor z ≠ 0) :
    ∃! z : ℝ,
      z ∈ Set.Ioo lower upper ∧
      supportThirteenPolynomial successor z = 0 ∧
      (difference (supportThirteenHazard successor z) successor 0 = 0 ∧
        difference (supportThirteenHazard successor z) successor 2 = 0 ∧
        difference (supportThirteenHazard successor z) successor 3 = 0) ∧
      predecessorValue (supportThirteenHazard successor z) successor =
        supportThirteenValue successor z := by
  obtain ⟨z, hz, hzUnique⟩ :=
    existsUnique_supportThirteen_root_Ioo successor lower upper
      hlowerUpper hlower hupper hderivative
  have hzero := hzeroDenominator z hz.1
  have htwo := htwoDenominator z hz.1
  refine ⟨z, ⟨hz.1, hz.2,
    supportThirteen_active successor z hzero htwo hz.2,
    supportThirteen_predecessorValue successor z hzero htwo hz.2⟩, ?_⟩
  intro y hy
  exact hzUnique y ⟨hy.1, hy.2.1⟩

def supportElevenDerivative
    (successor : BlockPairK11.Player → ℝ) (z : ℝ) : ℝ :=
  quadraticDerivative (supportElevenA successor)
    (supportElevenB successor) z

@[simp] theorem supportElevenPolynomial_eq_quadratic
    (successor : BlockPairK11.Player → ℝ) (z : ℝ) :
    supportElevenPolynomial successor z =
      quadraticValue (supportElevenA successor)
        (supportElevenB successor) (supportElevenC successor) z := rfl

theorem existsUnique_supportEleven_root_Ioo
    (successor : BlockPairK11.Player → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower < upper)
    (hlower : supportElevenPolynomial successor lower < 0)
    (hupper : 0 < supportElevenPolynomial successor upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < supportElevenDerivative successor z) :
    ∃! z : ℝ, z ∈ Set.Ioo lower upper ∧
      supportElevenPolynomial successor z = 0 := by
  exact existsUnique_quadratic_root_Ioo
    (supportElevenA successor) (supportElevenB successor)
    (supportElevenC successor) lower upper hlowerUpper hlower hupper
    hderivative

/-- A rational isolating interval selects a unique support-11 chart point,
including its active indifference and predecessor-value semantics. -/
theorem existsUnique_supportEleven_chart_Ioo
    (successor : BlockPairK11.Player → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower < upper)
    (hlower : supportElevenPolynomial successor lower < 0)
    (hupper : 0 < supportElevenPolynomial successor upper)
    (hderivative : ∀ z ∈ Set.Icc lower upper,
      0 < supportElevenDerivative successor z)
    (hzeroDenominator : ∀ z ∈ Set.Ioo lower upper,
      supportElevenZeroDenominator successor z ≠ 0)
    (honeDenominator : ∀ z ∈ Set.Ioo lower upper,
      supportElevenOneDenominator successor z ≠ 0) :
    ∃! z : ℝ,
      z ∈ Set.Ioo lower upper ∧
      supportElevenPolynomial successor z = 0 ∧
      (difference (supportElevenHazard successor z) successor 0 = 0 ∧
        difference (supportElevenHazard successor z) successor 1 = 0 ∧
        difference (supportElevenHazard successor z) successor 3 = 0) ∧
      predecessorValue (supportElevenHazard successor z) successor =
        supportElevenValue successor z := by
  obtain ⟨z, hz, hzUnique⟩ :=
    existsUnique_supportEleven_root_Ioo successor lower upper
      hlowerUpper hlower hupper hderivative
  have hzero := hzeroDenominator z hz.1
  have hone := honeDenominator z hz.1
  refine ⟨z, ⟨hz.1, hz.2,
    supportEleven_active successor z hzero hone hz.2,
    supportEleven_predecessorValue successor z hzero hone hz.2⟩, ?_⟩
  intro y hy
  exact hzUnique y ⟨hy.1, hy.2.1⟩

end GameTheory.BlockPairCharts
