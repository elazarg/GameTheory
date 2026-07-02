/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Mathlib.Analysis.Convex.StdSimplex

/-!
# PMFs and finite simplices

This file provides a small bridge between finite `PMF`s and the standard
simplex in the ambient vector space `α → ℝ`.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace ProbabilityMassFunction

variable {α : Type*}

/-- The real coordinate vector associated to a finite probability mass
function. -/
def toVector [Fintype α] (μ : PMF α) : α → ℝ :=
  fun a => (μ a).toReal

/-- The coordinate vector of a finite `PMF` belongs to the standard simplex. -/
theorem toVector_mem_stdSimplex [Fintype α] (μ : PMF α) :
    toVector μ ∈ stdSimplex ℝ α := by
  refine ⟨fun a => ENNReal.toReal_nonneg, ?_⟩
  exact Math.Probability.pmf_toReal_sum_one μ

/-- The coordinate-vector map from finite `PMF`s is injective. -/
theorem toVector_injective [Fintype α] :
    Function.Injective (toVector : PMF α → α → ℝ) := by
  intro μ ν h
  apply PMF.ext
  intro a
  have hreal : (μ a).toReal = (ν a).toReal := congrFun h a
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top μ a) (PMF.apply_ne_top ν a)).mp hreal

@[simp]
theorem toVector_pos_iff_ne_zero [Fintype α] (μ : PMF α) (a : α) :
    0 < toVector μ a ↔ μ a ≠ 0 := by
  constructor
  · intro h hzero
    simp [toVector, hzero] at h
  · intro h
    exact ENNReal.toReal_pos h (PMF.apply_ne_top μ a)

/-- Turn a point of the finite standard simplex into a `PMF`. -/
def ofVector [Fintype α] (w : α → ℝ) (hw : w ∈ stdSimplex ℝ α) : PMF α :=
  ⟨fun a => ENNReal.ofReal (w a), by
    have hsum : ∑ a : α, ENNReal.ofReal (w a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw.1 a), hw.2]
      norm_num
    simpa [tsum_fintype, hsum] using (hasSum_fintype (fun a : α => ENNReal.ofReal (w a)))⟩

@[simp]
theorem ofVector_apply [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α) (a : α) :
    ofVector w hw a = ENNReal.ofReal (w a) :=
  rfl

@[simp]
theorem ofVector_toReal [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α) (a : α) :
    ((ofVector w hw) a).toReal = w a := by
  rw [ofVector_apply]
  exact ENNReal.toReal_ofReal (hw.1 a)

@[simp]
theorem ofVector_ne_zero_iff [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α)
    (a : α) :
    ofVector w hw a ≠ 0 ↔ 0 < w a := by
  constructor
  · intro h
    have hpos := ENNReal.toReal_pos h (PMF.apply_ne_top (ofVector w hw) a)
    rwa [ofVector_toReal hw a] at hpos
  · intro h hzero
    have hreal : ((ofVector w hw) a).toReal = 0 := by simp [hzero]
    rw [ofVector_toReal hw a] at hreal
    linarith

/-- Converting a simplex vector to a `PMF` and back recovers the vector. -/
theorem toVector_ofVector [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α) :
    toVector (ofVector w hw) = w := by
  funext a
  exact ofVector_toReal hw a

end ProbabilityMassFunction
end Math
