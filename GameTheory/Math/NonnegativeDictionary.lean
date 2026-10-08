import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exit directions in nonnegative dictionaries

A nonnegative invertible basis cannot express a vector with a positive coordinate
using only nonpositive coefficients. This excludes terminal rays when every
entering column has a positive coordinate.
-/

namespace GameTheory.Math

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- A nonnegative matrix maps nonpositive vectors to nonpositive vectors. -/
theorem mulVec_nonpos_of_nonneg (B : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
    (hB : ∀ i j, 0 ≤ B i j) (hx : ∀ j, x j ≤ 0) :
    ∀ i, B.mulVec x i ≤ 0 := by
  intro i
  change (∑ j, B i j * x j) ≤ 0
  exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hB i j) (hx j)

/-- A positive entering coordinate forces a positive inverse-basis direction. -/
theorem exists_positive_inverse_mulVec (B : Matrix (Fin n) (Fin n) K) (c : Fin n → K)
    (hB : B.det ≠ 0) (hentries : ∀ i j, 0 ≤ B i j) (hc : ∃ i, 0 < c i) :
    ∃ j, 0 < B⁻¹.mulVec c j := by
  by_contra h
  have hn : ∀ j, B⁻¹.mulVec c j ≤ 0 := by
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
  have hm := mulVec_nonpos_of_nonneg B (B⁻¹.mulVec c) hentries hn
  simp only [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec] at hm
  obtain ⟨i, hi⟩ := hc
  exact (not_lt_of_ge (hm i)) hi

end GameTheory.Math
