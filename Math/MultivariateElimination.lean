/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Elimination of one multivariate polynomial variable

This module isolates one variable of a real multivariate polynomial as the
outer variable of a univariate polynomial. The resultant of two such
polynomials eliminates that variable.

The eliminant includes the leading coefficient of the first polynomial. This
factor covers specializations at which its degree drops: any common zero of
the original polynomials maps to a zero of the eliminant without a
specialization hypothesis. Nonvanishing of the eliminant is separated into
the exact algebraic condition that the formal resultant is nonzero.

## Main declarations

* `isolateVariable`: view a selected multivariate variable as a univariate
  polynomial variable.
* `eliminateVariable`: resultant eliminant, including the degree-drop locus.
* `eval_eliminateVariable_eq_zero`: common zeros descend through elimination.
* `eliminateVariable_ne_zero`: the formal resultant condition ensures that the
  eliminant carries information.
-/

noncomputable section

namespace Math
namespace MultivariateElimination

/-- Resultant vanishing at the actual degrees persists when the determinant
uses any larger degree bounds. -/
theorem resultant_eq_zero_of_le_of_not_isCoprime
    {K : Type*} [Field K]
    {f g : Polynomial K} {m n : ℕ}
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n)
    (hfg : f ≠ 0 ∨ g ≠ 0) (h : ¬ IsCoprime f g) :
    Polynomial.resultant f g m n = 0 := by
  have hbase : Polynomial.resultant f g = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨hfg, h⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
    hk', Polynomial.resultant_add_right_deg _ _ _ _ k' le_rfl,
    hbase, mul_zero, mul_zero]

/-- Regard `i` as the outer univariate variable and all other variables as
coefficients. -/
noncomputable def isolateVariable
    {σ : Type*} (i : σ) :
    MvPolynomial σ ℝ ≃ₐ[ℝ]
      Polynomial (MvPolynomial {j : σ // j ≠ i} ℝ) := by
  classical
  exact
    (MvPolynomial.renameEquiv ℝ
        (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft ℝ _)

/-- Evaluation commutes with isolating a variable. -/
theorem eval_isolateVariable
    {σ : Type*} (i : σ) (P : MvPolynomial σ ℝ)
    (a : σ → ℝ) :
    MvPolynomial.eval a P =
      Polynomial.eval (a i)
        (Polynomial.map
          (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
          (isolateVariable i P)) := by
  classical
  let b : Option {j : σ // j ≠ i} → ℝ :=
    fun x => Option.elim x (a i) (fun j => a j)
  have hcomp :
      b ∘ (Equiv.optionSubtypeNe i).symm = a := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [b]
    · simp [b, Equiv.optionSubtypeNe_symm_of_ne hji]
  calc
    MvPolynomial.eval a P =
        MvPolynomial.eval b
          (MvPolynomial.rename
            (Equiv.optionSubtypeNe i).symm P) := by
      rw [MvPolynomial.eval_rename, hcomp]
    _ = Polynomial.eval (a i)
        (Polynomial.map
          (MvPolynomial.eval
            fun j : {j : σ // j ≠ i} => a j)
          (isolateVariable i P)) := by
      simpa [b, isolateVariable] using
        (MvPolynomial.optionEquivLeft_elim_eval
          (R := ℝ) (S₁ := {j : σ // j ≠ i})
          (fun j : {j : σ // j ≠ i} => a j) (a i)
          (MvPolynomial.rename
            (Equiv.optionSubtypeNe i).symm P))

/-- Eliminate `i` from two multivariate polynomials. The leading-coefficient
factor records the locus at which specialization lowers the degree of `P`. -/
noncomputable def eliminateVariable
    {σ : Type*} (i : σ)
    (P Q : MvPolynomial σ ℝ) :
    MvPolynomial {j : σ // j ≠ i} ℝ := by
  classical
  exact
    Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) *
      (isolateVariable i P).leadingCoeff

/-- A nonzero first polynomial and nonzero formal resultant give a nonzero
eliminant. -/
theorem eliminateVariable_ne_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ}
    (hP : P ≠ 0)
    (hresultant :
      Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) ≠ 0) :
    eliminateVariable i P Q ≠ 0 := by
  classical
  apply mul_ne_zero hresultant
  apply Polynomial.leadingCoeff_ne_zero.mpr
  exact (isolateVariable i).injective.ne hP

/-- Every common zero of `P` and `Q` descends to a zero of their eliminant
under the assignment with `i` removed. -/
theorem eval_eliminateVariable_eq_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ} (a : σ → ℝ)
    (hP : MvPolynomial.eval a P = 0)
    (hQ : MvPolynomial.eval a Q = 0) :
    MvPolynomial.eval
        (fun j : {j : σ // j ≠ i} => a j)
        (eliminateVariable i P Q) = 0 := by
  classical
  let f :=
    (isolateVariable i P).map
      (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
  let g :=
    (isolateVariable i Q).map
      (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
  have hfroot : f.eval (a i) = 0 := by
    rw [← eval_isolateVariable i P a]
    exact hP
  have hgroot : g.eval (a i) = 0 := by
    rw [← eval_isolateVariable i Q a]
    exact hQ
  by_cases hlead :
      MvPolynomial.eval
        (fun j : {j : σ // j ≠ i} => a j)
        (isolateVariable i P).leadingCoeff = 0
  · simp [eliminateVariable, hlead]
  · have hfne : f ≠ 0 := by
      intro hf
      apply hlead
      have hc : f.coeff (isolateVariable i P).natDegree = 0 := by
        rw [hf]
        simp
      simpa [f, Polynomial.coeff_map] using hc
    have hnotcop : ¬ IsCoprime f g := by
      intro hcop
      rcases Polynomial.aeval_ne_zero_of_isCoprime hcop (a i) with h | h
      · exact h (by simpa [Polynomial.aeval_def,
          Polynomial.eval₂_id] using hfroot)
      · exact h (by simpa [Polynomial.aeval_def,
          Polynomial.eval₂_id] using hgroot)
    have hm : f.natDegree ≤ (isolateVariable i P).natDegree := by
      exact Polynomial.natDegree_map_le
    have hn : g.natDegree ≤ (isolateVariable i Q).natDegree := by
      exact Polynomial.natDegree_map_le
    have hres :
        Polynomial.resultant f g
          (isolateVariable i P).natDegree
          (isolateVariable i Q).natDegree = 0 :=
      resultant_eq_zero_of_le_of_not_isCoprime
        hm hn (Or.inl hfne) hnotcop
    have hmap :
        Polynomial.resultant f g
            (isolateVariable i P).natDegree
            (isolateVariable i Q).natDegree =
          MvPolynomial.eval
            (fun j : {j : σ // j ≠ i} => a j)
            (Polynomial.resultant
              (isolateVariable i P)
              (isolateVariable i Q)) := by
      dsimp only [f, g]
      rw [Polynomial.resultant_map_map]
    rw [eliminateVariable, map_mul, ← hmap, hres, zero_mul]

end MultivariateElimination
end Math
