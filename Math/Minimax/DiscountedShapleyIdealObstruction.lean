/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Minimax.DiscountedShapleySystem

open scoped BigOperators

/-!
# A positive-dimensional component in the raw Shapley kernel ideal

The statewise kernel products encode a union of local kernel branches. This
module gives a two-state, two-action obstruction to proving that their raw
coupled ideal is always zero-dimensional.

Rows have rewards `0` and `1`, independently of the column. The column
deterministically chooses the next state. For the full two-by-two kernel, the
bordered determinant vanishes while the ordinary determinant is

```
λ * (1 - λ) * (v₀ - v₁).
```

Consequently, this same factor divides both statewise product equations.
After extending coefficients from `ℝ[λ]` to `ℝ(λ)`, the parameter factor is a
unit and the coupled ideal is contained in the diagonal hypersurface ideal
`⟨v₀ - v₁⟩`. Its quotient retains a free polynomial coordinate and is not
finite-dimensional.

This rules out the raw product ideal as a universal zero-dimensional
elimination object. A complete arbitrary-state elimination argument must
select branches or saturate away components while retaining every actual
discounted Shapley assignment.

## Main declarations

* `diagonalKernel_candidate`: the full local kernel factor.
* `map_diagonalKernelSystemIdeal_le_diagonal`: the extended coupled ideal is
  contained in the diagonal hypersurface ideal.
* `diagonalKernelSystemIdeal_not_moduleFinite`: the raw coupled quotient is
  not finite-dimensional over `ℝ(λ)`.
-/

namespace ShapleySnow

noncomputable section

def diagonalKernelReward :
    Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun _ i _ => if i = 1 then 1 else 0

def diagonalKernelTransition :
    Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun _ _ j z => if z = j then 1 else 0

def fullTwoKernelShape :
    ActionKernelShape (Fin 2) (Fin 2) :=
  ⟨⟨2, by decide⟩,
    Function.Embedding.refl (Fin 2),
    Function.Embedding.refl (Fin 2)⟩

theorem diagonalKernel_matrix
    (s : Fin 2) :
    (Matrix.of
      (discountedStochasticEntry
        (diagonalKernelReward s)
        (diagonalKernelTransition s))) =
      !![
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (0 : Fin 2)),
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (1 : Fin 2));
        MvPolynomial.X none +
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (0 : Fin 2)),
        MvPolynomial.X none +
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (1 : Fin 2))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalKernelReward, diagonalKernelTransition,
      discountedStochasticEntry]

theorem diagonalKernel_bordered_det_eq_zero
    (s : Fin 2) :
    let B :=
      (Matrix.of
        (discountedStochasticEntry
          (diagonalKernelReward s)
          (diagonalKernelTransition s)))
    (borderedMatrix B).det = 0 := by
  classical
  dsimp only
  let B :
      Matrix (Fin 2) (Fin 2)
        (MvPolynomial (Option (Fin 2)) ℝ) :=
    (Matrix.of
      (discountedStochasticEntry
        (diagonalKernelReward s)
        (diagonalKernelTransition s)))
  let C := borderedMatrix B
  let c0 : Sum (Fin 2) Unit := Sum.inl 0
  let c1 : Sum (Fin 2) Unit := Sum.inl 1
  let cb : Sum (Fin 2) Unit := Sum.inr ()
  have hc1b : c1 ≠ cb := by simp [c1, cb]
  have hc10 : c1 ≠ c0 := by simp [c1, c0]
  let C' := C.updateCol c1
    (fun k => C k c1 + MvPolynomial.X none * C k cb)
  have hdet : C'.det = C.det := by
    exact Matrix.det_updateCol_add_smul_self C hc1b
      (MvPolynomial.X none)
  have hcols : ∀ k, C' k c1 = C' k c0 := by
    intro k
    rcases k with k | k
    · fin_cases k <;>
        simp [C', C, c0, c1, cb, borderedMatrix, B,
          diagonalKernel_matrix]
    · rcases k with ⟨⟩
      simp [C', C, c0, c1, cb, borderedMatrix]
  have hz : C'.det = 0 :=
    Matrix.det_zero_of_column_eq hc10 hcols
  rw [hdet] at hz
  exact hz

theorem diagonalKernel_candidate
    (s target : Fin 2) :
    mvBorderedKernelPoly
        (discountedStochasticEntry
          (diagonalKernelReward s)
          (diagonalKernelTransition s))
        (some target) fullTwoKernelShape =
      MvPolynomial.X none *
        (1 - MvPolynomial.X none) *
          (MvPolynomial.X (some (0 : Fin 2)) -
            MvPolynomial.X (some (1 : Fin 2))) := by
  simp only [mvBorderedKernelPoly, fullTwoKernelShape]
  change
    (Matrix.of
      (discountedStochasticEntry
        (diagonalKernelReward s)
        (diagonalKernelTransition s))).det -
      MvPolynomial.X (some target) *
        (borderedMatrix
          (Matrix.of
            (discountedStochasticEntry
              (diagonalKernelReward s)
              (diagonalKernelTransition s)))).det =
    _
  have hborder :
      (borderedMatrix
        (Matrix.of
          (discountedStochasticEntry
            (diagonalKernelReward s)
            (diagonalKernelTransition s)))).det = 0 := by
    simpa using diagonalKernel_bordered_det_eq_zero s
  rw [hborder]
  simp only [mul_zero, sub_zero]
  have hmatrix :
      Matrix.of
          (discountedStochasticEntry
            (diagonalKernelReward s)
            (diagonalKernelTransition s)) =
        !![
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (0 : Fin 2)),
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (1 : Fin 2));
          MvPolynomial.X none +
            (1 - MvPolynomial.X none) *
              MvPolynomial.X (some (0 : Fin 2)),
          MvPolynomial.X none +
            (1 - MvPolynomial.X none) *
              MvPolynomial.X (some (1 : Fin 2))] := by
    simpa using diagonalKernel_matrix s
  rw [hmatrix]
  simp [Matrix.det_fin_two]
  ring

def diagonalKernelFactor :
    MvPolynomial (Fin 2) (Polynomial ℝ) :=
  MvPolynomial.C
      (Polynomial.X * (1 - Polynomial.X)) *
    (MvPolynomial.X 0 - MvPolynomial.X 1)

theorem optionEquivRight_diagonalKernel_candidate
    (s target : Fin 2) :
    MvPolynomial.optionEquivRight ℝ (Fin 2)
        (mvBorderedKernelPoly
          (discountedStochasticEntry
            (diagonalKernelReward s)
            (diagonalKernelTransition s))
          (some target) fullTwoKernelShape) =
      diagonalKernelFactor := by
  rw [diagonalKernel_candidate]
  simp [diagonalKernelFactor]

theorem diagonalKernelFactor_ne_zero :
    diagonalKernelFactor ≠ 0 := by
  intro hzero
  have hvalues := congrArg
    (MvPolynomial.eval fun z : Fin 2 =>
      if z = 0 then (1 : Polynomial ℝ) else 0) hzero
  have hrate := congrArg (Polynomial.eval (1 / 2 : ℝ)) hvalues
  norm_num [diagonalKernelFactor] at hrate

theorem diagonalKernel_candidate_ne_zero
    (s target : Fin 2) :
    mvBorderedKernelPoly
        (discountedStochasticEntry
          (diagonalKernelReward s)
          (diagonalKernelTransition s))
        (some target) fullTwoKernelShape ≠ 0 := by
  intro hzero
  apply diagonalKernelFactor_ne_zero
  rw [← optionEquivRight_diagonalKernel_candidate s target,
    hzero, map_zero]

theorem diagonalKernelSystemIdeal_le_factor :
    discountedShapleySystemIdeal
        diagonalKernelReward diagonalKernelTransition ≤
      Ideal.span {diagonalKernelFactor} := by
  apply discountedShapleySystemIdeal_le_span_of_common_kernelFactor
  intro s
  exact ⟨fullTwoKernelShape,
    diagonalKernel_candidate_ne_zero s s,
    optionEquivRight_diagonalKernel_candidate s s⟩

theorem map_diagonalKernelSystemIdeal_le_diagonal :
    let A := Polynomial ℝ
    let K := FractionRing A
    let φ : MvPolynomial (Fin 2) A →+*
        MvPolynomial (Fin 2) K :=
      MvPolynomial.map (algebraMap A K)
    (discountedShapleySystemIdeal
      diagonalKernelReward diagonalKernelTransition).map φ ≤
        Ideal.span {
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) -
            MvPolynomial.X 1} := by
  dsimp only
  let φ : MvPolynomial (Fin 2) (Polynomial ℝ) →+*
      MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ)) :=
    MvPolynomial.map
      (algebraMap (Polynomial ℝ)
        (FractionRing (Polynomial ℝ)))
  let H :
      MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ)) :=
    (MvPolynomial.X 0 :
      MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ))) -
      MvPolynomial.X 1
  calc
    (discountedShapleySystemIdeal
        diagonalKernelReward diagonalKernelTransition).map φ ≤
        (Ideal.span {diagonalKernelFactor}).map φ :=
      Ideal.map_mono diagonalKernelSystemIdeal_le_factor
    _ = Ideal.span {φ diagonalKernelFactor} := by
      rw [Ideal.map_span]
      congr 1
      ext P
      simp
    _ ≤ Ideal.span {H} := by
      rw [Ideal.span_le]
      rintro P ⟨hP | hP, rfl⟩
      · apply Ideal.mem_span_singleton.mpr
        refine ⟨MvPolynomial.C
          (algebraMap (Polynomial ℝ)
            (FractionRing (Polynomial ℝ))
            (Polynomial.X * (1 - Polynomial.X))), ?_⟩
        simp [φ, diagonalKernelFactor, H]
        ring

theorem diagonalKernelSystemIdeal_not_moduleFinite :
    let A := Polynomial ℝ
    let K := FractionRing A
    ¬ Module.Finite K
      (MvPolynomial (Fin 2) K ⧸
        (discountedShapleySystemIdeal
          diagonalKernelReward diagonalKernelTransition).map
            (MvPolynomial.map (algebraMap A K))) := by
  dsimp only
  exact
    Math.MultivariateElimination.not_moduleFinite_quotient_of_le_span_X_sub_X
      ((discountedShapleySystemIdeal
        diagonalKernelReward diagonalKernelTransition).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))
      0 1
      map_diagonalKernelSystemIdeal_le_diagonal

end

end ShapleySnow
