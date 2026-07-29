/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Minimax.DiscountedShapleySystem

open scoped BigOperators

/-!
# Positive-dimensional components in Shapley kernel ideals

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

A second system shows that merely requiring the bordered denominator to be a
nonzero formal polynomial is not sufficient. With zero rewards, matching
actions send the process to state `1` and mismatching actions send it to state
`0`. The full two-by-two kernel is denominator-active, but its equation at
both states contains `v₁ - v₀`. The corresponding all-active fixed branch
therefore still has a positive-dimensional diagonal component. A universal
branch theorem must saturate by the bordered denominators or otherwise retain
only components on which the selected denominators do not vanish.

## Main declarations

* `diagonalKernel_candidate`: the full local kernel factor.
* `map_diagonalKernelSystemIdeal_le_diagonal`: the extended coupled ideal is
  contained in the diagonal hypersurface ideal.
* `diagonalKernelSystemIdeal_not_moduleFinite`: the raw coupled quotient is
  not finite-dimensional over `ℝ(λ)`.
* `activeBranchObstructionBranchIdeal_not_moduleFinite`: even an all-active
  fixed branch can have a positive-dimensional quotient.
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

/-- The full two-by-two shape responsible for the diagonal component is not
denominator-active and is therefore absent from the active-kernel product. -/
theorem diagonalKernel_fullTwo_not_active
    (s : Fin 2) :
    ¬ IsActiveKernelShape
      (discountedStochasticEntry
        (diagonalKernelReward s)
        (diagonalKernelTransition s))
      fullTwoKernelShape := by
  intro hactive
  apply hactive.2
  change
    (borderedMatrix
      ((Matrix.of
        (discountedStochasticEntry
          (diagonalKernelReward s)
          (diagonalKernelTransition s))).submatrix
            (Function.Embedding.refl (Fin 2))
            (Function.Embedding.refl (Fin 2)))).det = 0
  rw [show
    (Matrix.of
      (discountedStochasticEntry
        (diagonalKernelReward s)
        (diagonalKernelTransition s))).submatrix
          (Function.Embedding.refl (Fin 2))
          (Function.Embedding.refl (Fin 2)) =
      Matrix.of
        (discountedStochasticEntry
          (diagonalKernelReward s)
          (diagonalKernelTransition s)) by
    ext i j
    rfl]
  exact diagonalKernel_bordered_det_eq_zero s

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

/-! ### A denominator-active fixed branch with a diagonal component -/

def activeBranchObstructionReward :
    Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun _ _ _ => 0

def activeBranchObstructionTransition :
    Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun _ i j z =>
    if z = (if i = j then 1 else 0) then 1 else 0

theorem activeBranchObstruction_matrix
    (s : Fin 2) :
    Matrix.of
      (discountedStochasticEntry
        (activeBranchObstructionReward s)
        (activeBranchObstructionTransition s)) =
      !![
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (1 : Fin 2)),
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (0 : Fin 2));
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (0 : Fin 2)),
        (1 - MvPolynomial.X none) *
          MvPolynomial.X (some (1 : Fin 2))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [activeBranchObstructionReward,
      activeBranchObstructionTransition,
      discountedStochasticEntry]

theorem activeBranchObstruction_bordered_det
    (s : Fin 2) :
    (borderedMatrix
      (Matrix.of
        (discountedStochasticEntry
          (activeBranchObstructionReward s)
          (activeBranchObstructionTransition s)))).det =
      2 * (1 - MvPolynomial.X none) *
        (MvPolynomial.X (some (1 : Fin 2)) -
          MvPolynomial.X (some (0 : Fin 2))) := by
  let e : Sum (Fin 2) Unit ≃ Fin 3 := {
    toFun := Sum.elim
      (fun i => Fin.cases 0 (fun _ => 1) i)
      (fun _ => 2)
    invFun := fun i =>
      Fin.cases (Sum.inl 0)
        (fun j => Fin.cases (Sum.inl 1)
          (fun _ => Sum.inr ()) j) i
    left_inv := by
      intro x
      rcases x with i | ⟨⟩
      · fin_cases i <;> rfl
      · rfl
    right_inv := by
      intro i
      fin_cases i <;> rfl }
  have he0 : e.symm (0 : Fin 3) = Sum.inl 0 := by
    decide
  have he1 : e.symm (1 : Fin 3) = Sum.inl 1 := by
    decide
  have he2 : e.symm (2 : Fin 3) = Sum.inr () := by
    decide
  rw [← Matrix.det_reindex_self e]
  have hmatrix :
      Matrix.reindex e e
        (borderedMatrix
          (Matrix.of
            (discountedStochasticEntry
              (activeBranchObstructionReward s)
              (activeBranchObstructionTransition s)))) =
        !![
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (1 : Fin 2)),
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (0 : Fin 2)),
          -1;
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (0 : Fin 2)),
          (1 - MvPolynomial.X none) *
            MvPolynomial.X (some (1 : Fin 2)),
          -1;
          1, 1, 0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindex_apply, he0, he1, he2, borderedMatrix,
        activeBranchObstruction_matrix]
  rw [hmatrix]
  rw [Matrix.det_fin_three]
  let p : MvPolynomial (Option (Fin 2)) ℝ :=
    (1 - MvPolynomial.X none) *
      MvPolynomial.X (some (1 : Fin 2))
  let q : MvPolynomial (Option (Fin 2)) ℝ :=
    (1 - MvPolynomial.X none) *
      MvPolynomial.X (some (0 : Fin 2))
  change
    p * p * 0 - p * (-1) * 1 -
      q * q * 0 + q * (-1) * 1 +
      (-1) * q * 1 - (-1) * p * 1 = _
  dsimp [p, q]
  ring

theorem activeBranchObstruction_candidate
    (s target : Fin 2) :
    mvBorderedKernelPoly
        (discountedStochasticEntry
          (activeBranchObstructionReward s)
          (activeBranchObstructionTransition s))
        (some target) fullTwoKernelShape =
      (1 - MvPolynomial.X none) *
        (MvPolynomial.X (some (1 : Fin 2)) -
          MvPolynomial.X (some (0 : Fin 2))) *
        ((1 - MvPolynomial.X none) *
          (MvPolynomial.X (some (1 : Fin 2)) +
            MvPolynomial.X (some (0 : Fin 2))) -
          2 * MvPolynomial.X (some target)) := by
  simp only [mvBorderedKernelPoly, fullTwoKernelShape]
  change
    (Matrix.of
      (discountedStochasticEntry
        (activeBranchObstructionReward s)
        (activeBranchObstructionTransition s))).det -
      MvPolynomial.X (some target) *
        (borderedMatrix
          (Matrix.of
            (discountedStochasticEntry
              (activeBranchObstructionReward s)
              (activeBranchObstructionTransition s)))).det =
      _
  rw [activeBranchObstruction_bordered_det,
    activeBranchObstruction_matrix, Matrix.det_fin_two]
  let p : MvPolynomial (Option (Fin 2)) ℝ :=
    (1 - MvPolynomial.X none) *
      MvPolynomial.X (some (1 : Fin 2))
  let q : MvPolynomial (Option (Fin 2)) ℝ :=
    (1 - MvPolynomial.X none) *
      MvPolynomial.X (some (0 : Fin 2))
  change
    p * p - q * q -
      MvPolynomial.X (some target) *
        (2 * (1 - MvPolynomial.X none) *
          (MvPolynomial.X (some (1 : Fin 2)) -
            MvPolynomial.X (some (0 : Fin 2)))) = _
  dsimp [p, q]
  ring

theorem activeBranchObstruction_fullTwo_active
    (s : Fin 2) :
    IsActiveKernelShape
      (discountedStochasticEntry
        (activeBranchObstructionReward s)
        (activeBranchObstructionTransition s))
      fullTwoKernelShape := by
  constructor
  · simp [fullTwoKernelShape]
  · change
      (borderedMatrix
        ((Matrix.of
          (discountedStochasticEntry
            (activeBranchObstructionReward s)
            (activeBranchObstructionTransition s))).submatrix
              (Function.Embedding.refl (Fin 2))
              (Function.Embedding.refl (Fin 2)))).det ≠ 0
    rw [show
      (Matrix.of
        (discountedStochasticEntry
          (activeBranchObstructionReward s)
          (activeBranchObstructionTransition s))).submatrix
            (Function.Embedding.refl (Fin 2))
            (Function.Embedding.refl (Fin 2)) =
        Matrix.of
          (discountedStochasticEntry
            (activeBranchObstructionReward s)
            (activeBranchObstructionTransition s)) by
      apply Matrix.ext
      intro i j
      rfl]
    rw [activeBranchObstruction_bordered_det]
    intro hzero
    have h :=
      congrArg
        (MvPolynomial.eval fun x : Option (Fin 2) =>
          Option.casesOn x 0
            (fun z => if z = 1 then (1 : ℝ) else 0))
        hzero
    norm_num at h

def activeBranchObstructionBranch :
    Fin 2 → ActionKernelShape (Fin 2) (Fin 2) :=
  fun _ => fullTwoKernelShape

theorem activeBranchObstruction_kernelPoly_dvd_diagonal
    (s : Fin 2) :
    (MvPolynomial.X 1 - MvPolynomial.X 0 :
      MvPolynomial (Fin 2) (Polynomial ℝ)) ∣
      discountedShapleyActiveKernelPoly
        activeBranchObstructionReward
        activeBranchObstructionTransition
        s fullTwoKernelShape := by
  rw [discountedShapleyActiveKernelPoly,
    if_pos (activeBranchObstruction_fullTwo_active s),
    activeBranchObstruction_candidate]
  refine
    ⟨MvPolynomial.optionEquivRight ℝ (Fin 2)
      ((1 - MvPolynomial.X none) *
        ((1 - MvPolynomial.X none) *
          (MvPolynomial.X (some (1 : Fin 2)) +
            MvPolynomial.X (some (0 : Fin 2))) -
          2 * MvPolynomial.X (some s))), ?_⟩
  simp only [map_mul, map_sub, map_add,
    MvPolynomial.optionEquivRight_X_some]
  ring

theorem localized_activeBranchObstruction_kernelPoly_dvd_diagonal
    (s : Fin 2) :
    (MvPolynomial.X 1 - MvPolynomial.X 0 :
      MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ))) ∣
      localizedDiscountedShapleyActiveKernelPoly
        activeBranchObstructionReward
        activeBranchObstructionTransition
        s fullTwoKernelShape := by
  obtain ⟨Q, hQ⟩ :=
    activeBranchObstruction_kernelPoly_dvd_diagonal s
  refine
    ⟨MvPolynomial.map
      (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ))) Q, ?_⟩
  rw [localizedDiscountedShapleyActiveKernelPoly, hQ, map_mul]
  simp

theorem activeBranchObstructionBranchIdeal_le_diagonal :
    discountedShapleyActiveBranchIdeal
        activeBranchObstructionReward
        activeBranchObstructionTransition
        activeBranchObstructionBranch ≤
      Ideal.span {
        (MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ))) -
          MvPolynomial.X 0} := by
  rw [discountedShapleyActiveBranchIdeal, Ideal.span_le]
  rintro P ⟨s, rfl⟩
  apply Ideal.mem_span_singleton.mpr
  exact localized_activeBranchObstruction_kernelPoly_dvd_diagonal s

theorem activeBranchObstructionBranch_all_active :
    ∀ s, IsActiveKernelShape
      (discountedStochasticEntry
        (activeBranchObstructionReward s)
        (activeBranchObstructionTransition s))
      (activeBranchObstructionBranch s) := by
  intro s
  exact activeBranchObstruction_fullTwo_active s

theorem activeBranchObstructionBranchIdeal_not_moduleFinite :
    ¬ Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial (Fin 2) (FractionRing (Polynomial ℝ)) ⧸
        discountedShapleyActiveBranchIdeal
          activeBranchObstructionReward
          activeBranchObstructionTransition
          activeBranchObstructionBranch) := by
  exact
    Math.MultivariateElimination.not_moduleFinite_quotient_of_le_span_X_sub_X
      (discountedShapleyActiveBranchIdeal
        activeBranchObstructionReward
        activeBranchObstructionTransition
        activeBranchObstructionBranch)
      1 0
      activeBranchObstructionBranchIdeal_le_diagonal

end

end ShapleySnow
