/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Math.Minimax.ShapleySnow
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Coupled discounted Shapley systems

This module gives a multivariate polynomial presentation of the value vector
of a finite coupled family of discounted matrix games. The variables are the
discount rate and one value coordinate per state.

For each state, the general bordered Shapley--Snow theorem selects a square
kernel at every rate. A finite product packages those rate-dependent kernels
into one fixed nonzero multivariate polynomial vanishing along the full value
vector.

The contraction-form entries

```
λ * reward + (1 - λ) * ∑ nextState, transitionWeight * value nextState
```

make candidate nondegeneracy automatic. The proof compares the
specializations `(λ, value) = (1/2, u)` and `(2/3, 2u)`; ordinary and bordered
determinants scale in adjacent degrees.

## Main declarations

* `discountedStochasticEntry`: the multivariate entry polynomial.
* `discountedStochastic_borderedKernelPoly_ne_zero`: automatic candidate
  nondegeneracy for positive-size bordered kernels.
* `exists_nonzero_mvPolynomial_of_discountedShapleySystem`: a fixed nonzero
  relation for any chosen state coordinate of a finite coupled system.
-/

open scoped BigOperators

namespace ShapleySnow

noncomputable def discountedStochasticEntry
    {κ I J : Type*} [Fintype κ]
    (r : I → J → ℝ)
    (T : I → J → κ → ℝ)
    (i : I) (j : J) :
    MvPolynomial (Option κ) ℝ :=
  MvPolynomial.X none * MvPolynomial.C (r i j) +
    (1 - MvPolynomial.X none) *
      ∑ z, MvPolynomial.C (T i j z) *
        MvPolynomial.X (some z)

@[simp]
theorem eval_discountedStochasticEntry
    {κ I J : Type*} [Fintype κ]
    (r : I → J → ℝ)
    (T : I → J → κ → ℝ)
    (i : I) (j : J)
    (a : Option κ → ℝ) :
    MvPolynomial.eval a
        (discountedStochasticEntry r T i j) =
      a none * r i j +
        (1 - a none) * ∑ z, T i j z * a (some z) := by
  simp [discountedStochasticEntry]

theorem discountedStochastic_borderedKernelPoly_ne_zero
    {κ I J : Type*} [Fintype κ]
    (r : I → J → ℝ)
    (T : I → J → κ → ℝ)
    (target : κ)
    {sz : ℕ} (hr : 0 < sz)
    (rows : Fin sz ↪ I) (cols : Fin sz ↪ J)
    (hborder :
      (borderedMatrix
        ((Matrix.of
          (discountedStochasticEntry r T)).submatrix rows cols)).det ≠ 0) :
    ((Matrix.of
      (discountedStochasticEntry r T)).submatrix rows cols).det -
        MvPolynomial.X (some target) *
          (borderedMatrix
            ((Matrix.of
              (discountedStochasticEntry r T)).submatrix rows cols)).det ≠ 0 := by
  classical
  let R : Matrix (Fin sz) (Fin sz) ℝ :=
    (Matrix.of r).submatrix rows cols
  let L (u : κ → ℝ) : Matrix (Fin sz) (Fin sz) ℝ :=
    fun i j => ∑ z, T (rows i) (cols j) z * u z
  let M (u : κ → ℝ) : Matrix (Fin sz) (Fin sz) ℝ :=
    R + L u
  let B :=
    (Matrix.of
      (discountedStochasticEntry r T)).submatrix rows cols
  let D : MvPolynomial (Option κ) ℝ :=
    (borderedMatrix B).det
  haveI : Nonempty (Fin sz) := ⟨⟨0, hr⟩⟩
  intro hzero
  have heval_matrix (a : Option κ → ℝ) :
      B.map (MvPolynomial.eval a) =
        a none • R + (1 - a none) •
          L (fun z => a (some z)) := by
    ext i j
    simp [B, R, L, Matrix.map_apply,
      Matrix.submatrix_apply, Finset.mul_sum]
  have hhalf (u : κ → ℝ) :
      (1 / 2 : ℝ) * (M u).det -
          u target * (borderedMatrix (M u)).det = 0 := by
    let a : Option κ → ℝ
      | none => 1 / 2
      | some z => u z
    have hmat : B.map (MvPolynomial.eval a) =
        (1 / 2 : ℝ) • M u := by
      rw [heval_matrix]
      ext i j
      simp [a, M, Matrix.add_apply, Matrix.smul_apply]
      ring
    have h := congrArg (MvPolynomial.eval a) hzero
    rw [map_zero, map_sub, map_mul, MvPolynomial.eval_X,
      RingHom.map_det, RingHom.mapMatrix_apply,
      RingHom.map_det, RingHom.mapMatrix_apply,
      map_borderedMatrix, hmat,
      Matrix.det_smul, Fintype.card_fin,
      borderedMatrix_det_smul (M u) (1 / 2 : ℝ) (by norm_num)] at h
    have hp : (1 / 2 : ℝ) ^ (sz - 1) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have hpow :
        (1 / 2 : ℝ) ^ sz =
          (1 / 2 : ℝ) ^ (sz - 1) * (1 / 2 : ℝ) := by
      calc
        (1 / 2 : ℝ) ^ sz =
            (1 / 2 : ℝ) ^ ((sz - 1) + 1) := by
              congr 1
              omega
        _ = (1 / 2 : ℝ) ^ (sz - 1) * (1 / 2 : ℝ) :=
          pow_succ _ _
    simp only [a] at h
    norm_num at h
    rw [hpow] at h
    apply (mul_left_cancel₀ hp)
    rw [mul_zero]
    nlinarith
  have hthird (u : κ → ℝ) :
      (2 / 3 : ℝ) * (M u).det -
          2 * u target * (borderedMatrix (M u)).det = 0 := by
    let a : Option κ → ℝ
      | none => 2 / 3
      | some z => 2 * u z
    have hmat : B.map (MvPolynomial.eval a) =
        (2 / 3 : ℝ) • M u := by
      rw [heval_matrix]
      ext i j
      change
        (2 / 3 : ℝ) * R i j +
            (1 - 2 / 3 : ℝ) *
              ∑ z, T (rows i) (cols j) z * (2 * u z) =
          (2 / 3 : ℝ) *
            (R i j + ∑ z, T (rows i) (cols j) z * u z)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    have h := congrArg (MvPolynomial.eval a) hzero
    rw [map_zero, map_sub, map_mul, MvPolynomial.eval_X,
      RingHom.map_det, RingHom.mapMatrix_apply,
      RingHom.map_det, RingHom.mapMatrix_apply,
      map_borderedMatrix, hmat,
      Matrix.det_smul, Fintype.card_fin,
      borderedMatrix_det_smul (M u) (2 / 3 : ℝ) (by norm_num)] at h
    have hp : (2 / 3 : ℝ) ^ (sz - 1) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have hpow :
        (2 / 3 : ℝ) ^ sz =
          (2 / 3 : ℝ) ^ (sz - 1) * (2 / 3 : ℝ) := by
      calc
        (2 / 3 : ℝ) ^ sz =
            (2 / 3 : ℝ) ^ ((sz - 1) + 1) := by
              congr 1
              omega
        _ = (2 / 3 : ℝ) ^ (sz - 1) * (2 / 3 : ℝ) :=
          pow_succ _ _
    simp only [a] at h
    norm_num at h
    rw [hpow] at h
    apply (mul_left_cancel₀ hp)
    rw [mul_zero]
    nlinarith
  have hDM (u : κ → ℝ) (hu : u target ≠ 0) :
      (borderedMatrix (M u)).det = 0 := by
    have h1 := hhalf u
    have h2 := hthird u
    have huv :
        u target * (borderedMatrix (M u)).det = 0 := by
      linarith
    exact (mul_eq_zero.mp huv).resolve_left hu
  apply hborder
  let s : Option κ → Set ℝ
    | none => ({0, 1} : Set ℝ)ᶜ
    | some z => if z = target then ({0} : Set ℝ)ᶜ else Set.univ
  apply MvPolynomial.funext_set s
  · intro x
    rcases x with _ | z
    · exact (Set.toFinite ({0, 1} : Set ℝ)).infinite_compl
    · by_cases hz : z = target
      · simpa [s, hz] using
          (Set.finite_singleton (0 : ℝ)).infinite_compl
      · simp [s, hz, Set.infinite_univ]
  · intro a ha
    have hc0 : a none ≠ 0 := by
      have := ha none (Set.mem_univ _)
      have hpair : a none ≠ 0 ∧ a none ≠ 1 := by
        simpa [s] using this
      exact hpair.1
    have hc1 : a none ≠ 1 := by
      have := ha none (Set.mem_univ _)
      have hpair : a none ≠ 0 ∧ a none ≠ 1 := by
        simpa [s] using this
      exact hpair.2
    have htarget : a (some target) ≠ 0 := by
      have := ha (some target) (Set.mem_univ _)
      simpa [s] using this
    let u : κ → ℝ := fun z =>
      (1 - a none) / a none * a (some z)
    have hu : u target ≠ 0 := by
      apply mul_ne_zero
      · exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hc1)) hc0
      · exact htarget
    have hmat :
        B.map (MvPolynomial.eval a) =
          a none • M u := by
      rw [heval_matrix]
      ext i j
      change
        a none * R i j +
            (1 - a none) *
              ∑ z, T (rows i) (cols j) z * a (some z) =
          a none *
            (R i j +
              ∑ z, T (rows i) (cols j) z *
                ((1 - a none) / a none * a (some z)))
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      field_simp
    change MvPolynomial.eval a D =
      MvPolynomial.eval a 0
    rw [map_zero]
    dsimp [D]
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      map_borderedMatrix, hmat,
      borderedMatrix_det_smul (M u) (a none) hc0,
      hDM u hu, mul_zero]

theorem exists_nonzero_mvPolynomial_of_forall_mem_exists
    {ι σ τ : Type*} [Finite ι]
    (F : ι → MvPolynomial σ ℝ)
    (S : Set τ) (assign : τ → σ → ℝ)
    (hcov : ∀ t ∈ S, ∃ k,
      F k ≠ 0 ∧ MvPolynomial.eval (assign t) (F k) = 0) :
    ∃ Q : MvPolynomial σ ℝ, Q ≠ 0 ∧
      ∀ t ∈ S, MvPolynomial.eval (assign t) Q = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∏ k, (if F k ≠ 0 then F k else 1), ?_,
    fun t ht => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _
    split_ifs with h
    · exact h
    · exact one_ne_zero
  · obtain ⟨k, hk0, hkeval⟩ := hcov t ht
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [if_pos hk0]
    exact hkeval

/-- A square kernel size, bounded by the row cardinality, together with its
row and column embeddings into arbitrary finite action types. -/
def ActionKernelShape (I J : Type*) [Fintype I] : Type _ :=
  Σ sz : Fin (Fintype.card I + 1),
    (Fin sz.val ↪ I) × (Fin sz.val ↪ J)

noncomputable instance instFiniteActionKernelShape
    (I J : Type*) [Fintype I] [Finite J] :
    Finite (ActionKernelShape I J) := by
  letI : Fintype J := Fintype.ofFinite J
  unfold ActionKernelShape
  infer_instance

/-- The bordered-kernel candidate associated to a kernel shape in an
arbitrary finite action matrix. -/
noncomputable def mvBorderedKernelPoly
    {σ I J : Type*} [Fintype I]
    (E : I → J → MvPolynomial σ ℝ)
    (target : σ) :
    ActionKernelShape I J → MvPolynomial σ ℝ :=
  fun ⟨_sz, rows, cols⟩ =>
    let B := (Matrix.of E).submatrix rows cols
    B.det - MvPolynomial.X target * (borderedMatrix B).det

theorem exists_nonzero_mvPolynomial_of_discountedShapleySystem
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (w : ℝ → κ → ℝ)
    (S : Set ℝ)
    (hw : ∀ l ∈ S, ∀ s,
      w l s =
        MinimaxLoomis.lam0
          (fun i j =>
            l * r s i j +
              (1 - l) * ∑ z, T s i j z * w l z))
    (target : κ) :
    ∃ Q : MvPolynomial (Option κ) ℝ, Q ≠ 0 ∧
      ∀ l ∈ S,
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l)) Q = 0 := by
  apply exists_nonzero_mvPolynomial_of_forall_mem_exists
    (mvBorderedKernelPoly
      (discountedStochasticEntry (r target) (T target))
      (some target))
    S (fun l x => Option.casesOn x l (w l))
  intro l hl
  let A : Matrix I J ℝ :=
    fun i j =>
      l * r target i j +
        (1 - l) * ∑ z, T target i j z * w l z
  obtain ⟨sz, hsz, rows, cols, hborder, hvalue⟩ :=
    exists_bordered_kernel A
  have hszm : sz ≤ Fintype.card I := by
    have := Fintype.card_le_of_embedding rows
    simpa using this
  let a : Option κ → ℝ :=
    fun x => Option.casesOn x l (w l)
  have hmap :
      ((Matrix.of
        (discountedStochasticEntry
          (r target) (T target))).submatrix rows cols).map
          (MvPolynomial.eval a) =
        A.submatrix rows cols := by
    ext i j
    simp [a, A, Matrix.map_apply, Matrix.submatrix_apply]
  refine ⟨⟨⟨sz, by omega⟩, rows, cols⟩, ?_, ?_⟩
  · exact discountedStochastic_borderedKernelPoly_ne_zero
      (r target) (T target) target hsz rows cols (by
        intro hz
        apply hborder
        have heval := congrArg (MvPolynomial.eval a) hz
        rw [map_zero, RingHom.map_det,
          RingHom.mapMatrix_apply, map_borderedMatrix,
          hmap] at heval
        exact heval)
  · change MvPolynomial.eval a
      (mvBorderedKernelPoly
        (discountedStochasticEntry
          (r target) (T target))
        (some target)
        ⟨⟨sz, by omega⟩, rows, cols⟩) = 0
    unfold mvBorderedKernelPoly
    simp only [map_sub, map_mul, MvPolynomial.eval_X,
      RingHom.map_det, RingHom.mapMatrix_apply,
      map_borderedMatrix, hmap]
    have hw' : MinimaxLoomis.lam0 A = w l target := by
      exact (hw l hl target).symm
    rw [hw'] at hvalue
    exact sub_eq_zero.mpr hvalue.symm

end ShapleySnow
