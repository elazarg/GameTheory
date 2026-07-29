/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Math.Minimax.ShapleySnow
import Math.MultivariateElimination
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
* `discountedShapleySystemIdeal`: the coupled kernel equations with the rate
  moved into the coefficient ring.
* `exists_nonzero_bivariateRelation_of_discountedShapleySystemIdeal_moduleFinite`:
  zero-dimensionality of the coupled kernel ideal gives a fixed bivariate
  coordinate relation.
* `discountedShapleySystem_twoState_kernelPair_elimination_dichotomy`:
  pairwise resultant elimination for a two-state coupled system, with a
  specific local-kernel degeneracy certificate.
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

/-- At every parameter, a coupled Shapley equation selects a nonzero local
bordered-kernel candidate that vanishes at the full value assignment. -/
theorem exists_nonzero_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
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
    (target : κ) {l : ℝ} (hl : l ∈ S) :
    ∃ k : ActionKernelShape I J,
      mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k ≠ 0 ∧
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r target) (T target))
            (some target) k) = 0 := by
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

/-- A finite product of local kernel candidates gives one fixed nonzero
multivariate relation along a coupled discounted Shapley value vector. -/
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
  exact
    exists_nonzero_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
      r T w S hw target hl

/-- Evaluation commutes with moving the `none` variable into the univariate
coefficient ring. -/
theorem eval₂_optionEquivRight
    {κ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (v : κ → S)
    (l : S) (P : MvPolynomial (Option κ) R) :
    MvPolynomial.eval₂ (Polynomial.eval₂RingHom φ l) v
        (MvPolynomial.optionEquivRight R κ P) =
      MvPolynomial.eval₂ φ
        (fun x => Option.casesOn x l v) P := by
  let f : MvPolynomial (Option κ) R →+* S :=
    (MvPolynomial.eval₂Hom
      (Polynomial.eval₂RingHom φ l) v).comp
        (MvPolynomial.optionEquivRight R κ).toRingHom
  let g : MvPolynomial (Option κ) R →+* S :=
    MvPolynomial.eval₂Hom φ
      (fun x => Option.casesOn x l v)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, g]
    · intro x
      cases x with
      | none =>
          simp [f, g]
      | some s =>
          simp [f, g]
  exact RingHom.congr_fun hfg P

/-- Evaluating a univariate polynomial at one multivariate coordinate and then
evaluating all coordinates is the corresponding ordinary univariate
evaluation. -/
theorem eval₂_polynomial_aeval_X
    {κ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (v : κ → S)
    (target : κ) (q : Polynomial R) :
    MvPolynomial.eval₂ φ v
        (Polynomial.aeval (MvPolynomial.X target) q) =
      Polynomial.eval₂ φ (v target) q := by
  have hcomp :
      (MvPolynomial.eval₂Hom φ v).comp
          (algebraMap R (MvPolynomial κ R)) = φ := by
    ext r
    simp
  have h :=
    Polynomial.hom_eval₂
      q (algebraMap R (MvPolynomial κ R))
      (MvPolynomial.eval₂Hom φ v)
      (MvPolynomial.X target)
  rw [hcomp] at h
  simpa [Polynomial.aeval_def] using h

/-- The product of all nonzero local bordered-kernel candidates for one
state. -/
noncomputable def discountedShapleyCoordinatePoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) :
    MvPolynomial (Option κ) ℝ := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  exact
    ∏ k,
      if mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k ≠ 0 then
        mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k
      else 1

theorem discountedShapleyCoordinatePoly_ne_zero
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) :
    discountedShapleyCoordinatePoly r T target ≠ 0 := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  rw [discountedShapleyCoordinatePoly, Finset.prod_ne_zero_iff]
  intro k _
  split_ifs with hk
  · exact hk
  · exact one_ne_zero

/-- Every nonzero local kernel candidate divides its state's fixed product
relation. -/
theorem mvBorderedKernelPoly_dvd_discountedShapleyCoordinatePoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) (k : ActionKernelShape I J)
    (hk : mvBorderedKernelPoly
      (discountedStochasticEntry (r target) (T target))
      (some target) k ≠ 0) :
    mvBorderedKernelPoly
        (discountedStochasticEntry (r target) (T target))
        (some target) k ∣
      discountedShapleyCoordinatePoly r T target := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  let F : ActionKernelShape I J →
      MvPolynomial (Option κ) ℝ :=
    fun k =>
      if mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k ≠ 0 then
        mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k
      else 1
  have hdvd := Finset.dvd_prod_of_mem F (Finset.mem_univ k)
  simpa [discountedShapleyCoordinatePoly, F, hk] using hdvd

theorem eval_discountedShapleyCoordinatePoly_eq_zero
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
    (target : κ) {l : ℝ} (hl : l ∈ S) :
    MvPolynomial.eval
        (fun x => Option.casesOn x l (w l))
        (discountedShapleyCoordinatePoly r T target) = 0 := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  obtain ⟨k, hk, hkeval⟩ :=
    exists_nonzero_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
      r T w S hw target hl
  rw [discountedShapleyCoordinatePoly, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [if_pos hk]
  exact hkeval

/-- The coupled bordered-kernel ideal with the rate moved into the coefficient
ring `ℝ[λ]` and only value coordinates retained as variables. -/
noncomputable def discountedShapleySystemIdeal
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ) :
    Ideal (MvPolynomial κ (Polynomial ℝ)) :=
  Ideal.span
    (Set.range fun s =>
      MvPolynomial.optionEquivRight ℝ κ
        (discountedShapleyCoordinatePoly r T s))

/-- A nonzero local kernel factor common to every statewise product contains
the entire coupled system ideal in its principal ideal. -/
theorem discountedShapleySystemIdeal_le_span_of_common_kernelFactor
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (H : MvPolynomial κ (Polynomial ℝ))
    (hcommon : ∀ s, ∃ k : ActionKernelShape I J,
      mvBorderedKernelPoly
          (discountedStochasticEntry (r s) (T s))
          (some s) k ≠ 0 ∧
        MvPolynomial.optionEquivRight ℝ κ
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r s) (T s))
            (some s) k) = H) :
    discountedShapleySystemIdeal r T ≤ Ideal.span {H} := by
  rw [discountedShapleySystemIdeal, Ideal.span_le]
  rintro P ⟨s, rfl⟩
  obtain ⟨k, hk, hmap⟩ := hcommon s
  change MvPolynomial.optionEquivRight ℝ κ
      (discountedShapleyCoordinatePoly r T s) ∈
    Ideal.span {H}
  rw [Ideal.mem_span_singleton]
  rw [← hmap]
  exact map_dvd (MvPolynomial.optionEquivRight ℝ κ)
    (mvBorderedKernelPoly_dvd_discountedShapleyCoordinatePoly
      r T s k hk)

/-- Every coupled Shapley value assignment annihilates the coupled
bordered-kernel ideal after specializing the rate coefficient. -/
theorem eval₂_mem_discountedShapleySystemIdeal_eq_zero
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
    {P : MvPolynomial κ (Polynomial ℝ)}
    (hP : P ∈ discountedShapleySystemIdeal r T)
    {l : ℝ} (hl : l ∈ S) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l) P = 0 := by
  have hle : discountedShapleySystemIdeal r T ≤
      RingHom.ker (MvPolynomial.eval₂Hom
        (Polynomial.evalRingHom l) (w l)) := by
    rw [discountedShapleySystemIdeal, Ideal.span_le]
    rintro P ⟨s, rfl⟩
    change MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
      (MvPolynomial.optionEquivRight ℝ κ
        (discountedShapleyCoordinatePoly r T s)) = 0
    calc
      _ = MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (discountedShapleyCoordinatePoly r T s) := by
        simpa [Polynomial.evalRingHom] using
          (eval₂_optionEquivRight (RingHom.id ℝ) (w l) l
            (discountedShapleyCoordinatePoly r T s))
      _ = 0 :=
        eval_discountedShapleyCoordinatePoly_eq_zero
          r T w S hw s hl
  exact hle hP

/-- If the coupled bordered-kernel ideal becomes zero-dimensional over
`ℝ(λ)`, every chosen value coordinate satisfies a fixed nonzero bivariate
relation in the rate and that coordinate. -/
theorem exists_nonzero_bivariateRelation_of_discountedShapleySystemIdeal_moduleFinite
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
    [Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial κ (FractionRing (Polynomial ℝ)) ⧸
        (discountedShapleySystemIdeal r T).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))]
    (target : κ) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ S,
        Polynomial.eval (w l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  obtain ⟨R, hR, hRmem⟩ :=
    Math.MultivariateElimination.exists_nonzero_coordinateRelation_mem_of_moduleFinite_fractionRing
      (discountedShapleySystemIdeal r T) target
  refine ⟨R, hR, fun l hl => ?_⟩
  have hz :=
    eval₂_mem_discountedShapleySystemIdeal_eq_zero
      r T w S hw hRmem hl
  rw [eval₂_polynomial_aeval_X] at hz
  simpa [Polynomial.eval₂_eq_eval_map] using hz

/-- After eliminating one state coordinate from a two-state system, the
remaining variables are canonically the rate and the target value. -/
noncomputable def twoStateRemainingEquiv
    {κ : Type*} (target other : κ)
    (hne : target ≠ other)
    (hcover : ∀ z : κ, z = target ∨ z = other) :
    {x : Option κ // x ≠ some other} ≃ Option Unit where
  toFun x :=
    match x.1 with
    | none => some ()
    | some _ => none
  invFun x :=
    match x with
    | none => ⟨some target, by simpa using hne⟩
    | some _ => ⟨none, by simp⟩
  left_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    cases x with
    | none => rfl
    | some z =>
        simp only
        rcases hcover z with hzt | hzo
        · simp [hzt]
        · subst z
          exact False.elim (hx rfl)
  right_inv := by
    intro x
    cases x <;> rfl

@[simp]
theorem twoStateRemainingEquiv_symm_none
    {κ : Type*} (target other : κ)
    (hne : target ≠ other)
    (hcover : ∀ z : κ, z = target ∨ z = other) :
    (twoStateRemainingEquiv target other hne hcover).symm none =
      ⟨some target, by simpa using hne⟩ := rfl

@[simp]
theorem twoStateRemainingEquiv_symm_some
    {κ : Type*} (target other : κ)
    (hne : target ≠ other)
    (hcover : ∀ z : κ, z = target ∨ z = other) :
    (twoStateRemainingEquiv target other hne hcover).symm (some ()) =
      ⟨none, by simp⟩ := rfl

/-- For a two-state discounted Shapley system, fixed nonzero relations for
the two coordinates either have zero formal resultant in the other value
variable, or yield a fixed nonzero bivariate polynomial in the rate and target
value.

The first branch is an explicit degeneracy certificate. The second branch has
the nested-polynomial orientation used by the algebraic-selection API: the
outer variable is the target value and coefficient polynomials use the rate. -/
theorem discountedShapleySystem_twoState_elimination_dichotomy
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
    (target other : κ) (hne : target ≠ other)
    (hcover : ∀ z : κ, z = target ∨ z = other) :
    ∃ P Q : MvPolynomial (Option κ) ℝ,
      P ≠ 0 ∧ Q ≠ 0 ∧
      (∀ l ∈ S,
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l)) P = 0) ∧
      (∀ l ∈ S,
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l)) Q = 0) ∧
      (Polynomial.resultant
          (Math.MultivariateElimination.isolateVariable
            (some other) P)
          (Math.MultivariateElimination.isolateVariable
            (some other) Q) = 0 ∨
        ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
          ∀ l ∈ S,
            Polynomial.eval (w l target)
              (Polynomial.map (Polynomial.evalRingHom l) R) = 0) := by
  obtain ⟨P, hP, hPvanish⟩ :=
    exists_nonzero_mvPolynomial_of_discountedShapleySystem
      r T w S hw target
  obtain ⟨Q, hQ, hQvanish⟩ :=
    exists_nonzero_mvPolynomial_of_discountedShapleySystem
      r T w S hw other
  refine ⟨P, Q, hP, hQ, hPvanish, hQvanish, ?_⟩
  by_cases hres :
      Polynomial.resultant
        (Math.MultivariateElimination.isolateVariable
          (some other) P)
        (Math.MultivariateElimination.isolateVariable
          (some other) Q) = 0
  · exact Or.inl hres
  · right
    let E :=
      Math.MultivariateElimination.eliminateVariable
        (some other) P Q
    let e :=
      twoStateRemainingEquiv target other hne hcover
    let R :=
      Math.MultivariateElimination.bivariateOfEquiv e E
    refine ⟨R, ?_, ?_⟩
    · have hE0 :=
        Math.MultivariateElimination.eliminateVariable_ne_zero
          (some other) hP hres
      intro hR
      apply hE0
      apply
        (Math.MultivariateElimination.bivariateOfEquiv e).injective
      simpa [R] using hR
    · intro l hl
      let a : Option κ → ℝ :=
        fun x => Option.casesOn x l (w l)
      have hE :
          MvPolynomial.eval
            (fun x : {x : Option κ // x ≠ some other} => a x)
            E = 0 :=
        Math.MultivariateElimination.eval_eliminateVariable_eq_zero
          (some other) a (hPvanish l hl) (hQvanish l hl)
      calc
        Polynomial.eval (w l target)
            (Polynomial.map (Polynomial.evalRingHom l) R) =
          MvPolynomial.eval
            (fun x : {x : Option κ // x ≠ some other} => a x)
            E := by
              simpa [R, e, a] using
                (Math.MultivariateElimination.eval_bivariateOfEquiv
                  e E
                  (fun x : {x : Option κ // x ≠ some other} =>
                    a x))
        _ = 0 := hE

/-- Pair local kernel candidates before taking resultants in a two-state
system. Either a specific nonzero target/other kernel pair is active at the
same rate and has zero resultant, or the product of all nondegenerate pairwise
eliminants is a fixed nonzero bivariate relation for the target value.

This avoids artificial common factors introduced by first multiplying all
kernel candidates for each state. -/
theorem discountedShapleySystem_twoState_kernelPair_elimination_dichotomy
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
    (target other : κ) (hne : target ≠ other)
    (hcover : ∀ z : κ, z = target ∨ z = other) :
    (∃ l ∈ S, ∃ kt ko : ActionKernelShape I J,
      mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) kt ≠ 0 ∧
      mvBorderedKernelPoly
          (discountedStochasticEntry (r other) (T other))
          (some other) ko ≠ 0 ∧
      MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r target) (T target))
            (some target) kt) = 0 ∧
      MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r other) (T other))
            (some other) ko) = 0 ∧
      Polynomial.resultant
          (Math.MultivariateElimination.isolateVariable
            (some other)
            (mvBorderedKernelPoly
              (discountedStochasticEntry (r target) (T target))
              (some target) kt))
          (Math.MultivariateElimination.isolateVariable
            (some other)
            (mvBorderedKernelPoly
              (discountedStochasticEntry (r other) (T other))
              (some other) ko)) = 0) ∨
      ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
        ∀ l ∈ S,
          Polynomial.eval (w l target)
            (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  let Pt : ActionKernelShape I J →
      MvPolynomial (Option κ) ℝ :=
    mvBorderedKernelPoly
      (discountedStochasticEntry (r target) (T target))
      (some target)
  let Po : ActionKernelShape I J →
      MvPolynomial (Option κ) ℝ :=
    mvBorderedKernelPoly
      (discountedStochasticEntry (r other) (T other))
      (some other)
  by_cases hdeg : ∃ l ∈ S, ∃ kt ko,
      Pt kt ≠ 0 ∧ Po ko ≠ 0 ∧
      MvPolynomial.eval
        (fun x => Option.casesOn x l (w l)) (Pt kt) = 0 ∧
      MvPolynomial.eval
        (fun x => Option.casesOn x l (w l)) (Po ko) = 0 ∧
      Polynomial.resultant
        (Math.MultivariateElimination.isolateVariable
          (some other) (Pt kt))
        (Math.MultivariateElimination.isolateVariable
          (some other) (Po ko)) = 0
  · left
    simpa [Pt, Po] using hdeg
  · right
    push Not at hdeg
    let Kt := {k : ActionKernelShape I J // Pt k ≠ 0}
    let Ko := {k : ActionKernelShape I J // Po k ≠ 0}
    let Kgood := {k : Kt × Ko //
      Polynomial.resultant
        (Math.MultivariateElimination.isolateVariable
          (some other) (Pt k.1))
        (Math.MultivariateElimination.isolateVariable
          (some other) (Po k.2)) ≠ 0}
    let E : Kgood →
          MvPolynomial
            {x : Option κ // x ≠ some other} ℝ :=
      fun k =>
        Math.MultivariateElimination.eliminateVariable
          (some other) (Pt k.1.1) (Po k.1.2)
    let A : MvPolynomial
        {x : Option κ // x ≠ some other} ℝ :=
      ∏ k, E k
    have hA : A ≠ 0 := by
      dsimp only [A]
      rw [Finset.prod_ne_zero_iff]
      intro k _
      exact Math.MultivariateElimination.eliminateVariable_ne_zero
        (some other) k.1.1.property k.property
    let e :=
      twoStateRemainingEquiv target other hne hcover
    let R :=
      Math.MultivariateElimination.bivariateOfEquiv e A
    refine ⟨R, ?_, ?_⟩
    · intro hR
      apply hA
      apply
        (Math.MultivariateElimination.bivariateOfEquiv e).injective
      simpa [R] using hR
    · intro l hl
      let a : Option κ → ℝ :=
        fun x => Option.casesOn x l (w l)
      obtain ⟨kt, hkt, hkteval⟩ :=
        exists_nonzero_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
          r T w S hw target hl
      obtain ⟨ko, hko, hkoeval⟩ :=
        exists_nonzero_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
          r T w S hw other hl
      let kts : Kt := ⟨kt, by simpa [Kt, Pt] using hkt⟩
      let kos : Ko := ⟨ko, by simpa [Ko, Po] using hko⟩
      have hFteval : MvPolynomial.eval a (Pt kts) = 0 := by
        simpa [kts, Pt, a] using hkteval
      have hFoeval : MvPolynomial.eval a (Po kos) = 0 := by
        simpa [kos, Po, a] using hkoeval
      have hres :
          Polynomial.resultant
            (Math.MultivariateElimination.isolateVariable
              (some other) (Pt kts))
            (Math.MultivariateElimination.isolateVariable
              (some other) (Po kos)) ≠ 0 := by
        exact hdeg l hl kt ko hkt hko hkteval hkoeval
      let kgood : Kgood := ⟨(kts, kos), hres⟩
      have hEeval :
          MvPolynomial.eval
            (fun x : {x : Option κ // x ≠ some other} => a x)
            (E kgood) = 0 := by
        exact
          Math.MultivariateElimination.eval_eliminateVariable_eq_zero
            (some other) a hFteval hFoeval
      have hAeval :
          MvPolynomial.eval
            (fun x : {x : Option κ // x ≠ some other} => a x)
            A = 0 := by
        dsimp only [A]
        rw [map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ kgood)
        exact hEeval
      calc
        Polynomial.eval (w l target)
            (Polynomial.map (Polynomial.evalRingHom l) R) =
          MvPolynomial.eval
            (fun x : {x : Option κ // x ≠ some other} => a x)
            A := by
              simpa [R, e, a] using
                (Math.MultivariateElimination.eval_bivariateOfEquiv
                  e A
                  (fun x : {x : Option κ // x ≠ some other} =>
                    a x))
        _ = 0 := hAeval

end ShapleySnow
