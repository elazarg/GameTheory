/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Math.Minimax.ShapleySnow
import Math.CofiniteIdeal
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
* `discountedShapleyActiveSystemIdeal`: the denominator-active coupled kernel
  equations with the rate moved into the coefficient ring.
* `moduleFinite_discountedShapleyActiveSystemIdeal_of_activeBranches`:
  fixed active-branch zero-dimensionality implies zero-dimensionality of the
  product-generated active ideal.
* `exists_nonzero_bivariateRelation_of_nonvanishingActiveBranches_moduleFinite`:
  zero-dimensionality after adjoining inverse-denominator equations gives one
  fixed bivariate relation across all selected branches.
* `exists_nonzero_bivariateRelation_of_discountedShapleyActiveSystemIdeal_moduleFinite`:
  zero-dimensionality of the active coupled kernel ideal gives a fixed
  bivariate coordinate relation.
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

/-- The bordered determinant associated to a kernel shape. Its nonvanishing
is the algebraic form of the Shapley--Snow basis condition. -/
noncomputable def mvBorderedKernelDenominator
    {σ I J : Type*} [Fintype I]
    (E : I → J → MvPolynomial σ ℝ) :
    ActionKernelShape I J → MvPolynomial σ ℝ :=
  fun ⟨_sz, rows, cols⟩ =>
    (borderedMatrix
      ((Matrix.of E).submatrix rows cols)).det

/-- A positive-size kernel shape whose bordered determinant is a nonzero
formal polynomial. -/
def IsActiveKernelShape
    {σ I J : Type*} [Fintype I]
    (E : I → J → MvPolynomial σ ℝ)
    (k : ActionKernelShape I J) : Prop :=
  0 < k.1.val ∧ mvBorderedKernelDenominator E k ≠ 0

/-- At every parameter, a coupled Shapley equation selects a
denominator-active local bordered-kernel candidate that vanishes at the full
value assignment. -/
theorem exists_active_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
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
      IsActiveKernelShape
          (discountedStochasticEntry (r target) (T target)) k ∧
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelDenominator
            (discountedStochasticEntry (r target) (T target)) k) ≠ 0 ∧
        mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k ≠ 0 ∧
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r target) (T target))
            (some target) k) = 0 := by
  let A : Matrix I J ℝ := fun i j =>
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
  let k : ActionKernelShape I J :=
    ⟨⟨sz, by omega⟩, rows, cols⟩
  have hden :
      mvBorderedKernelDenominator
        (discountedStochasticEntry (r target) (T target)) k ≠ 0 := by
    intro hz
    apply hborder
    have heval := congrArg (MvPolynomial.eval a) hz
    simp only [mvBorderedKernelDenominator, k, map_zero,
      RingHom.map_det, RingHom.mapMatrix_apply,
      map_borderedMatrix, hmap] at heval
    exact heval
  refine ⟨k, ⟨hsz, hden⟩, ?_, ?_, ?_⟩
  · change MvPolynomial.eval a
      (mvBorderedKernelDenominator
        (discountedStochasticEntry (r target) (T target)) k) ≠ 0
    simp only [mvBorderedKernelDenominator, k,
      RingHom.map_det, RingHom.mapMatrix_apply, map_borderedMatrix]
    rw [hmap]
    exact hborder
  · exact discountedStochastic_borderedKernelPoly_ne_zero
      (r target) (T target) target hsz rows cols (by
        simpa [mvBorderedKernelDenominator, k] using hden)
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
  obtain ⟨k, _hkactive, _hkdenominator, hk, hkeval⟩ :=
    exists_active_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
      r T w S hw target hl
  exact ⟨k, hk, hkeval⟩

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

noncomputable local instance
    {I J : Type*} [Fintype I] [Fintype J] :
    Fintype (ActionKernelShape I J) :=
  Fintype.ofFinite (ActionKernelShape I J)

/-- The product of all denominator-active local bordered-kernel candidates for
one state. Candidates with identically zero bordered determinant are excluded
because they cannot be selected by `exists_bordered_kernel`. -/
noncomputable def discountedShapleyActiveCoordinatePoly
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
      if IsActiveKernelShape
          (discountedStochasticEntry (r target) (T target)) k then
        mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k
      else 1

theorem discountedShapleyActiveCoordinatePoly_ne_zero
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) :
    discountedShapleyActiveCoordinatePoly r T target ≠ 0 := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  rw [discountedShapleyActiveCoordinatePoly,
    Finset.prod_ne_zero_iff]
  intro k _
  split_ifs with hk
  · rcases k with ⟨sz, rows, cols⟩
    exact discountedStochastic_borderedKernelPoly_ne_zero
      (r target) (T target) target hk.1 rows cols hk.2
  · exact one_ne_zero

/-- One denominator-active local kernel factor, with the rate moved into
`ℝ[λ]` and value coordinates retained as variables. Inactive shapes contribute
the unit factor, matching `discountedShapleyActiveCoordinatePoly`. -/
noncomputable def discountedShapleyActiveKernelPoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) (k : ActionKernelShape I J) :
    MvPolynomial κ (Polynomial ℝ) := by
  classical
  exact
    MvPolynomial.optionEquivRight ℝ κ
      (if IsActiveKernelShape
          (discountedStochasticEntry (r target) (T target)) k then
        mvBorderedKernelPoly
          (discountedStochasticEntry (r target) (T target))
          (some target) k
      else 1)

/-- The active state polynomial is the product of its individual kernel
factors after moving the rate into the coefficient ring. -/
theorem prod_discountedShapleyActiveKernelPoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) :
    ∏ k, discountedShapleyActiveKernelPoly r T target k =
      MvPolynomial.optionEquivRight ℝ κ
        (discountedShapleyActiveCoordinatePoly r T target) := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  rw [discountedShapleyActiveCoordinatePoly, map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rfl

/-- A local active-kernel factor after extending coefficients from `ℝ[λ]`
to the rational-function field `ℝ(λ)`. -/
noncomputable def localizedDiscountedShapleyActiveKernelPoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) (k : ActionKernelShape I J) :
    MvPolynomial κ (FractionRing (Polynomial ℝ)) :=
  MvPolynomial.map
    (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))
    (discountedShapleyActiveKernelPoly r T target k)

/-- The localized ideal for a fixed choice of one active-kernel shape at
each state. Choices of inactive shapes generate the unit ideal. -/
noncomputable def discountedShapleyActiveBranchIdeal
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J) :
    Ideal (MvPolynomial κ (FractionRing (Polynomial ℝ))) :=
  Ideal.span
    (Set.range fun s =>
      localizedDiscountedShapleyActiveKernelPoly r T s (branch s))

/-- One bordered denominator with the rate moved into `ℝ[λ]`. -/
noncomputable def discountedShapleyKernelDenominatorPoly
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (target : κ) (k : ActionKernelShape I J) :
    MvPolynomial κ (Polynomial ℝ) :=
  MvPolynomial.optionEquivRight ℝ κ
    (mvBorderedKernelDenominator
      (discountedStochasticEntry (r target) (T target)) k)

/-- The product of the selected bordered denominators in a fixed branch. -/
noncomputable def discountedShapleyBranchDenominator
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J) :
    MvPolynomial κ (Polynomial ℝ) :=
  ∏ s, discountedShapleyKernelDenominatorPoly
    r T s (branch s)

/-- A fixed branch together with an inverse for the product of its bordered
denominators. The extra `none` variable enforces pointwise denominator
nonvanishing and removes components supported on a denominator-zero locus. -/
noncomputable def discountedShapleyNonvanishingBranchIdeal
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J) :
    Ideal (MvPolynomial (Option κ) (Polynomial ℝ)) :=
  Ideal.span
      (Set.range fun s =>
        MvPolynomial.rename some
          (discountedShapleyActiveKernelPoly r T s (branch s))) ⊔
    Ideal.span {
      MvPolynomial.X none *
        MvPolynomial.rename some
          (discountedShapleyBranchDenominator r T branch) - 1}

/-- A common zero of a fixed branch at which the product of bordered
denominators is nonzero extends, by assigning its inverse to `none`, to a zero
of the nonvanishing branch ideal. -/
theorem eval₂_mem_discountedShapleyNonvanishingBranchIdeal_eq_zero
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J)
    (l : ℝ) (v : κ → ℝ)
    (hkernel : ∀ s,
      MvPolynomial.eval₂ (Polynomial.evalRingHom l) v
        (discountedShapleyActiveKernelPoly r T s (branch s)) = 0)
    (hdenominator :
      MvPolynomial.eval₂ (Polynomial.evalRingHom l) v
        (discountedShapleyBranchDenominator r T branch) ≠ 0)
    {P : MvPolynomial (Option κ) (Polynomial ℝ)}
    (hP : P ∈ discountedShapleyNonvanishingBranchIdeal r T branch) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom l)
        (fun x => Option.casesOn x
          (MvPolynomial.eval₂ (Polynomial.evalRingHom l) v
            (discountedShapleyBranchDenominator r T branch))⁻¹
          v)
        P = 0 := by
  let d : ℝ :=
    MvPolynomial.eval₂ (Polynomial.evalRingHom l) v
      (discountedShapleyBranchDenominator r T branch)
  let a : Option κ → ℝ :=
    fun x => Option.casesOn x d⁻¹ v
  have hle :
      discountedShapleyNonvanishingBranchIdeal r T branch ≤
        RingHom.ker
          (MvPolynomial.eval₂Hom (Polynomial.evalRingHom l) a) := by
    rw [discountedShapleyNonvanishingBranchIdeal, sup_le_iff]
    constructor
    · rw [Ideal.span_le]
      rintro Q ⟨s, rfl⟩
      change MvPolynomial.eval₂ (Polynomial.evalRingHom l) a
        (MvPolynomial.rename some
          (discountedShapleyActiveKernelPoly r T s (branch s))) = 0
      rw [MvPolynomial.eval₂_rename]
      have ha : a ∘ some = v := by
        funext z
        simp [a]
      rw [ha]
      exact hkernel s
    · rw [Ideal.span_le]
      rintro Q ⟨hQ | hQ, rfl⟩
      · change MvPolynomial.eval₂ (Polynomial.evalRingHom l) a
          (MvPolynomial.X none *
            MvPolynomial.rename some
              (discountedShapleyBranchDenominator r T branch) - 1) = 0
        rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename,
          MvPolynomial.eval₂_one]
        have ha : a ∘ some = v := by
          funext z
          simp [a]
        rw [ha]
        simp only [a]
        change d⁻¹ * d - 1 = 0
        rw [inv_mul_cancel₀ (by simpa [d] using hdenominator), sub_self]
  exact hle hP

/-- At every parameter, one fixed kernel choice per state gives vanishing
branch equations whose bordered-denominator product is nonzero at the actual
coupled Shapley value. -/
theorem exists_activeBranch_eval_zero_denominator_ne_zero_of_discountedShapleySystem
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
    {l : ℝ} (hl : l ∈ S) :
    ∃ branch : κ → ActionKernelShape I J,
      (∀ s, IsActiveKernelShape
        (discountedStochasticEntry (r s) (T s)) (branch s)) ∧
      (∀ s,
        MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
          (discountedShapleyActiveKernelPoly r T s (branch s)) = 0) ∧
      MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
        (discountedShapleyBranchDenominator r T branch) ≠ 0 := by
  have hexists (s : κ) :
      ∃ k : ActionKernelShape I J,
        IsActiveKernelShape
            (discountedStochasticEntry (r s) (T s)) k ∧
          MvPolynomial.eval
            (fun x => Option.casesOn x l (w l))
            (mvBorderedKernelDenominator
              (discountedStochasticEntry (r s) (T s)) k) ≠ 0 ∧
          mvBorderedKernelPoly
            (discountedStochasticEntry (r s) (T s))
            (some s) k ≠ 0 ∧
          MvPolynomial.eval
            (fun x => Option.casesOn x l (w l))
            (mvBorderedKernelPoly
              (discountedStochasticEntry (r s) (T s))
              (some s) k) = 0 :=
    exists_active_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
      r T w S hw s hl
  choose branch hactive hdenominator _hpoly hkernel using hexists
  refine ⟨branch, hactive, ?_, ?_⟩
  · intro s
    rw [discountedShapleyActiveKernelPoly, if_pos (hactive s)]
    calc
      MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
          (MvPolynomial.optionEquivRight ℝ κ
            (mvBorderedKernelPoly
              (discountedStochasticEntry (r s) (T s))
              (some s) (branch s))) =
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelPoly
            (discountedStochasticEntry (r s) (T s))
            (some s) (branch s)) := by
          simpa [Polynomial.evalRingHom] using
            (eval₂_optionEquivRight (RingHom.id ℝ) (w l) l
              (mvBorderedKernelPoly
                (discountedStochasticEntry (r s) (T s))
                (some s) (branch s)))
      _ = 0 := hkernel s
  · rw [discountedShapleyBranchDenominator]
    change
      (MvPolynomial.eval₂Hom (Polynomial.evalRingHom l) (w l))
        (∏ s, discountedShapleyKernelDenominatorPoly
          r T s (branch s)) ≠ 0
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro s _
    rw [discountedShapleyKernelDenominatorPoly]
    calc
      MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
          (MvPolynomial.optionEquivRight ℝ κ
            (mvBorderedKernelDenominator
              (discountedStochasticEntry (r s) (T s))
              (branch s))) =
        MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (mvBorderedKernelDenominator
            (discountedStochasticEntry (r s) (T s))
            (branch s)) := by
          simpa [Polynomial.evalRingHom] using
            (eval₂_optionEquivRight (RingHom.id ℝ) (w l) l
              (mvBorderedKernelDenominator
                (discountedStochasticEntry (r s) (T s))
                (branch s)))
      _ ≠ 0 := hdenominator s

/-- A fixed branch that selects an inactive shape contains a unit generator
and is therefore the unit ideal. -/
theorem discountedShapleyActiveBranchIdeal_eq_top_of_not_active
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J)
    (target : κ)
    (htarget : ¬ IsActiveKernelShape
      (discountedStochasticEntry (r target) (T target))
      (branch target)) :
    discountedShapleyActiveBranchIdeal r T branch = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨target, ?_⟩
  simp [localizedDiscountedShapleyActiveKernelPoly,
    discountedShapleyActiveKernelPoly, htarget]

/-- A nonvanishing branch with an inactive selected shape is the unit ideal,
because its corresponding kernel equation is the unit polynomial. -/
theorem discountedShapleyNonvanishingBranchIdeal_eq_top_of_not_active
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J)
    (target : κ)
    (htarget : ¬ IsActiveKernelShape
      (discountedStochasticEntry (r target) (T target))
      (branch target)) :
    discountedShapleyNonvanishingBranchIdeal r T branch = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.mem_sup_left
  apply Ideal.subset_span
  refine ⟨target, ?_⟩
  simp [discountedShapleyActiveKernelPoly, htarget]

theorem eval_discountedShapleyActiveCoordinatePoly_eq_zero
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
        (discountedShapleyActiveCoordinatePoly r T target) = 0 := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  obtain ⟨k, hk, _hkdenominator, _hkpoly, hkeval⟩ :=
    exists_active_mvBorderedKernelPoly_eval_zero_of_discountedShapleySystem
      r T w S hw target hl
  rw [discountedShapleyActiveCoordinatePoly, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [if_pos hk]
  exact hkeval

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

/-- The coupled ideal generated only by denominator-active local kernel
products, with the rate in `ℝ[λ]`. -/
noncomputable def discountedShapleyActiveSystemIdeal
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ) :
    Ideal (MvPolynomial κ (Polynomial ℝ)) :=
  Ideal.span
    (Set.range fun s =>
      MvPolynomial.optionEquivRight ℝ κ
        (discountedShapleyActiveCoordinatePoly r T s))

/-- After extending coefficients to `ℝ(λ)`, the active coupled ideal is
generated by the statewise products of the localized kernel factors. -/
theorem map_discountedShapleyActiveSystemIdeal
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ) :
    (discountedShapleyActiveSystemIdeal r T).map
        (MvPolynomial.map
          (algebraMap (Polynomial ℝ)
            (FractionRing (Polynomial ℝ)))) =
      Ideal.span
        (Set.range fun s =>
          ∏ k, localizedDiscountedShapleyActiveKernelPoly r T s k) := by
  classical
  letI : Fintype (ActionKernelShape I J) :=
    Fintype.ofFinite (ActionKernelShape I J)
  rw [discountedShapleyActiveSystemIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext P
  constructor
  · rintro ⟨Q, ⟨s, rfl⟩, rfl⟩
    refine ⟨s, ?_⟩
    change (∏ k, localizedDiscountedShapleyActiveKernelPoly r T s k) =
      MvPolynomial.map
        (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))
        (MvPolynomial.optionEquivRight ℝ κ
          (discountedShapleyActiveCoordinatePoly r T s))
    rw [← prod_discountedShapleyActiveKernelPoly, map_prod]
    rfl
  · rintro ⟨s, rfl⟩
    refine
      ⟨MvPolynomial.optionEquivRight ℝ κ
          (discountedShapleyActiveCoordinatePoly r T s),
        ⟨s, rfl⟩, ?_⟩
    change MvPolynomial.map
        (algebraMap (Polynomial ℝ) (FractionRing (Polynomial ℝ)))
        (MvPolynomial.optionEquivRight ℝ κ
          (discountedShapleyActiveCoordinatePoly r T s)) =
      ∏ k, localizedDiscountedShapleyActiveKernelPoly r T s k
    rw [← prod_discountedShapleyActiveKernelPoly, map_prod]
    rfl

/-- It is enough to prove finite-dimensionality for every fixed tuple of
local kernel choices. This is the branch-level zero-dimensionality boundary
for the active coupled Shapley system. -/
theorem moduleFinite_discountedShapleyActiveSystemIdeal_of_branches
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (hbranch : ∀ branch : κ → ActionKernelShape I J,
      Module.Finite (FractionRing (Polynomial ℝ))
        (MvPolynomial κ (FractionRing (Polynomial ℝ)) ⧸
          discountedShapleyActiveBranchIdeal r T branch)) :
    Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial κ (FractionRing (Polynomial ℝ)) ⧸
        (discountedShapleyActiveSystemIdeal r T).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ))))) := by
  rw [map_discountedShapleyActiveSystemIdeal]
  apply Math.CofiniteIdeal.moduleFinite_quotient_span_range_prod_of_branches
    (f := fun s k =>
      localizedDiscountedShapleyActiveKernelPoly r T s k)
  intro branch
  exact hbranch branch

/-- Only tuples of denominator-active kernel shapes need a
finite-dimensionality proof; every other branch is already the unit ideal. -/
theorem moduleFinite_discountedShapleyActiveSystemIdeal_of_activeBranches
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (hbranch : ∀ branch : κ → ActionKernelShape I J,
      (∀ s, IsActiveKernelShape
        (discountedStochasticEntry (r s) (T s)) (branch s)) →
      Module.Finite (FractionRing (Polynomial ℝ))
        (MvPolynomial κ (FractionRing (Polynomial ℝ)) ⧸
          discountedShapleyActiveBranchIdeal r T branch)) :
    Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial κ (FractionRing (Polynomial ℝ)) ⧸
        (discountedShapleyActiveSystemIdeal r T).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ))))) := by
  apply moduleFinite_discountedShapleyActiveSystemIdeal_of_branches r T
  intro branch
  by_cases hactive : ∀ s, IsActiveKernelShape
      (discountedStochasticEntry (r s) (T s)) (branch s)
  · exact hbranch branch hactive
  · obtain ⟨s, hs⟩ := Classical.not_forall.mp hactive
    rw [discountedShapleyActiveBranchIdeal_eq_top_of_not_active
      r T branch s hs]
    exact Math.CofiniteIdeal.moduleFinite_quotient_top

/-- Every coupled Shapley value assignment annihilates the active-kernel ideal
after specializing the rate coefficient. -/
theorem eval₂_mem_discountedShapleyActiveSystemIdeal_eq_zero
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
    (hP : P ∈ discountedShapleyActiveSystemIdeal r T)
    {l : ℝ} (hl : l ∈ S) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l) P = 0 := by
  have hle : discountedShapleyActiveSystemIdeal r T ≤
      RingHom.ker (MvPolynomial.eval₂Hom
        (Polynomial.evalRingHom l) (w l)) := by
    rw [discountedShapleyActiveSystemIdeal, Ideal.span_le]
    rintro P ⟨s, rfl⟩
    change MvPolynomial.eval₂ (Polynomial.evalRingHom l) (w l)
      (MvPolynomial.optionEquivRight ℝ κ
        (discountedShapleyActiveCoordinatePoly r T s)) = 0
    calc
      _ = MvPolynomial.eval
          (fun x => Option.casesOn x l (w l))
          (discountedShapleyActiveCoordinatePoly r T s) := by
        simpa [Polynomial.evalRingHom] using
          (eval₂_optionEquivRight (RingHom.id ℝ) (w l) l
            (discountedShapleyActiveCoordinatePoly r T s))
      _ = 0 :=
        eval_discountedShapleyActiveCoordinatePoly_eq_zero
          r T w S hw s hl
  exact hle hP

/-- If the active-kernel ideal becomes zero-dimensional over `ℝ(λ)`, every
chosen value coordinate satisfies a fixed nonzero bivariate relation. -/
theorem exists_nonzero_bivariateRelation_of_discountedShapleyActiveSystemIdeal_moduleFinite
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
        (discountedShapleyActiveSystemIdeal r T).map
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
      (discountedShapleyActiveSystemIdeal r T) target
  refine ⟨R, hR, fun l hl => ?_⟩
  have hz :=
    eval₂_mem_discountedShapleyActiveSystemIdeal_eq_zero
      r T w S hw hRmem hl
  rw [eval₂_polynomial_aeval_X] at hz
  simpa [Polynomial.eval₂_eq_eval_map] using hz

/-- A finite-dimensional nonvanishing fixed branch supplies a nonzero
coordinate relation in the original rate-polynomial coefficient ring. -/
theorem exists_nonzero_coordinateRelation_mem_of_nonvanishingBranch_moduleFinite
    {κ I J : Type*} [Fintype κ] [Fintype I] [Fintype J]
    (r : κ → I → J → ℝ)
    (T : κ → I → J → κ → ℝ)
    (branch : κ → ActionKernelShape I J)
    [Module.Finite (FractionRing (Polynomial ℝ))
      (MvPolynomial (Option κ) (FractionRing (Polynomial ℝ)) ⧸
        (discountedShapleyNonvanishingBranchIdeal r T branch).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))]
    (target : κ) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      Polynomial.aeval (MvPolynomial.X (some target)) R ∈
        discountedShapleyNonvanishingBranchIdeal r T branch := by
  exact
    Math.MultivariateElimination.exists_nonzero_coordinateRelation_mem_of_moduleFinite_fractionRing
      (discountedShapleyNonvanishingBranchIdeal r T branch) (some target)

/-- If every denominator-nonvanishing active fixed branch is
zero-dimensional over `ℝ(λ)`, then every coupled Shapley value coordinate
satisfies one fixed nonzero bivariate relation. -/
theorem exists_nonzero_bivariateRelation_of_nonvanishingActiveBranches_moduleFinite
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
    (hfinite : ∀ branch : κ → ActionKernelShape I J,
      (∀ s, IsActiveKernelShape
        (discountedStochasticEntry (r s) (T s)) (branch s)) →
      Module.Finite (FractionRing (Polynomial ℝ))
        (MvPolynomial (Option κ) (FractionRing (Polynomial ℝ)) ⧸
          (discountedShapleyNonvanishingBranchIdeal r T branch).map
            (MvPolynomial.map
              (algebraMap (Polynomial ℝ)
                (FractionRing (Polynomial ℝ))))))
    (target : κ) :
    ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
      ∀ l ∈ S,
        Polynomial.eval (w l target)
          (Polynomial.map (Polynomial.evalRingHom l) R) = 0 := by
  classical
  have hrelation (branch : κ → ActionKernelShape I J) :
      ∃ R : Polynomial (Polynomial ℝ), R ≠ 0 ∧
        Polynomial.aeval (MvPolynomial.X (some target)) R ∈
          discountedShapleyNonvanishingBranchIdeal r T branch := by
    by_cases hactive : ∀ s, IsActiveKernelShape
        (discountedStochasticEntry (r s) (T s)) (branch s)
    · letI : Module.Finite (FractionRing (Polynomial ℝ))
          (MvPolynomial (Option κ) (FractionRing (Polynomial ℝ)) ⧸
            (discountedShapleyNonvanishingBranchIdeal r T branch).map
              (MvPolynomial.map
                (algebraMap (Polynomial ℝ)
                  (FractionRing (Polynomial ℝ))))) :=
        hfinite branch hactive
      exact
        exists_nonzero_coordinateRelation_mem_of_nonvanishingBranch_moduleFinite
          r T branch target
    · obtain ⟨s, hs⟩ := Classical.not_forall.mp hactive
      letI : Module.Finite (FractionRing (Polynomial ℝ))
          (MvPolynomial (Option κ) (FractionRing (Polynomial ℝ)) ⧸
            (discountedShapleyNonvanishingBranchIdeal r T branch).map
              (MvPolynomial.map
                (algebraMap (Polynomial ℝ)
                  (FractionRing (Polynomial ℝ))))) := by
        rw [discountedShapleyNonvanishingBranchIdeal_eq_top_of_not_active
          r T branch s hs, Ideal.map_top]
        exact Math.CofiniteIdeal.moduleFinite_quotient_top
      exact
        exists_nonzero_coordinateRelation_mem_of_nonvanishingBranch_moduleFinite
          r T branch target
  choose R hR hRmem using hrelation
  refine ⟨∏ branch, R branch, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro branch _
    exact hR branch
  · intro l hl
    obtain ⟨branch, _hactive, hkernel, hdenominator⟩ :=
      exists_activeBranch_eval_zero_denominator_ne_zero_of_discountedShapleySystem
        r T w S hw hl
    have hz :=
      eval₂_mem_discountedShapleyNonvanishingBranchIdeal_eq_zero
        r T branch l (w l) hkernel hdenominator (hRmem branch)
    rw [eval₂_polynomial_aeval_X] at hz
    have hz' :
        Polynomial.eval (w l target)
          (Polynomial.map (Polynomial.evalRingHom l) (R branch)) = 0 := by
      simpa [Polynomial.eval₂_eq_eval_map] using hz
    rw [← Polynomial.eval₂_eq_eval_map]
    change
      (Polynomial.eval₂RingHom
        (Polynomial.evalRingHom l) (w l target))
        (∏ branch, R branch) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ branch)
    simpa [Polynomial.eval₂_eq_eval_map] using hz'

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
