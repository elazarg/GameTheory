/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Math.Minimax.MinimaxLoomis
import Math.Minimax.Loomis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Math.Minimax.ShapleySnow

The Shapley–Snow kernel theorem for finite matrix games, and its parametric corollary.

## Stage 1 — kernel theorem interface

For a matrix game `A : Matrix (Fin m) (Fin n) ℝ`, the value
`V := MinimaxLoomis.lam0 A` satisfies a determinant identity over a square
submatrix `B`. This module uses the bordered formulation

```
det (borderedMatrix B) ≠ 0
V * det (borderedMatrix B) = det B.
```

It also develops the classical adjugate formulation
`V * (∑ i j, B.adjugate i j) = B.det` with nonzero adjugate sum.

This module factors that argument into theorem-level interfaces:

* `exists_kernel_of_saddlePoint` handles pure saddle points;
* `value_and_kernelIdentity_of_equalizing` proves the determinant identity for any
  square equalizing pair, including singular matrices;
* `exists_kernel_of_equalizing_of_adjugateSum_ne` uses the correct bordered-system
  condition, namely a nonzero adjugate sum;
* the `OptimalStrategies` section supplies extreme optimizers, complementary slackness,
  trivial-kernel lemmas, and cardinality bounds;
* `exists_extreme_tight_bordered_submatrix` selects a basis of tight columns
  on one extreme strategy's support;
* `borderedKernelIdentity` converts bordered injectivity to the determinant
  identity by Cramer's rule;
* `exists_bordered_kernel` is the general bordered kernel theorem.

The payoff submatrix itself may be singular; the nonsingular object is its
bordered system.

## Stage 2 — the parametric product corollary

Given a family of matrices with entries that are bivariate polynomials
`E i j : Polynomial (Polynomial ℝ)` — outer variable `v` (`Polynomial.X`), coefficients
in `ℝ[λ]` — and a self-referential value function `val : ℝ → ℝ` with
`val λ = lam0 (fun i j => bivEval λ (val λ) (E i j))` for `λ` in some set `S`,
Stage 1 produces a square kernel shape whose bordered polynomial
`F_B := B.det - X * det (borderedMatrix B)` vanishes at `(λ, val λ)`.
There are only finitely many possible shapes, so a product of the nonzero
candidates gives one fixed polynomial vanishing along the value function.

The clean, fully general engine behind this argument is
`exists_nonzero_poly_of_forall_mem_exists` below: given *any* finite family of candidate
bivariate polynomials such that, for every parameter, at least one candidate is both
nonzero (as an abstract polynomial) and vanishes at that parameter's specialisation
point, their product is a single nonzero polynomial vanishing at every parameter.

### A statement adjustment, and why it is necessary

The bordered matrix-game instantiation
`exists_nonzero_poly_of_borderedKernel` carries only a genericity hypothesis
`hgen`; `exists_bordered_kernel` supplies its matrix-game input. The adjugate
variant `exists_nonzero_poly_of_kernel` exposes the classical kernel property
as `hkernel`.

`hgen` is needed because a nonzero kernel denominator does not by itself imply
that `F_B` is a nonzero abstract polynomial. Counterexample: `m = n = 1`,
`E 0 0 = Polynomial.X`. Both the adjugate sum and bordered determinant are
`1`, yet `F_B = X - X * 1 = 0`. In this example `val λ = lam0 [[val λ]] =
val λ` holds *tautologically* for every real number `val λ`, so `val` is entirely
unconstrained by the hypotheses — and indeed no single nonzero polynomial can force
`val` at every `λ` in this case. `hgen` rules out exactly this degeneracy. Genuine
applications (Stage 3: discounted stochastic games, entries affine in `v` with slope
`λ ∈ (0, 1)`, i.e. a *strict* contraction) are not of this degenerate form.

## Attribution

Shapley, L. S. and Snow, R. N., "Basic solutions of discrete games", 1950.
-/

open Finset BigOperators Matrix Polynomial

namespace ShapleySnow

/-! ### Stage 1 — the classical Shapley–Snow kernel theorem

```
theorem shapley_snow_kernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (r : ℕ) (hr : 0 < r) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
      (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j) ≠ 0 ∧
        MinimaxLoomis.lam0 A * (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j)
          = (A.submatrix rows cols).det
```

Classical proof architecture (Shapley–Snow 1950): take extreme optimal mixed
strategies `x` (for the row player) and `y` (for the column player) with supports
`R ⊆ Fin m`, `C ⊆ Fin n`; on the kernel the payoff equations are tight,
`(Aᵀ x) j = V` for `j ∈ C` and `(A y) i = V` for `i ∈ R`. Extremality of `x`, `y` among
optimal strategies forces `|R| = |C| =: r` and makes the bordered `(r+1) × (r+1)` system
`[[B, 1], [1ᵀ, 0]]` (`B := A.submatrix rows cols` for `rows`, `cols` enumerating `R`, `C`)
nonsingular. Cramer's rule on that bordered system, or the determinant identity
`det [[B, 1], [1ᵀ, 0]] = -∑ i j, B.adjugate i j`, then gives
`V = B.det / (∑ i j, B.adjugate i j)` with the denominator nonzero. The case `r = 1`
covers pure kernels (`B.adjugate = 1` by `Matrix.adjugate_subsingleton`, so
`∑ i j, B.adjugate i j = 1` and `V = B.det`, i.e. a pure saddle point).

### Factored proof components

`exists_kernel_of_saddlePoint` gives a `1 × 1` kernel for a pure saddle point.
`value_and_kernelIdentity_of_equalizing` gives the determinant identity for a square
equalizing pair without assuming nonsingularity. The separate hypothesis
`∑ i, ∑ j, B.adjugate i j ≠ 0` is the kernel condition; the formally checked
`singular_equalizing_kernel_example` shows why it cannot be replaced by `IsUnit B.det`.

For extreme optimal strategies, `eq_zero_of_extreme_optimalRow` and
`eq_zero_of_extreme_optimalCol` prove that the tight-constraint linear system has
trivial kernel on the strategy support. Their proof is the `openSegment`-based
`x ± εd` perturbation argument, derived directly from `Set.extremePoints`.
`card_support_le_card_tightCol_of_extreme` and
`card_support_le_card_tightRow_of_extreme` convert this injectivity into cardinality
bounds. `eq_zero_of_extreme_optimalRow_bordered` adds the value coordinate,
`exists_bordered_subfamily` extracts a tight-column basis, and
`exists_extreme_tight_bordered_submatrix` instantiates that basis on the
strategy support. `exists_bordered_kernel` packages the resulting general
kernel theorem. `exists_kernel_of_extreme_matching_support` remains an
alternative adjugate-form reassembly interface.
-/

/-- **Saddle-point base case.** If `(i₀, j₀)` is a saddle point of `A` — row `i₀`
attains its minimum at column `j₀`, and column `j₀` attains its maximum at row `i₀` —
then `lam0 A = A i₀ j₀`, and the singleton kernel `{i₀} × {j₀}` (`r = 1`) satisfies the
Shapley–Snow identity: `A.adjugate` on a `1 × 1` matrix is the constant `1`
(`Matrix.adjugate_subsingleton`), so the adjugate sum is `1 ≠ 0` and the determinant is
just the entry `A i₀ j₀ = lam0 A`. -/
theorem exists_kernel_of_saddlePoint {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) (i₀ : Fin m) (j₀ : Fin n)
    (hrow : ∀ j, A i₀ j₀ ≤ A i₀ j) (hcol : ∀ i, A i j₀ ≤ A i₀ j₀) :
    ∃ (rows : Fin 1 ↪ Fin m) (cols : Fin 1 ↪ Fin n),
      (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j) ≠ 0 ∧
        MinimaxLoomis.lam0 A * (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j)
          = (A.submatrix rows cols).det := by
  classical
  have hVeq : MinimaxLoomis.lam0 A = A i₀ j₀ := by
    have hlamaux : MinimaxLoomis.lam.aux A (stdSimplex.pure i₀) = A i₀ j₀ := by
      unfold MinimaxLoomis.lam.aux
      have hfun : (fun j => wsum (stdSimplex.pure i₀) (fun i => A i j)) = fun j => A i₀ j :=
        funext fun j => wsum_pure_apply i₀ (fun i => A i j)
      rw [hfun]
      exact le_antisymm (Finset.inf'_le _ (Finset.mem_univ j₀))
        (Finset.le_inf' _ _ fun j _ => hrow j)
    have hmuaux : MinimaxLoomis.mu.aux A (stdSimplex.pure j₀) = A i₀ j₀ := by
      unfold MinimaxLoomis.mu.aux
      have hfun : (fun i => wsum (stdSimplex.pure j₀) (fun j => A i j)) = fun i => A i j₀ :=
        funext fun i => wsum_pure_apply j₀ (fun j => A i j)
      rw [hfun]
      exact le_antisymm (Finset.sup'_le _ _ fun i _ => hcol i)
        (Finset.le_sup' (fun i => A i j₀) (Finset.mem_univ i₀))
    have hVlam0 : A i₀ j₀ ≤ MinimaxLoomis.lam0 A :=
      hlamaux ▸ MinimaxLoomis.lam.aux.le_lam0 A (stdSimplex.pure i₀)
    have hmu0V : MinimaxLoomis.mu0 A ≤ A i₀ j₀ :=
      hmuaux ▸ MinimaxLoomis.mu.aux.ge_mu0 A (stdSimplex.pure j₀)
    exact le_antisymm ((MinimaxLoomis.lam0_le_mu0 A).trans hmu0V) hVlam0
  set rows : Fin 1 ↪ Fin m := ⟨fun _ => i₀, fun _ _ _ => Subsingleton.elim _ _⟩ with hrows
  set cols : Fin 1 ↪ Fin n := ⟨fun _ => j₀, fun _ _ _ => Subsingleton.elim _ _⟩ with hcols
  have hB00 : (A.submatrix rows cols) 0 0 = A i₀ j₀ := rfl
  have hadj : (A.submatrix rows cols).adjugate = 1 := Matrix.adjugate_subsingleton _
  refine ⟨rows, cols, ?_, ?_⟩
  · rw [hadj]
    simp
  · rw [hadj, hVeq, Matrix.det_fin_one, hB00]
    simp

/-- A right equalizing strategy gives the Shapley--Snow determinant identity.
The matrix need not be nonsingular, and no optimality hypothesis is used. -/
theorem kernelIdentity_of_right_equalizing
    {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (y : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hy : ∀ i, wsum y (fun j => A i j) = V) :
    V * (∑ i, ∑ j, A.adjugate i j) = A.det := by
  classical
  have hmulVec : A *ᵥ y.val = V • (1 : Fin n → ℝ) := by
    funext i
    have hrow :
        (A *ᵥ y.val) i = wsum y (fun j => A i j) :=
      dotProduct_comm (A i) y.val
    rw [hrow, hy i]
    simp
  have hadj :
      Matrix.adjugate A *ᵥ (A *ᵥ y.val) =
        A.det • y.val := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hadj' :
      Matrix.adjugate A *ᵥ (A *ᵥ y.val) =
        V • (fun i => ∑ j, Matrix.adjugate A i j) := by
    rw [hmulVec, Matrix.mulVec_smul]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hkey :
      A.det • y.val =
        V • (fun i => ∑ j, Matrix.adjugate A i j) :=
    hadj.symm.trans hadj'
  have hsum :
      A.det * (∑ i, y.val i) =
        V * (∑ i, ∑ j, Matrix.adjugate A i j) := by
    have hcongr :=
      congrArg (fun f : Fin n → ℝ => ∑ i, f i) hkey
    simpa [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      using hcongr
  rw [y.property.2, mul_one] at hsum
  exact hsum.symm

/-- A left equalizing strategy gives the Shapley--Snow determinant identity.
This is the transpose of `kernelIdentity_of_right_equalizing`. -/
theorem kernelIdentity_of_left_equalizing
    {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hx : ∀ j, wsum x (fun i => A i j) = V) :
    V * (∑ i, ∑ j, A.adjugate i j) = A.det := by
  have hxT :
      ∀ j, wsum x (fun i => A.transpose j i) = V := by
    simpa only [Matrix.transpose_apply] using hx
  have hid :=
    kernelIdentity_of_right_equalizing A.transpose x V hxT
  rw [Matrix.det_transpose, ← Matrix.adjugate_transpose A] at hid
  have hsum :
      (∑ i, ∑ j, A.adjugate.transpose i j) =
        ∑ i, ∑ j, A.adjugate i j := by
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [hsum] at hid
  exact hid

/-- The bordered matrix for column equalization and mass normalization.
For a vector `(d, t)`, its `Fin n` coordinates are
`∑ i, d i * B i j - t`, and its `Unit` coordinate is `∑ i, d i`. -/
def borderedMatrix {ι R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) :
    Matrix (Sum ι Unit) (Sum ι Unit) R :=
  Matrix.fromBlocks B.transpose
    (fun _ _ => -1) (fun _ _ => 1) 0

theorem map_borderedMatrix
    {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S]
    (f : R →+* S) (B : Matrix ι ι R) :
    (borderedMatrix B).map f = borderedMatrix (B.map f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [borderedMatrix]
  · cases j
    simp [borderedMatrix]
  · cases i
    simp [borderedMatrix]
  · cases i
    cases j
    simp [borderedMatrix]

theorem borderedMatrix_mulVec_inl
    {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (d : ι → ℝ) (t : ℝ) (j : ι) :
    (borderedMatrix B *ᵥ
        Sum.elim d (fun _ => t)) (Sum.inl j) =
      (∑ i, d i * B i j) - t := by
  classical
  simp only [mulVec, dotProduct, borderedMatrix,
    Fintype.sum_sum_type, fromBlocks_apply₁₁,
    transpose_apply, Sum.elim_inl, univ_unique,
    PUnit.default_eq_unit, fromBlocks_apply₁₂,
    Sum.elim_inr, neg_mul, one_mul, sum_neg_distrib,
    sum_const, card_singleton, one_smul]
  simp_rw [mul_comm]
  ring

theorem borderedMatrix_mulVec_inr
    {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (d : ι → ℝ) (t : ℝ) :
    (borderedMatrix B *ᵥ
        Sum.elim d (fun _ => t)) (Sum.inr ()) =
      ∑ i, d i := by
  classical
  simp [borderedMatrix, Matrix.mulVec, dotProduct]

/-- Bordered injectivity supplies a nonzero kernel denominator, and Cramer's
rule identifies the determinant relation for a left equalizing simplex.

This formulation includes value-zero singular payoff matrices without asking
for a separate adjugate-sum argument. -/
theorem borderedKernelIdentity
    {n : ℕ} [Nonempty (Fin n)]
    (B : Matrix (Fin n) (Fin n) ℝ)
    (x : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hx : ∀ j, wsum x (fun i => B i j) = V)
    (hborder : ∀ (d : Fin n → ℝ) (t : ℝ),
      (∑ i, d i = 0) →
      (∀ j, ∑ i, d i * B i j = t) →
      d = 0 ∧ t = 0) :
    (borderedMatrix B).det ≠ 0 ∧
      V * (borderedMatrix B).det = B.det := by
  classical
  let C := borderedMatrix B
  have hker :
      ∀ z : Sum (Fin n) Unit → ℝ,
        C *ᵥ z = 0 → z = 0 := by
    intro z hz
    let d : Fin n → ℝ := fun i => z (Sum.inl i)
    let t : ℝ := z (Sum.inr ())
    have hzrepr : z = Sum.elim d (fun _ => t) := by
      funext k
      cases k with
      | inl i => rfl
      | inr u =>
          cases u
          rfl
    have hsum : ∑ i, d i = 0 := by
      have hzlast := congrFun hz (Sum.inr ())
      rw [hzrepr, borderedMatrix_mulVec_inr] at hzlast
      exact hzlast
    have heq : ∀ j, ∑ i, d i * B i j = t := by
      intro j
      have hzj := congrFun hz (Sum.inl j)
      have hzj' :
          (∑ i, d i * B i j) - t = 0 := by
        rw [hzrepr, borderedMatrix_mulVec_inl] at hzj
        exact hzj
      exact sub_eq_zero.mp hzj'
    obtain ⟨hd, ht⟩ := hborder d t hsum heq
    funext k
    cases k with
    | inl i => simpa [d] using congrFun hd i
    | inr u =>
        cases u
        simpa [t] using ht
  have hinj :
      Function.Injective (fun z => C *ᵥ z) := by
    intro z z' hzz'
    apply sub_eq_zero.mp
    apply hker (z - z')
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hzz'
  have hCmatrixUnit : IsUnit C :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hCunit : IsUnit C.det :=
    hCmatrixUnit.map Matrix.detMonoidHom
  have hCne : C.det ≠ 0 := hCunit.ne_zero
  let z : Sum (Fin n) Unit → ℝ :=
    Sum.elim x.val (fun _ => V)
  let e : Sum (Fin n) Unit → ℝ :=
    Pi.single (Sum.inr ()) 1
  have hCz : C *ᵥ z = e := by
    funext k
    cases k with
    | inl j =>
        have hxj := hx j
        change (∑ i, x.val i * B i j) = V at hxj
        simp [C, z, e, borderedMatrix_mulVec_inl, hxj]
    | inr u =>
        cases u
        simp [C, z, e, borderedMatrix_mulVec_inr,
          x.property.2]
  have hsame : Matrix.cramer C e = C.det • z := by
    apply hinj
    change
      C *ᵥ Matrix.cramer C e = C *ᵥ (C.det • z)
    rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hCz]
  have hcomponent := congrFun hsame (Sum.inr ())
  have hupdate :
      C.updateCol (Sum.inr ()) e =
        Matrix.fromBlocks B.transpose 0
          (fun _ _ => 1) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · cases j
      simp [C, e, borderedMatrix]
    · cases i
      rfl
    · cases i
      cases j
      simp [C, e, borderedMatrix]
  have hdetUpdate :
      (C.updateCol (Sum.inr ()) e).det = B.det := by
    rw [hupdate, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_transpose]
    simp
  change
    (C.updateCol (Sum.inr ()) e).det =
      C.det * V at hcomponent
  rw [hdetUpdate] at hcomponent
  exact ⟨hCne, by nlinarith⟩

/-- An equalizing pair determines the matrix-game value and the
Shapley--Snow determinant identity. No nonsingularity assumption is needed for
the identity: multiplying `A *ᵥ y = V • 1` by `adjugate A` works for singular
matrices as well. -/
theorem value_and_kernelIdentity_of_equalizing {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hxT : ∀ j, wsum x (fun i => A i j) = V)
    (hy : ∀ i, wsum y (fun j => A i j) = V) :
    MinimaxLoomis.lam0 A = V ∧
      MinimaxLoomis.lam0 A * (∑ i, ∑ j, A.adjugate i j) = A.det := by
  classical
  have hVeq : MinimaxLoomis.lam0 A = V := by
    have hlamaux : MinimaxLoomis.lam.aux A x = V := by
      unfold MinimaxLoomis.lam.aux
      rw [show (fun j => wsum x (fun i => A i j)) =
        fun _ : Fin n => V from funext hxT]
      exact Finset.inf'_const Finset.univ_nonempty V
    have hmuaux : MinimaxLoomis.mu.aux A y = V := by
      unfold MinimaxLoomis.mu.aux
      rw [show (fun i => wsum y (fun j => A i j)) =
        fun _ : Fin n => V from funext hy]
      exact Finset.sup'_const Finset.univ_nonempty V
    have hVlam0 : V ≤ MinimaxLoomis.lam0 A :=
      hlamaux ▸ MinimaxLoomis.lam.aux.le_lam0 A x
    have hmu0V : MinimaxLoomis.mu0 A ≤ V :=
      hmuaux ▸ MinimaxLoomis.mu.aux.ge_mu0 A y
    exact le_antisymm
      ((MinimaxLoomis.lam0_le_mu0 A).trans hmu0V) hVlam0
  have hmulVec : A *ᵥ y.val = V • (1 : Fin n → ℝ) := by
    funext i
    have hrow : (A *ᵥ y.val) i =
        wsum y (fun j => A i j) :=
      dotProduct_comm (A i) y.val
    rw [hrow, hy i]
    simp
  have hadj :
      Matrix.adjugate A *ᵥ (A *ᵥ y.val) =
        A.det • y.val := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hadj' :
      Matrix.adjugate A *ᵥ (A *ᵥ y.val) =
        V • (fun i => ∑ j, Matrix.adjugate A i j) := by
    rw [hmulVec, Matrix.mulVec_smul]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hkey :
      A.det • y.val =
        V • (fun i => ∑ j, Matrix.adjugate A i j) :=
    hadj.symm.trans hadj'
  have hsum :
      A.det * (∑ i, y.val i) =
        V * (∑ i, ∑ j, Matrix.adjugate A i j) := by
    have hcongr := congrArg (fun f : Fin n → ℝ => ∑ i, f i) hkey
    simpa [Pi.smul_apply, smul_eq_mul, Finset.mul_sum] using hcongr
  rw [y.property.2, mul_one] at hsum
  exact ⟨hVeq, hVeq ▸ hsum.symm⟩

/-- **Completely-mixed kernel with the correct bordered-system condition.**
If a square game has an equalizing pair and its adjugate sum is nonzero, the
whole matrix is a Shapley--Snow kernel. This includes singular kernels of value
zero. -/
theorem exists_kernel_of_equalizing_of_adjugateSum_ne
    {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hxT : ∀ j, wsum x (fun i => A i j) = V)
    (hy : ∀ i, wsum y (fun j => A i j) = V)
    (hSne : (∑ i, ∑ j, A.adjugate i j) ≠ 0) :
    MinimaxLoomis.lam0 A = V ∧
      (∑ i, ∑ j, A.adjugate i j) ≠ 0 ∧
      MinimaxLoomis.lam0 A *
          (∑ i, ∑ j, A.adjugate i j) = A.det := by
  obtain ⟨hVeq, hid⟩ :=
    value_and_kernelIdentity_of_equalizing A x y V hxT hy
  exact ⟨hVeq, hSne, hid⟩

/-- A singular Shapley--Snow kernel.

The matrix `[-1, 2; 1, -2]` has equalizing strategies
`x = (1/2, 1/2)` and `y = (2/3, 1/3)` at value zero. Its determinant
vanishes, while its adjugate sum does not. This example makes the distinction
between matrix nonsingularity and the correct nonzero-adjugate-sum
(equivalently, bordered-system) kernel condition explicit. -/
theorem singular_equalizing_kernel_example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 2; 1, -2]
    A.det = 0 ∧
      (∑ i, ∑ j, A.adjugate i j) ≠ 0 ∧
      MinimaxLoomis.lam0 A = 0 ∧
      MinimaxLoomis.lam0 A *
        (∑ i, ∑ j, A.adjugate i j) = A.det := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 2; 1, -2]
  let x : stdSimplex ℝ (Fin 2) :=
    ⟨![1 / 2, 1 / 2],
      (by intro i; fin_cases i <;> norm_num),
      (by norm_num)⟩
  let y : stdSimplex ℝ (Fin 2) :=
    ⟨![2 / 3, 1 / 3],
      (by intro j; fin_cases j <;> norm_num),
      (by norm_num)⟩
  have hx0 : x 0 = 1 / 2 := by rfl
  have hx1 : x 1 = 1 / 2 := by rfl
  have hy0 : y 0 = 2 / 3 := by rfl
  have hy1 : y 1 = 1 / 3 := by rfl
  have hx : ∀ j, wsum x (fun i => A i j) = 0 := by
    intro j
    fin_cases j
    · norm_num [wsum, A, dotProduct, hx0, hx1]
    · norm_num [wsum, A, dotProduct, hx0, hx1]
  have hy : ∀ i, wsum y (fun j => A i j) = 0 := by
    intro i
    fin_cases i
    · norm_num [wsum, A, dotProduct, hy0, hy1]
    · norm_num [wsum, A, dotProduct, hy0, hy1]
  have hdata :=
    value_and_kernelIdentity_of_equalizing A x y 0 hx hy
  have hdet : A.det = 0 := by
    norm_num [A, Matrix.det_fin_two]
  have hsum : (∑ i, ∑ j, A.adjugate i j) ≠ 0 := by
    rw [Matrix.adjugate_fin_two]
    norm_num [A]
  exact ⟨hdet, hsum, hdata.1, hdata.2⟩

/-- **Completely-mixed nonsingular kernel** (Kaplansky's determinant formula
for a fully-mixed square game). Nonsingularity is a sufficient condition for
the adjugate sum to be nonzero; singular kernels are covered by
`exists_kernel_of_equalizing_of_adjugateSum_ne`.

Proof: `V = lam0 A` follows the saddle-point argument above, with mixed strategies in
place of pure ones (`lam.aux`/`mu.aux` collapse to the constant `V` since every pure
response is equalised). The determinant identity is linear algebra: left-multiplying
`A *ᵥ y = V • 1` by `adjugate A` and using `adjugate A * A = det A • 1` gives
`det A • y = V • (fun i => ∑ j, adjugate A i j)`; summing over `i` and using `∑ y = 1`
gives `det A = V * (∑ i j, adjugate A i j)`, and `det A ≠ 0` (nonsingularity) forces the
adjugate sum to be nonzero. -/
theorem exists_kernel_of_completelyMixed {n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (x y : stdSimplex ℝ (Fin n)) (V : ℝ)
    (hxT : ∀ j, wsum x (fun i => A i j) = V) (hy : ∀ i, wsum y (fun j => A i j) = V) :
    MinimaxLoomis.lam0 A = V ∧ (∑ i, ∑ j, A.adjugate i j) ≠ 0 ∧
      MinimaxLoomis.lam0 A * (∑ i, ∑ j, A.adjugate i j) = A.det := by
  obtain ⟨hVeq, hid⟩ :=
    value_and_kernelIdentity_of_equalizing A x y V hxT hy
  have hSne : (∑ i, ∑ j, A.adjugate i j) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hid
    exact hA.ne_zero hid.symm
  exact ⟨hVeq, hSne, hid⟩

/-! ### Optimal strategy sets: convexity, compactness, extreme optimizers

Building blocks for the classical Shapley–Snow reduction (`x`, `y` "extreme
optimal mixed strategies" in the proof architecture above). `optimalRowStrategies A V`
and `optimalColStrategies A V` are the sets of row- / column-player mixed strategies
that are optimal *at value `V`* — phrased as subsets of the ambient vector space
`I → ℝ` / `J → ℝ` (rather than the `stdSimplex ℝ I` subtype used elsewhere) so
that Mathlib's `Set.extremePoints` / Krein–Milman API, which is stated for subsets of a
topological vector space, applies to them directly.

At `V := MinimaxLoomis.lam0 A` these sets are shown convex, compact, and (via
`exists_xx_lam0` / `exists_yy_mu0` together with `Loomis.minmax_from_general`, the
already-proved von Neumann minimax `lam0 = mu0`) nonempty, so Krein–Milman
(`IsCompact.extremePoints_nonempty`) produces an *extreme* optimal strategy for each
player. `expectedPayoff_eq_of_optimal` and its corollaries `tight_of_optimal_col_support`
/ `tight_of_optimal_row_support` are the complementary-slackness step of the sketch: on
the support of an optimal pair, the payoff equations are tight. The
bordered tight-column basis selector after this section converts these facts
to a square kernel. -/

section OptimalStrategies

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The row player's mixed strategies that are optimal *at value `V`*: simplex points
whose expected payoff against every pure column is at least `V`. -/
def optimalRowStrategies (A : I → J → ℝ) (V : ℝ) : Set (I → ℝ) :=
  stdSimplex ℝ I ∩ ⋂ j, {x : I → ℝ | V ≤ ∑ i, x i * A i j}

/-- The column player's mixed strategies that are optimal *at value `V`*: simplex points
whose expected payoff against every pure row is at most `V`. The sum order `y j * A i j`
matches `MinimaxLoomis.mu.aux`'s `wsum y (fun j => A i j)`. -/
def optimalColStrategies (A : I → J → ℝ) (V : ℝ) : Set (J → ℝ) :=
  stdSimplex ℝ J ∩ ⋂ i, {y : J → ℝ | ∑ j, y j * A i j ≤ V}

omit [Fintype J] [Nonempty I] [Nonempty J] in
/-- Each "beats `V` against pure column `j`" cut is a closed halfspace, hence convex. -/
theorem convex_rowHalfspace (A : I → J → ℝ) (V : ℝ) (j : J) :
    Convex ℝ {x : I → ℝ | V ≤ ∑ i, x i * A i j} := by
  intro x hx y hy a b ha hb _hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hcomb : ∑ i, (a • x + b • y) i * A i j
      = a * (∑ i, x i * A i j) + b * (∑ i, y i * A i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcomb]
  have h1 : a * V ≤ a * (∑ i, x i * A i j) := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * V ≤ b * (∑ i, y i * A i j) := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * V + b * V = V := by rw [← add_mul, _hab, one_mul]
  linarith

omit [Fintype I] [Nonempty I] [Nonempty J] in
/-- Each "beaten by `V` against pure row `i`" cut is a closed halfspace, hence convex. -/
theorem convex_colHalfspace (A : I → J → ℝ) (V : ℝ) (i : I) :
    Convex ℝ {y : J → ℝ | ∑ j, y j * A i j ≤ V} := by
  intro x hx y hy a b ha hb _hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hcomb : ∑ j, (a • x + b • y) j * A i j
      = a * (∑ j, x j * A i j) + b * (∑ j, y j * A i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcomb]
  have h1 : a * (∑ j, x j * A i j) ≤ a * V := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * (∑ j, y j * A i j) ≤ b * V := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * V + b * V = V := by rw [← add_mul, _hab, one_mul]
  linarith

omit [Fintype J] [Nonempty I] [Nonempty J] in
/-- `optimalRowStrategies A V` is convex: the intersection of the (convex) simplex with
countably many convex halfspace cuts. -/
theorem convex_optimalRowStrategies (A : I → J → ℝ) (V : ℝ) :
    Convex ℝ (optimalRowStrategies A V) :=
  (convex_stdSimplex ℝ I).inter (convex_iInter fun j => convex_rowHalfspace A V j)

omit [Fintype I] [Nonempty I] [Nonempty J] in
/-- `optimalColStrategies A V` is convex. -/
theorem convex_optimalColStrategies (A : I → J → ℝ) (V : ℝ) :
    Convex ℝ (optimalColStrategies A V) :=
  (convex_stdSimplex ℝ J).inter (convex_iInter fun i => convex_colHalfspace A V i)

omit [Fintype J] [Nonempty I] [Nonempty J] in
theorem isClosed_rowHalfspace (A : I → J → ℝ) (V : ℝ) (j : J) :
    IsClosed {x : I → ℝ | V ≤ ∑ i, x i * A i j} := by
  have heq : {x : I → ℝ | V ≤ ∑ i, x i * A i j}
      = (fun x : I → ℝ => ∑ i, x i * A i j) ⁻¹' Set.Ici V := rfl
  rw [heq]
  exact isClosed_Ici.preimage
    (continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).mul continuous_const)

omit [Fintype I] [Nonempty I] [Nonempty J] in
theorem isClosed_colHalfspace (A : I → J → ℝ) (V : ℝ) (i : I) :
    IsClosed {y : J → ℝ | ∑ j, y j * A i j ≤ V} := by
  have heq : {y : J → ℝ | ∑ j, y j * A i j ≤ V}
      = (fun y : J → ℝ => ∑ j, y j * A i j) ⁻¹' Set.Iic V := rfl
  rw [heq]
  exact isClosed_Iic.preimage
    (continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).mul continuous_const)

omit [Fintype J] [Nonempty I] [Nonempty J] in
/-- `optimalRowStrategies A V` is closed (in the ambient space `I → ℝ`): the simplex is
compact-hence-closed in a `T2Space`, and each halfspace cut is closed. -/
theorem isClosed_optimalRowStrategies (A : I → J → ℝ) (V : ℝ) :
    IsClosed (optimalRowStrategies A V) :=
  (isCompact_stdSimplex ℝ I).isClosed.inter
    (isClosed_iInter fun j => isClosed_rowHalfspace A V j)

omit [Fintype I] [Nonempty I] [Nonempty J] in
/-- `optimalColStrategies A V` is closed. -/
theorem isClosed_optimalColStrategies (A : I → J → ℝ) (V : ℝ) :
    IsClosed (optimalColStrategies A V) :=
  (isCompact_stdSimplex ℝ J).isClosed.inter
    (isClosed_iInter fun i => isClosed_colHalfspace A V i)

omit [Fintype J] [Nonempty I] [Nonempty J] in
/-- `optimalRowStrategies A V` is compact: a closed subset of the compact simplex. -/
theorem isCompact_optimalRowStrategies (A : I → J → ℝ) (V : ℝ) :
    IsCompact (optimalRowStrategies A V) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ I) (isClosed_optimalRowStrategies A V)
    Set.inter_subset_left

omit [Fintype I] [Nonempty I] [Nonempty J] in
/-- `optimalColStrategies A V` is compact. -/
theorem isCompact_optimalColStrategies (A : I → J → ℝ) (V : ℝ) :
    IsCompact (optimalColStrategies A V) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ J) (isClosed_optimalColStrategies A V)
    Set.inter_subset_left

/-- At `V := lam0 A`, `optimalRowStrategies` is nonempty: `exists_xx_lam0` supplies a
mixed strategy whose column-payoffs all dominate `lam0 A`. -/
theorem optimalRowStrategies_lam0_nonempty (A : I → J → ℝ) :
    (optimalRowStrategies A (MinimaxLoomis.lam0 A)).Nonempty := by
  obtain ⟨xx, hxx⟩ := MinimaxLoomis.exists_xx_lam0 A
  exact ⟨xx.val, xx.property, Set.mem_iInter.2 fun j => hxx j⟩

/-- At `V := lam0 A`, `optimalColStrategies` is nonempty: `exists_yy_mu0` supplies a
mixed strategy whose row-payoffs are all dominated by `mu0 A`, and `mu0 A = lam0 A` by
the (already-proved) von Neumann minimax theorem `Loomis.minmax_from_general`. -/
theorem optimalColStrategies_lam0_nonempty (A : I → J → ℝ) :
    (optimalColStrategies A (MinimaxLoomis.lam0 A)).Nonempty := by
  rw [Loomis.minmax_from_general A]
  obtain ⟨yy, hyy⟩ := MinimaxLoomis.exists_yy_mu0 A
  exact ⟨yy.val, yy.property, Set.mem_iInter.2 fun i => hyy i⟩

/-- **Krein–Milman for the row player's optimal strategies.** A nonempty compact convex
set in a locally convex space has an extreme point (`IsCompact.extremePoints_nonempty`);
`optimalRowStrategies A (lam0 A)` is exactly such a set. This produces an *extreme*
optimal mixed strategy for the row player — the `x` of the reduction sketch above. -/
theorem extremePoints_optimalRowStrategies_nonempty (A : I → J → ℝ) :
    (Set.extremePoints ℝ (optimalRowStrategies A (MinimaxLoomis.lam0 A))).Nonempty :=
  IsCompact.extremePoints_nonempty (isCompact_optimalRowStrategies A (MinimaxLoomis.lam0 A))
    (optimalRowStrategies_lam0_nonempty A)

/-- **Krein–Milman for the column player's optimal strategies.** The `y` of the
reduction sketch above. -/
theorem extremePoints_optimalColStrategies_nonempty (A : I → J → ℝ) :
    (Set.extremePoints ℝ (optimalColStrategies A (MinimaxLoomis.lam0 A))).Nonempty :=
  IsCompact.extremePoints_nonempty (isCompact_optimalColStrategies A (MinimaxLoomis.lam0 A))
    (optimalColStrategies_lam0_nonempty A)

omit [Nonempty I] [Nonempty J] in
/-- **The expected payoff of any optimal pair equals the value.** If `x` is optimal for
the row player and `y` is optimal for the column player at the same value `V`, then
`E(x,y) = V`: `x`'s guarantee bounds `E(x,y)` below by `V` (averaging `x`'s per-column
guarantee `≥ V` against `y`), and `y`'s guarantee bounds `E(x,y)` above by `V`
(averaging `y`'s per-row guarantee `≤ V` against `x`); the two bounds coincide. -/
theorem expectedPayoff_eq_of_optimal {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ optimalRowStrategies A V)
    {y : J → ℝ} (hy : y ∈ optimalColStrategies A V) :
    ∑ i, ∑ j, x i * A i j * y j = V := by
  obtain ⟨hxs, hxge⟩ := hx
  obtain ⟨hys, hyle⟩ := hy
  rw [Set.mem_iInter] at hxge hyle
  simp only [Set.mem_setOf_eq] at hxge hyle
  have hswapR : ∑ i, ∑ j, x i * A i j * y j = ∑ j, y j * (∑ i, x i * A i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hswapC : ∑ i, ∑ j, x i * A i j * y j = ∑ i, x i * (∑ j, y j * A i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hge : V ≤ ∑ j, y j * (∑ i, x i * A i j) := by
    calc V = ∑ j, y j * V := by rw [← Finset.sum_mul, hys.2, one_mul]
      _ ≤ ∑ j, y j * (∑ i, x i * A i j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxge j) (hys.1 j)
  have hle : ∑ i, x i * (∑ j, y j * A i j) ≤ V := by
    calc ∑ i, x i * (∑ j, y j * A i j)
        ≤ ∑ i, x i * V :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyle i) (hxs.1 i)
      _ = V := by rw [← Finset.sum_mul, hxs.2, one_mul]
  have hSge : V ≤ ∑ i, ∑ j, x i * A i j * y j := hswapR ▸ hge
  have hSle : (∑ i, ∑ j, x i * A i j * y j) ≤ V := hswapC ▸ hle
  exact le_antisymm hSle hSge

omit [Nonempty I] [Nonempty J] in
/-- **Complementary slackness, column side.** If `y j ≠ 0` for an optimal column
strategy `y`, then column `j`'s payoff against `x` is exactly the value `V` (not just
`≥ V`). -/
theorem tight_of_optimal_col_support {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ optimalRowStrategies A V)
    {y : J → ℝ} (hy : y ∈ optimalColStrategies A V) {j : J} (hj : y j ≠ 0) :
    ∑ i, x i * A i j = V := by
  have hEV := expectedPayoff_eq_of_optimal hx hy
  obtain ⟨-, hxge⟩ := hx
  rw [Set.mem_iInter] at hxge
  simp only [Set.mem_setOf_eq] at hxge
  obtain ⟨hys, -⟩ := hy
  have hswap : ∑ i, ∑ j, x i * A i j * y j = ∑ j, y j * (∑ i, x i * A i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hswap] at hEV
  have hzero : ∑ j, y j * (∑ i, x i * A i j - V) = 0 := by
    have heq : ∑ j, y j * (∑ i, x i * A i j - V)
        = (∑ j, y j * (∑ i, x i * A i j)) - V * ∑ j, y j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq, hEV, hys.2, mul_one, sub_self]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset J), 0 ≤ y j * (∑ i, x i * A i j - V) :=
    fun j _ => mul_nonneg (hys.1 j) (by linarith [hxge j])
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.1 hall with h | h
  · exact absurd h hj
  · linarith

omit [Nonempty I] [Nonempty J] in
/-- **Complementary slackness, row side.** If `x i ≠ 0` for an optimal row strategy `x`,
then row `i`'s payoff against `y` is exactly the value `V`. -/
theorem tight_of_optimal_row_support {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ optimalRowStrategies A V)
    {y : J → ℝ} (hy : y ∈ optimalColStrategies A V) {i : I} (hi : x i ≠ 0) :
    ∑ j, y j * A i j = V := by
  have hEV := expectedPayoff_eq_of_optimal hx hy
  obtain ⟨-, hyle⟩ := hy
  rw [Set.mem_iInter] at hyle
  simp only [Set.mem_setOf_eq] at hyle
  obtain ⟨hxs, -⟩ := hx
  have hswap : ∑ i, ∑ j, x i * A i j * y j = ∑ i, x i * (∑ j, y j * A i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hswap] at hEV
  -- Note the sign: `y`'s guarantee is `≤ V`, so the nonnegative slack is `V - (Ay)_i`.
  have hzero : ∑ i, x i * (V - ∑ j, y j * A i j) = 0 := by
    have heq : ∑ i, x i * (V - ∑ j, y j * A i j)
        = (∑ i, x i) * V - ∑ i, x i * (∑ j, y j * A i j) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq, hxs.2, one_mul, hEV, sub_self]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ x i * (V - ∑ j, y j * A i j) :=
    fun i _ => mul_nonneg (hxs.1 i) (by linarith [hyle i])
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.1 hall with h | h
  · exact absurd h hi
  · linarith

omit [Fintype J] in
/-- **Extremality forces the tight-constraint system to have trivial kernel (row side).**
This is the precise "if the tight constraints had a nontrivial kernel direction `d`, then
`x ± εd` would both be optimal, contradicting extremality" step of the Shapley–Snow
reduction sketch. If `x` is an extreme point of `optimalRowStrategies A V`, and `d`
(i) is supported on `x`'s support, (ii) sums to `0` (so `x ± εd` stays in the simplex),
and (iii) is annihilated by every column tight at `x` (so `x ± εd` keeps those columns at
exactly `V`), then `d = 0`. Proof: for small `ε > 0`, both `x + εd` and `x - εd` lie in
`optimalRowStrategies A V` (nonnegativity from (i)+(ii) via a finite-min `ε`, tightness
preserved by (iii), strict columns stay `≥ V` by taking `ε` small relative to their
slack), and `x` is their midpoint; extremality then forces `x + εd = x`, i.e. `εd = 0`,
i.e. `d = 0` since `ε ≠ 0`. -/
theorem eq_zero_of_extreme_optimalRow [Finite J] {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A V))
    {d : I → ℝ} (hd_supp : ∀ i, x i = 0 → d i = 0) (hd_sum : ∑ i, d i = 0)
    (hd_tight : ∀ j, ∑ i, x i * A i j = V → ∑ i, d i * A i j = 0) : d = 0 := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  by_contra hd0
  obtain ⟨hxs, hxge⟩ := extremePoints_subset hx
  rw [Set.mem_iInter] at hxge
  simp only [Set.mem_setOf_eq] at hxge
  have hboundI_pos : ∀ i : I, (0:ℝ) < if x i = 0 then 1 else x i / (|d i| + 1) := by
    intro i; split_ifs with h
    · norm_num
    · have hxi_pos : 0 < x i := lt_of_le_of_ne (hxs.1 i) (Ne.symm h)
      positivity
  have hboundJ_pos : ∀ j : J,
      (0:ℝ) < if ∑ i, x i * A i j = V then 1
        else (∑ i, x i * A i j - V) / (|∑ i, d i * A i j| + 1) := by
    intro j; split_ifs with h
    · norm_num
    · have hslack : 0 < ∑ i, x i * A i j - V := by
        rcases lt_or_eq_of_le (hxge j) with h' | h'
        · linarith
        · exact absurd h'.symm h
      positivity
  set ε : ℝ := min
      (Finset.univ.inf' Finset.univ_nonempty
        (fun i : I => if x i = 0 then (1:ℝ) else x i / (|d i| + 1)))
      (Finset.univ.inf' Finset.univ_nonempty
        (fun j : J => if ∑ i, x i * A i j = V then (1:ℝ)
          else (∑ i, x i * A i j - V) / (|∑ i, d i * A i j| + 1)))
    with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min ((Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ => hboundI_pos i)
      ((Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => hboundJ_pos j)
  have hεI' : ∀ i : I, ε ≤ if x i = 0 then (1:ℝ) else x i / (|d i| + 1) := fun i =>
    (min_le_left _ _).trans
      (Finset.inf'_le (fun i : I => if x i = 0 then (1:ℝ) else x i / (|d i| + 1))
        (Finset.mem_univ i))
  have hεJ' : ∀ j : J, ε ≤ if ∑ i, x i * A i j = V then (1:ℝ)
      else (∑ i, x i * A i j - V) / (|∑ i, d i * A i j| + 1) := fun j =>
    (min_le_right _ _).trans
      (Finset.inf'_le
        (fun j : J => if ∑ i, x i * A i j = V then (1:ℝ)
          else (∑ i, x i * A i j - V) / (|∑ i, d i * A i j| + 1)) (Finset.mem_univ j))
  have hbdI : ∀ i, ε * |d i| ≤ x i := by
    intro i
    by_cases hxi : x i = 0
    · rw [hxi, hd_supp i hxi]; simp
    · have hb := hεI' i
      simp only [hxi, if_false] at hb
      have hpos : (0:ℝ) < |d i| + 1 := by positivity
      have h1 : ε * (|d i| + 1) ≤ x i := (le_div_iff₀ hpos).mp hb
      nlinarith
  have hbdJ : ∀ j, ∑ i, x i * A i j ≠ V →
      ε * |∑ i, d i * A i j| ≤ ∑ i, x i * A i j - V := by
    intro j hj
    have hb := hεJ' j
    simp only [hj, if_false] at hb
    have hpos : (0:ℝ) < |∑ i, d i * A i j| + 1 := by positivity
    have h1 : ε * (|∑ i, d i * A i j| + 1) ≤ ∑ i, x i * A i j - V := (le_div_iff₀ hpos).mp hb
    nlinarith
  -- `habs t bnd hbnd σ hσ` turns an absolute-value bound `ε * |t| ≤ bnd` into a two-sided
  -- bound on `σ * (ε * t)`, usable for whichever sign `σ = ±1` is in play.
  have habs : ∀ t bnd : ℝ, ε * |t| ≤ bnd → ∀ σ : ℝ, σ = 1 ∨ σ = -1 → |σ * (ε * t)| ≤ bnd := by
    intro t bnd hbnd σ hσ
    have hσ1 : |σ| = 1 := by rcases hσ with hσ | hσ <;> subst hσ <;> norm_num
    have heq : |σ * (ε * t)| = ε * |t| := by
      rw [abs_mul, abs_mul, hσ1, one_mul, abs_of_pos hεpos]
    rw [heq]; exact hbnd
  have hmem : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (fun i => x i + σ * (ε * d i)) ∈ optimalRowStrategies A V := by
    intro σ hσ
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp (habs (d i) (x i) (hbdI i) σ hσ)).1]
    · have hpt : ∀ i, x i + σ * (ε * d i) = x i + (σ * ε) * d i := fun i => by ring
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hxs.2, hd_sum]; ring
    · rw [Set.mem_iInter]
      intro j
      simp only [Set.mem_setOf_eq]
      have hswap : ∑ i, (x i + σ * (ε * d i)) * A i j
          = ∑ i, x i * A i j + σ * (ε * ∑ i, d i * A i j) := by
        have hpt : ∀ i, (x i + σ * (ε * d i)) * A i j
            = x i * A i j + (σ * ε) * (d i * A i j) := fun i => by ring
        simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
      rw [hswap]
      by_cases htight : ∑ i, x i * A i j = V
      · rw [hd_tight j htight]; simp only [mul_zero, add_zero]; linarith
      · linarith [(abs_le.mp
          (habs (∑ i, d i * A i j) (∑ i, x i * A i j - V) (hbdJ j htight) σ hσ)).1]
  have hx1mem := hmem 1 (Or.inl rfl)
  have hx2mem := hmem (-1) (Or.inr rfl)
  simp only [one_mul] at hx1mem
  have hxseg : x ∈ openSegment ℝ (fun i => x i + ε * d i) (fun i => x i + (-1) * (ε * d i)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := hx.2 hx1mem hx2mem hxseg
  have hεd0 : d = 0 := by
    funext i
    have hi : x i + ε * d i = x i := congrFun heq i
    rcases mul_eq_zero.1 (show ε * d i = 0 by linarith) with h | h
    · exact absurd h hεpos.ne'
    · exact h
  exact hd0 hεd0

/-- **The bordered tight-constraint system has trivial kernel (row side).**
Pair an extreme optimal row strategy `x` with any optimal column strategy `y`.
If a support-preserving direction `d` has zero total mass and changes every
column tight at `x` by the same scalar `t`, then both `d` and `t` vanish.

Complementary slackness makes the support of `y` tight at `x`, so averaging
the common change `t` against `y` rewrites it as an average of `d` against
the rows tight at `y`. That average is `V * ∑ i, d i = 0`. The theorem
`eq_zero_of_extreme_optimalRow` then kills `d`. This is the injectivity
property of the bordered linear system used by Shapley--Snow basis
selection. -/
theorem eq_zero_of_extreme_optimalRow_bordered
    {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ}
    (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A V))
    {y : J → ℝ} (hy : y ∈ optimalColStrategies A V)
    {d : I → ℝ} {t : ℝ}
    (hd_supp : ∀ i, x i = 0 → d i = 0)
    (hd_sum : ∑ i, d i = 0)
    (hd_tight :
      ∀ j, ∑ i, x i * A i j = V → ∑ i, d i * A i j = t) :
    d = 0 ∧ t = 0 := by
  classical
  have hxopt : x ∈ optimalRowStrategies A V := extremePoints_subset hx
  have ht : t = 0 := by
    calc
      t = ∑ j, y j * t := by
        rw [← Finset.sum_mul, hy.1.2, one_mul]
      _ = ∑ j, y j * (∑ i, d i * A i j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : y j = 0
        · simp [hj]
        · rw [hd_tight j (tight_of_optimal_col_support hxopt hy hj)]
      _ = ∑ j, ∑ i, y j * (d i * A i j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, y j * (d i * A i j) := Finset.sum_comm
      _ = ∑ i, d i * (∑ j, y j * A i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, d i * V := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x i = 0
        · simp [hd_supp i hi]
        · rw [tight_of_optimal_row_support hxopt hy hi]
      _ = 0 := by rw [← Finset.sum_mul, hd_sum, zero_mul]
  subst t
  exact ⟨eq_zero_of_extreme_optimalRow hx hd_supp hd_sum hd_tight, rfl⟩

omit [Fintype I] in
/-- **Extremality forces the tight-constraint system to have trivial kernel (column
side).** The column-player mirror of `eq_zero_of_extreme_optimalRow`: if `y` is an
extreme point of `optimalColStrategies A V`, and `e` (i) is supported on `y`'s support,
(ii) sums to `0`, and (iii) is annihilated by every row tight at `y`, then `e = 0`. -/
theorem eq_zero_of_extreme_optimalCol [Finite I] {A : I → J → ℝ} {V : ℝ}
    {y : J → ℝ} (hy : y ∈ Set.extremePoints ℝ (optimalColStrategies A V))
    {e : J → ℝ} (he_supp : ∀ j, y j = 0 → e j = 0) (he_sum : ∑ j, e j = 0)
    (he_tight : ∀ i, ∑ j, y j * A i j = V → ∑ j, e j * A i j = 0) : e = 0 := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  by_contra he0
  obtain ⟨hys, hyle⟩ := extremePoints_subset hy
  rw [Set.mem_iInter] at hyle
  simp only [Set.mem_setOf_eq] at hyle
  have hboundJ_pos : ∀ j : J, (0:ℝ) < if y j = 0 then 1 else y j / (|e j| + 1) := by
    intro j; split_ifs with h
    · norm_num
    · have hyj_pos : 0 < y j := lt_of_le_of_ne (hys.1 j) (Ne.symm h)
      positivity
  have hboundI_pos : ∀ i : I, (0:ℝ) < if ∑ j, y j * A i j = V then 1
      else (V - ∑ j, y j * A i j) / (|∑ j, e j * A i j| + 1) := by
    intro i; split_ifs with h
    · norm_num
    · have hslack : 0 < V - ∑ j, y j * A i j := by
        rcases lt_or_eq_of_le (hyle i) with h' | h'
        · linarith
        · exact absurd h' h
      positivity
  set ε : ℝ := min
      (Finset.univ.inf' Finset.univ_nonempty
        (fun j : J => if y j = 0 then (1:ℝ) else y j / (|e j| + 1)))
      (Finset.univ.inf' Finset.univ_nonempty
        (fun i : I => if ∑ j, y j * A i j = V then (1:ℝ)
          else (V - ∑ j, y j * A i j) / (|∑ j, e j * A i j| + 1)))
    with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min ((Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => hboundJ_pos j)
      ((Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ => hboundI_pos i)
  have hεJ' : ∀ j : J, ε ≤ if y j = 0 then (1:ℝ) else y j / (|e j| + 1) := fun j =>
    (min_le_left _ _).trans
      (Finset.inf'_le (fun j : J => if y j = 0 then (1:ℝ) else y j / (|e j| + 1))
        (Finset.mem_univ j))
  have hεI' : ∀ i : I, ε ≤ if ∑ j, y j * A i j = V then (1:ℝ)
      else (V - ∑ j, y j * A i j) / (|∑ j, e j * A i j| + 1) := fun i =>
    (min_le_right _ _).trans
      (Finset.inf'_le
        (fun i : I => if ∑ j, y j * A i j = V then (1:ℝ)
          else (V - ∑ j, y j * A i j) / (|∑ j, e j * A i j| + 1)) (Finset.mem_univ i))
  have hbdJ : ∀ j, ε * |e j| ≤ y j := by
    intro j
    by_cases hyj : y j = 0
    · rw [hyj, he_supp j hyj]; simp
    · have hb := hεJ' j
      simp only [hyj, if_false] at hb
      have hpos : (0:ℝ) < |e j| + 1 := by positivity
      have h1 : ε * (|e j| + 1) ≤ y j := (le_div_iff₀ hpos).mp hb
      nlinarith
  have hbdI : ∀ i, ∑ j, y j * A i j ≠ V → ε * |∑ j, e j * A i j| ≤ V - ∑ j, y j * A i j := by
    intro i hi
    have hb := hεI' i
    simp only [hi, if_false] at hb
    have hpos : (0:ℝ) < |∑ j, e j * A i j| + 1 := by positivity
    have h1 : ε * (|∑ j, e j * A i j| + 1) ≤ V - ∑ j, y j * A i j := (le_div_iff₀ hpos).mp hb
    nlinarith
  have habs : ∀ t bnd : ℝ, ε * |t| ≤ bnd → ∀ σ : ℝ, σ = 1 ∨ σ = -1 → |σ * (ε * t)| ≤ bnd := by
    intro t bnd hbnd σ hσ
    have hσ1 : |σ| = 1 := by rcases hσ with hσ | hσ <;> subst hσ <;> norm_num
    have heq : |σ * (ε * t)| = ε * |t| := by
      rw [abs_mul, abs_mul, hσ1, one_mul, abs_of_pos hεpos]
    rw [heq]; exact hbnd
  have hmem : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (fun j => y j + σ * (ε * e j)) ∈ optimalColStrategies A V := by
    intro σ hσ
    refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp (habs (e j) (y j) (hbdJ j) σ hσ)).1]
    · have hpt : ∀ j, y j + σ * (ε * e j) = y j + (σ * ε) * e j := fun j => by ring
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hys.2, he_sum]; ring
    · rw [Set.mem_iInter]
      intro i
      simp only [Set.mem_setOf_eq]
      have hswap : ∑ j, (y j + σ * (ε * e j)) * A i j
          = ∑ j, y j * A i j + σ * (ε * ∑ j, e j * A i j) := by
        have hpt : ∀ j, (y j + σ * (ε * e j)) * A i j
            = y j * A i j + (σ * ε) * (e j * A i j) := fun j => by ring
        simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
      rw [hswap]
      by_cases htight : ∑ j, y j * A i j = V
      · rw [he_tight i htight]; simp only [mul_zero, add_zero]; linarith
      · linarith [(abs_le.mp
          (habs (∑ j, e j * A i j) (V - ∑ j, y j * A i j) (hbdI i htight) σ hσ)).2]
  have hy1mem := hmem 1 (Or.inl rfl)
  have hy2mem := hmem (-1) (Or.inr rfl)
  simp only [one_mul] at hy1mem
  have hyseg : y ∈ openSegment ℝ (fun j => y j + ε * e j) (fun j => y j + (-1) * (ε * e j)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := hy.2 hy1mem hy2mem hyseg
  have he0' : e = 0 := by
    funext j
    have hj : y j + ε * e j = y j := congrFun heq j
    rcases mul_eq_zero.1 (show ε * e j = 0 by linarith) with h | h
    · exact absurd h hεpos.ne'
    · exact h
  exact he0 he0'

/-- **Reindexing a sum over a support.** If `f` vanishes off `x`'s support, its sum over
the whole (ambient, `Fintype`) index type equals its sum over the support subtype. Used
below to translate the `hd_sum`/`hd_tight`-shaped hypotheses of `eq_zero_of_extreme_*`
(indexed over the full type) into sums over a strict subtype (the support), which is what
carries a usable `Module.finrank`. -/
theorem sum_eq_sum_support {ι : Type*} [Fintype ι] {x : ι → ℝ} (f : ι → ℝ)
    (hf : ∀ i, x i = 0 → f i = 0) : ∑ i, f i = ∑ i : {i : ι // x i ≠ 0}, f i.val := by
  classical
  refine Finset.sum_congr_set {i : ι | x i ≠ 0} f (fun i => f i.val) (fun _ _ => rfl) ?_
  intro i hi
  simp only [Set.mem_setOf_eq, not_not] at hi
  exact hf i hi

/-- **Cardinality bound (row side).** If `x` is an extreme
optimal row strategy at value `V`, the number of rows in its support is at most one more
than the number of columns tight at `x`. Proof: package
`eq_zero_of_extreme_optimalRow`'s hypotheses as an explicit `LinearMap` `g` from
`x`'s-support-indexed directions `d` to `(∑ d, tight-column payoffs of d)`; its
injectivity (that lemma) forces, via rank-nullity (`LinearMap.finrank_le_finrank_of_injective`),
the domain dimension `|support x|` to be at most the codomain dimension
`1 + |tight columns|`. -/
theorem card_support_le_card_tightCol_of_extreme {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A V)) :
    Fintype.card {i : I // x i ≠ 0} ≤ Fintype.card {j : J // ∑ i, x i * A i j = V} + 1 := by
  classical
  let g : ({i : I // x i ≠ 0} → ℝ) →ₗ[ℝ]
      ℝ × ({j : J // ∑ i, x i * A i j = V} → ℝ) :=
    { toFun := fun d => (∑ i, d i, fun j => ∑ i, d i * A i j.val)
      map_add' := by
        intro d d'
        refine Prod.ext ?_ (funext fun j => ?_)
        · simp [Finset.sum_add_distrib]
        · simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c d
        refine Prod.ext ?_ (funext fun j => ?_)
        · simp [Finset.mul_sum]
        · simp [Finset.mul_sum, mul_assoc] }
  have hginj : Function.Injective g := by
    intro d d' hdd'
    have hz : g (d - d') = 0 := by rw [map_sub, hdd', sub_self]
    set e : {i : I // x i ≠ 0} → ℝ := d - d' with hedef
    have hz1 : ∑ i, e i = 0 := congrArg Prod.fst hz
    have hz2 : ∀ j : {j : J // ∑ i, x i * A i j = V}, ∑ i, e i * A i j.val = 0 := fun j =>
      congrFun (congrArg Prod.snd hz) j
    set extendR : I → ℝ := fun i => if h : x i ≠ 0 then e ⟨i, h⟩ else 0 with hextendRdef
    have hval : ∀ i : {i : I // x i ≠ 0}, extendR i.val = e i := fun i => by
      simp only [hextendRdef]; rw [dif_pos i.property]
    have hd_supp : ∀ i, x i = 0 → extendR i = 0 := by
      intro i hi; simp only [hextendRdef]; rw [dif_neg (by rw [hi]; simp)]
    have hd_sum : ∑ i, extendR i = 0 := by
      rw [sum_eq_sum_support extendR hd_supp]
      exact (Finset.sum_congr rfl fun i _ => hval i).trans hz1
    have hd_tight : ∀ j, ∑ i, x i * A i j = V → ∑ i, extendR i * A i j = 0 := by
      intro j htight
      have hf0 : ∀ i, x i = 0 → extendR i * A i j = 0 := fun i hi => by rw [hd_supp i hi, zero_mul]
      rw [sum_eq_sum_support (fun i => extendR i * A i j) hf0]
      have := hz2 ⟨j, htight⟩
      exact (Finset.sum_congr rfl fun i _ => by rw [hval i]).trans this
    have hextendR0 : extendR = 0 := eq_zero_of_extreme_optimalRow hx hd_supp hd_sum hd_tight
    have he0 : e = 0 := funext fun i => (hval i).symm.trans (congrFun hextendR0 i.val)
    exact sub_eq_zero.mp he0
  have hle := LinearMap.finrank_le_finrank_of_injective hginj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hle
  omega

/-- **Cardinality bound (column side).** If `y`
is an extreme optimal column strategy at value `V`, the number of columns in its support
is at most one more than the number of rows tight at `y`. -/
theorem card_support_le_card_tightRow_of_extreme {A : I → J → ℝ} {V : ℝ}
    {y : J → ℝ} (hy : y ∈ Set.extremePoints ℝ (optimalColStrategies A V)) :
    Fintype.card {j : J // y j ≠ 0} ≤ Fintype.card {i : I // ∑ j, y j * A i j = V} + 1 := by
  classical
  let g : ({j : J // y j ≠ 0} → ℝ) →ₗ[ℝ]
      ℝ × ({i : I // ∑ j, y j * A i j = V} → ℝ) :=
    { toFun := fun e => (∑ j, e j, fun i => ∑ j, e j * A i.val j)
      map_add' := by
        intro e e'
        refine Prod.ext ?_ (funext fun i => ?_)
        · simp [Finset.sum_add_distrib]
        · simp [Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c e
        refine Prod.ext ?_ (funext fun i => ?_)
        · simp [Finset.mul_sum]
        · simp [Finset.mul_sum, mul_assoc] }
  have hginj : Function.Injective g := by
    intro e e' hee'
    have hz : g (e - e') = 0 := by rw [map_sub, hee', sub_self]
    set d : {j : J // y j ≠ 0} → ℝ := e - e' with hddef
    have hz1 : ∑ j, d j = 0 := congrArg Prod.fst hz
    have hz2 : ∀ i : {i : I // ∑ j, y j * A i j = V}, ∑ j, d j * A i.val j.val = 0 := fun i =>
      congrFun (congrArg Prod.snd hz) i
    set extendC : J → ℝ := fun j => if h : y j ≠ 0 then d ⟨j, h⟩ else 0 with hextendCdef
    have hval : ∀ j : {j : J // y j ≠ 0}, extendC j.val = d j := fun j => by
      simp only [hextendCdef]; rw [dif_pos j.property]
    have hd_supp : ∀ j, y j = 0 → extendC j = 0 := by
      intro j hj; simp only [hextendCdef]; rw [dif_neg (by rw [hj]; simp)]
    have hd_sum : ∑ j, extendC j = 0 := by
      rw [sum_eq_sum_support extendC hd_supp]
      exact (Finset.sum_congr rfl fun j _ => hval j).trans hz1
    have hd_tight : ∀ i, ∑ j, y j * A i j = V → ∑ j, extendC j * A i j = 0 := by
      intro i htight
      have hf0 : ∀ j, y j = 0 → extendC j * A i j = 0 := fun j hj => by rw [hd_supp j hj, zero_mul]
      rw [sum_eq_sum_support (fun j => extendC j * A i j) hf0]
      have := hz2 ⟨i, htight⟩
      exact (Finset.sum_congr rfl fun j _ => by rw [hval j]).trans this
    have hextendC0 : extendC = 0 := eq_zero_of_extreme_optimalCol hy hd_supp hd_sum hd_tight
    have he0 : d = 0 := funext fun j => (hval j).symm.trans (congrFun hextendC0 j.val)
    exact sub_eq_zero.mp he0
  have hle := LinearMap.finrank_le_finrank_of_injective hginj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hle
  omega

end OptimalStrategies

/-! ### Bordered tight-constraint basis selection -/

/-- A finite separating family of linear functionals admits a basis subfamily
that contains a prescribed nonzero functional.

The family indexed by `Option T` consists of `f0` and the functionals `f j`.
Point separation says that it spans the dual. Extending the singleton
`{f0}` inside this finite spanning family produces a basis; the other `n`
basis elements give the embedding `e`. -/
theorem exists_bordered_subfamily
    {H T : Type*} [AddCommGroup H] [Module ℝ H]
    [FiniteDimensional ℝ H] [Finite T]
    (n : ℕ) (hdim : Module.finrank ℝ H = n + 1)
    (f0 : Module.Dual ℝ H) (f : T → Module.Dual ℝ H)
    (hf0 : f0 ≠ 0)
    (hsep : ∀ z, f0 z = 0 → (∀ j, f j z = 0) → z = 0) :
    ∃ e : Fin n ↪ T,
      ∀ z, f0 z = 0 → (∀ k, f (e k) z = 0) → z = 0 := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let family : Option T → Module.Dual ℝ H
    | none => f0
    | some j => f j
  have hfamily_span :
      Submodule.span ℝ (Set.range family) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_cases hz0 : f0 z = 0
    · have hfj : ∃ j, f j z ≠ 0 := by
        by_contra h
        push Not at h
        exact hz (hsep z hz0 h)
      obtain ⟨j, hj⟩ := hfj
      exact ⟨family (some j), ⟨some j, rfl⟩, hj⟩
    · exact ⟨family none, ⟨none, rfl⟩, hz0⟩
  have hsingle :
      LinearIndepOn ℝ family ({none} : Set (Option T)) := by
    rw [linearIndepOn_singleton_iff]
    exact hf0
  obtain ⟨b, _hbsub, hnone, hbspan, hbli⟩ :=
    exists_linearIndepOn_extension hsingle
      (show ({none} : Set (Option T)) ⊆ Set.univ from
        Set.subset_univ _)
  have hnoneb : none ∈ b := hnone (Set.mem_singleton none)
  let B := {k : Option T // k ∈ b}
  let S := {j : T // (some j : Option T) ∈ b}
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype S := Fintype.ofFinite S
  have himage :
      family '' b = Set.range (fun k : B => family k.val) := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k.val, k.property, rfl⟩
  have hbspan_top :
      Submodule.span ℝ
          (Set.range fun k : B => family k.val) = ⊤ := by
    apply top_unique
    rw [← hfamily_span]
    apply Submodule.span_le.mpr
    intro g hg
    obtain ⟨k, rfl⟩ := hg
    have hkspan :
        family k ∈ Submodule.span ℝ (family '' b) :=
      hbspan ⟨k, Set.mem_univ k, rfl⟩
    rwa [himage] at hkspan
  have hbli' :
      LinearIndependent ℝ (fun k : B => family k.val) :=
    hbli.linearIndependent
  let basis : Module.Basis B ℝ (Module.Dual ℝ H) :=
    Module.Basis.mk hbli' (by rw [hbspan_top])
  have hcardB : Fintype.card B = n + 1 := by
    rw [← Module.finrank_eq_card_basis basis,
      Subspace.dual_finrank_eq, hdim]
  let eOption : Option S ≃ B :=
    { toFun := fun
        | none => ⟨none, hnoneb⟩
        | some j => ⟨some j.val, j.property⟩
      invFun := fun k =>
        match hk : k.val with
        | none => none
        | some j => some ⟨j, by simpa [hk] using k.property⟩
      left_inv := by
        intro k
        cases k with
        | none => rfl
        | some j => rfl
      right_inv := by
        intro k
        rcases k with ⟨k, hk⟩
        cases k <;> rfl }
  have hcardS : Fintype.card S = n := by
    have hcard := Fintype.card_congr eOption
    rw [Fintype.card_option, hcardB] at hcard
    omega
  let eS : Fin n ≃ S :=
    (Fintype.equivFinOfCardEq hcardS).symm
  let e : Fin n ↪ T :=
    eS.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_⟩
  intro z hz0 hz
  apply hsep z hz0
  intro j
  let ev : Module.Dual ℝ H →ₗ[ℝ] ℝ :=
    { toFun := fun g => g z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hbker : family '' b ⊆ ev.ker := by
    intro g hg
    obtain ⟨k, hkb, rfl⟩ := hg
    change family k z = 0
    cases k with
    | none => exact hz0
    | some j' =>
        let sj : S := ⟨j', hkb⟩
        obtain ⟨k, hk⟩ := eS.surjective sj
        have hek : e k = j' := by
          change (eS k).val = j'
          exact congrArg Subtype.val hk
        simpa [hek] using hz k
  have hmem :
      family (some j) ∈ Submodule.span ℝ (family '' b) :=
    hbspan ⟨some j, Set.mem_univ _, rfl⟩
  exact
    (Submodule.span_le.mpr hbker hmem :
      family (some j) ∈ ev.ker)

section BorderedTightSelection

variable {I J : Type*} [Fintype I] [Fintype J]
  [Nonempty I] [Nonempty J]

/-- Tight payoff columns contain a square bordered basis on the support of an
extreme optimal row strategy.

The selected rows enumerate the support of `x`; the selected columns are
tight at `x`. The final conjunct is injectivity of the associated bordered
system: a zero-mass direction whose selected-column changes are all the same
scalar must have zero direction and zero scalar. -/
theorem exists_extreme_tight_bordered_submatrix
    (A : I → J → ℝ) :
    ∃ (r : ℕ) (_ : 0 < r)
      (rows : Fin r ↪ I) (cols : Fin r ↪ J)
      (x : I → ℝ),
      x ∈ Set.extremePoints ℝ
          (optimalRowStrategies A (MinimaxLoomis.lam0 A)) ∧
      (∀ i, x i ≠ 0 ↔ i ∈ Set.range rows) ∧
      (∀ j,
        ∑ i, x i * A i (cols j) =
          MinimaxLoomis.lam0 A) ∧
      ∀ (d : Fin r → ℝ) (t : ℝ),
        (∑ i, d i = 0) →
        (∀ j,
          ∑ i, d i * A (rows i) (cols j) = t) →
        d = 0 ∧ t = 0 := by
  classical
  let V := MinimaxLoomis.lam0 A
  obtain ⟨x, hx⟩ :=
    extremePoints_optimalRowStrategies_nonempty A
  obtain ⟨y, hy⟩ := optimalColStrategies_lam0_nonempty A
  have hxopt : x ∈ optimalRowStrategies A V :=
    extremePoints_subset hx
  let R := {i : I // x i ≠ 0}
  have hR : Nonempty R := by
    by_contra h
    have hxzero : x = 0 := by
      funext i
      by_contra hi
      exact h ⟨⟨i, hi⟩⟩
    have hxsum := hxopt.1.2
    rw [hxzero] at hxsum
    simp at hxsum
  let r := Fintype.card R
  have hr : 0 < r := Fintype.card_pos_iff.mpr hR
  let rowsEquiv : Fin r ≃ R :=
    (Fintype.equivFin R).symm
  let rows : Fin r ↪ I :=
    rowsEquiv.toEmbedding.trans
      (Function.Embedding.subtype _)
  have hrows :
      ∀ i, x i ≠ 0 ↔ i ∈ Set.range rows := by
    intro i
    constructor
    · intro hi
      let ri : R := ⟨i, hi⟩
      obtain ⟨k, hk⟩ := rowsEquiv.surjective ri
      refine ⟨k, ?_⟩
      change (rowsEquiv k).val = i
      exact congrArg Subtype.val hk
    · rintro ⟨k, rfl⟩
      exact (rowsEquiv k).property
  let T := {j : J // ∑ i, x i * A i j = V}
  let H := (R → ℝ) × ℝ
  let mass : Module.Dual ℝ H :=
    { toFun := fun z => ∑ i, z.1 i
      map_add' := by
        intro z z'
        change (∑ i, (z.1 i + z'.1 i)) =
          (∑ i, z.1 i) + ∑ i, z'.1 i
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c z
        change (∑ i, c * z.1 i) =
          c * ∑ i, z.1 i
        rw [Finset.mul_sum] }
  let tight : T → Module.Dual ℝ H := fun j =>
    { toFun := fun z =>
        (∑ i, z.1 i * A i.val j.val) - z.2
      map_add' := by
        intro z z'
        change
          (∑ i, (z.1 i + z'.1 i) * A i.val j.val) -
              (z.2 + z'.2) =
            ((∑ i, z.1 i * A i.val j.val) - z.2) +
              ((∑ i, z'.1 i * A i.val j.val) - z'.2)
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c z
        change
          (∑ i, (c * z.1 i) * A i.val j.val) -
              c * z.2 =
            c * ((∑ i, z.1 i * A i.val j.val) - z.2)
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        ring }
  have hmass : mass ≠ 0 := by
    intro hm
    let i0 : R := Classical.choice hR
    have hz := LinearMap.congr_fun hm
      ((Pi.single i0 1 : R → ℝ), (0 : ℝ))
    simp [mass] at hz
  have hsep :
      ∀ z : H, mass z = 0 →
        (∀ j, tight j z = 0) → z = 0 := by
    intro z hmassz htightz
    let d : I → ℝ := fun i =>
      if hi : x i ≠ 0 then z.1 ⟨i, hi⟩ else 0
    have hd_supp : ∀ i, x i = 0 → d i = 0 := by
      intro i hi
      simp [d, hi]
    have hd_on : ∀ i : R, d i.val = z.1 i := by
      intro i
      simp [d, i.property]
    have hd_sum : ∑ i, d i = 0 := by
      rw [sum_eq_sum_support d hd_supp]
      change (∑ i : R, z.1 i) = 0 at hmassz
      simpa only [hd_on] using hmassz
    have hd_tight :
        ∀ j, (∑ i, x i * A i j = V) →
          ∑ i, d i * A i j = z.2 := by
      intro j hj
      rw [sum_eq_sum_support (fun i => d i * A i j)
        (fun i hi => by
          rw [hd_supp i hi, zero_mul])]
      have hzj := htightz ⟨j, hj⟩
      change
        (∑ i : R, z.1 i * A i.val j) - z.2 = 0 at hzj
      simpa only [hd_on] using sub_eq_zero.mp hzj
    obtain ⟨hd, ht⟩ :=
      eq_zero_of_extreme_optimalRow_bordered hx hy
        hd_supp hd_sum hd_tight
    apply Prod.ext
    · funext i
      have hi := congrFun hd i.val
      simpa [d, i.property] using hi
    · exact ht
  have hdim : Module.finrank ℝ H = r + 1 := by
    simp [H, r, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card]
  obtain ⟨colsT, hcolsT⟩ :=
    exists_bordered_subfamily r hdim
      mass tight hmass hsep
  let cols : Fin r ↪ J :=
    colsT.trans (Function.Embedding.subtype _)
  have hcols :
      ∀ j, ∑ i, x i * A i (cols j) = V := by
    intro j
    exact (colsT j).property
  refine
    ⟨r, hr, rows, cols, x, hx, hrows, hcols, ?_⟩
  intro d t hd_sum hd_tight
  let z : H := (fun i => d (rowsEquiv.symm i), t)
  have hz0 : mass z = 0 := by
    change ∑ i : R, d (rowsEquiv.symm i) = 0
    rw [rowsEquiv.symm.sum_comp]
    exact hd_sum
  have hztight : ∀ k, tight (colsT k) z = 0 := by
    intro k
    change
      (∑ i : R,
        d (rowsEquiv.symm i) *
          A i.val (colsT k).val) - t = 0
    have hreindex :
        (∑ i : R,
          d (rowsEquiv.symm i) *
            A i.val (colsT k).val) =
          ∑ i : Fin r,
            d i * A (rowsEquiv i).val (colsT k).val := by
      simpa using rowsEquiv.symm.sum_comp
        (fun i : Fin r =>
          d i * A (rowsEquiv i).val (colsT k).val)
    rw [hreindex]
    apply sub_eq_zero.mpr
    have hdt := hd_tight k
    change
      (∑ i : Fin r,
        d i * A (rowsEquiv i).val (colsT k).val) = t at hdt
    exact hdt
  have hz := hcolsT z hz0 hztight
  constructor
  · funext i
    have hi :=
      congrArg (fun z : H => z.1 (rowsEquiv i)) hz
    simpa [z] using hi
  · exact congrArg Prod.snd hz

end BorderedTightSelection

/-- **Reindexing a sum along an embedding whose range is exactly a support.** If
`e : Fin r ↪ κ` enumerates `z`'s support exactly (`z k ≠ 0 ↔ k ∈ Set.range e`) and `f`
vanishes off `z`'s support, then summing `f ∘ e` over `Fin r` recovers the sum of `f` over
all of `κ`. Used by kernel reassembly to transport tightness/normalisation
facts about a strategy `z`, stated as sums over the ambient type `κ`, onto a
`Fin r`-indexed enumeration of `z`'s support. -/
theorem sum_embedding_eq_sum_of_range_eq_support {κ : Type*} [Fintype κ] {z : κ → ℝ}
    {r : ℕ} (e : Fin r ↪ κ) (he : ∀ k, z k ≠ 0 → k ∈ Set.range e)
    (f : κ → ℝ) (hf : ∀ k, z k = 0 → f k = 0) :
    ∑ i, f (e i) = ∑ k, f k := by
  have h1 : ∑ k ∈ Finset.univ.map e, f k = ∑ i, f (e i) := Finset.sum_map _ _ _
  have h2 : ∑ k ∈ Finset.univ.map e, f k = ∑ k, f k := by
    apply Fintype.sum_subset
    intro k hk
    rw [Finset.mem_map]
    obtain ⟨i, hi⟩ := he k (fun hz => hk (hf k hz))
    exact ⟨i, Finset.mem_univ i, hi⟩
  rw [← h1, h2]

/-- **Bordered-kernel reassembly from one support and tight columns.**
The support restriction is a simplex and equalizes the selected columns.
Bordered injectivity then supplies a nonzero determinant denominator and the
kernel identity. -/
theorem borderedKernel_of_tight_support
    {I J : Type*} [Fintype I]
    {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ optimalRowStrategies A V)
    {r : ℕ} (hr : 0 < r)
    (rows : Fin r ↪ I) (cols : Fin r ↪ J)
    (hrows : ∀ i, x i ≠ 0 ↔ i ∈ Set.range rows)
    (hcols : ∀ j, ∑ i, x i * A i (cols j) = V)
    (hborder : ∀ (d : Fin r → ℝ) (t : ℝ),
      (∑ i, d i = 0) →
      (∀ j, ∑ i, d i * A (rows i) (cols j) = t) →
      d = 0 ∧ t = 0) :
    let B := (Matrix.of A).submatrix rows cols
    (borderedMatrix B).det ≠ 0 ∧
      V * (borderedMatrix B).det = B.det := by
  classical
  let B := (Matrix.of A).submatrix rows cols
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hnonneg : ∀ i : Fin r, 0 ≤ x (rows i) :=
    fun i => hx.1.1 (rows i)
  have hsum : ∑ i : Fin r, x (rows i) = 1 := by
    rw [sum_embedding_eq_sum_of_range_eq_support rows
      (fun i hi => (hrows i).mp hi) x (fun _ hk => hk)]
    exact hx.1.2
  let xr : stdSimplex ℝ (Fin r) :=
    ⟨fun i => x (rows i), hnonneg, hsum⟩
  have hequal :
      ∀ j : Fin r, wsum xr (fun i => B i j) = V := by
    intro j
    change ∑ i : Fin r, x (rows i) * B i j = V
    simp only [B, Matrix.submatrix_apply, Matrix.of_apply]
    rw [sum_embedding_eq_sum_of_range_eq_support rows
      (fun i hi => (hrows i).mp hi)
      (fun i => x i * A i (cols j))
      (fun _ hk => by rw [hk, zero_mul])]
    exact hcols j
  exact borderedKernelIdentity B xr V hequal hborder

/-- **General bordered Shapley--Snow kernel theorem.**
Every nonempty finite matrix game has a square submatrix whose bordered
determinant is nonzero and satisfies the value/determinant identity. -/
theorem exists_bordered_kernel
    {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (A : I → J → ℝ) :
    ∃ (r : ℕ) (_ : 0 < r)
      (rows : Fin r ↪ I) (cols : Fin r ↪ J),
      let B := (Matrix.of A).submatrix rows cols
      (borderedMatrix B).det ≠ 0 ∧
        MinimaxLoomis.lam0 A * (borderedMatrix B).det =
          B.det := by
  obtain
    ⟨r, hr, rows, cols, x, hx, hrows, hcols, hborder⟩ :=
      exists_extreme_tight_bordered_submatrix A
  have hxopt :
      x ∈ optimalRowStrategies A (MinimaxLoomis.lam0 A) :=
    extremePoints_subset hx
  obtain ⟨hne, hid⟩ :=
    borderedKernel_of_tight_support
      hxopt hr rows cols hrows hcols hborder
  exact ⟨r, hr, rows, cols, hne, hid⟩

/-- **Kernel reassembly from one extreme support and tight columns.**
If `rows` enumerates the support of an optimal row strategy `x`, every selected
column is tight at value `V`, and the selected square submatrix has nonzero
adjugate sum, then that submatrix satisfies the Shapley--Snow identity at `V`.

Only the left equalizing strategy is needed for the determinant identity; no
enumeration of a column strategy's support is required. -/
theorem kernel_of_tight_support_of_adjugateSum_ne
    {I J : Type*} [Fintype I]
    {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ optimalRowStrategies A V)
    {r : ℕ} (hr : 0 < r)
    (rows : Fin r ↪ I) (cols : Fin r ↪ J)
    (hrows : ∀ i, x i ≠ 0 ↔ i ∈ Set.range rows)
    (hcols : ∀ j, ∑ i, x i * A i (cols j) = V)
    (hS : (∑ i, ∑ j,
      ((Matrix.of A).submatrix rows cols).adjugate i j) ≠ 0) :
    (∑ i, ∑ j,
        ((Matrix.of A).submatrix rows cols).adjugate i j) ≠ 0 ∧
      V * (∑ i, ∑ j,
        ((Matrix.of A).submatrix rows cols).adjugate i j) =
          ((Matrix.of A).submatrix rows cols).det := by
  classical
  let B := (Matrix.of A).submatrix rows cols
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hnonneg : ∀ i : Fin r, 0 ≤ x (rows i) :=
    fun i => hx.1.1 (rows i)
  have hsum : ∑ i : Fin r, x (rows i) = 1 := by
    rw [sum_embedding_eq_sum_of_range_eq_support rows
      (fun i hi => (hrows i).mp hi) x (fun _ hk => hk)]
    exact hx.1.2
  let xr : stdSimplex ℝ (Fin r) :=
    ⟨fun i => x (rows i), hnonneg, hsum⟩
  have hequal :
      ∀ j : Fin r, wsum xr (fun i => B i j) = V := by
    intro j
    change ∑ i : Fin r, x (rows i) * B i j = V
    simp only [B, Matrix.submatrix_apply, Matrix.of_apply]
    rw [sum_embedding_eq_sum_of_range_eq_support rows
      (fun i hi => (hrows i).mp hi)
      (fun i => x i * A i (cols j))
      (fun _ hk => by rw [hk, zero_mul])]
    exact hcols j
  exact
    ⟨hS, kernelIdentity_of_left_equalizing B xr V hequal⟩

section SquareKernelReassembly

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

omit [Nonempty I] in
/-- **Kernel reassembly from matching supports.** If `x`, `y` are extreme optimal
strategies at `V := lam0 A` whose supports are *exactly* enumerated by embeddings `rows`,
`cols` of a common size `r` (`hrows`, `hcols`), and the resulting square submatrix
has nonzero adjugate sum (`hB`), then that submatrix IS a Shapley–Snow
kernel for `A`: the restrictions `x ∘ rows`, `y ∘ cols` are themselves mixed strategies
(they inherit non-negativity from `x`, `y`, and sum to `1` since `rows`/`cols` exactly
enumerate the support, so no mass is lost), and they form an *equalizing pair* for the
submatrix at value `V` (complementary slackness, `tight_of_optimal_row_support` /
`tight_of_optimal_col_support`, applied since every row of `rows`/column of `cols` lies in
the support of `x`/`y`, hence in the region where the corresponding player's tightness is
known). `exists_kernel_of_equalizing_of_adjugateSum_ne` then gives
`lam0 (submatrix) = V`, and
`V = lam0 A` by construction, yielding exactly the Shapley–Snow determinant identity for
`A` itself (not just for the submatrix in isolation) — the "reassembly" step. -/
theorem exists_kernel_of_extreme_matching_support {A : I → J → ℝ}
    {x : I → ℝ} (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A (MinimaxLoomis.lam0 A)))
    {y : J → ℝ} (hy : y ∈ Set.extremePoints ℝ (optimalColStrategies A (MinimaxLoomis.lam0 A)))
    {r : ℕ} (rows : Fin r ↪ I) (cols : Fin r ↪ J)
    (hrows : ∀ i, x i ≠ 0 ↔ i ∈ Set.range rows)
    (hcols : ∀ j, y j ≠ 0 ↔ j ∈ Set.range cols)
    (hB : (∑ i, ∑ j,
      ((Matrix.of A).submatrix rows cols).adjugate i j) ≠ 0) :
    ∃ (r' : ℕ) (_ : 0 < r') (rows' : Fin r' ↪ I) (cols' : Fin r' ↪ J),
      (∑ i, ∑ j, ((Matrix.of A).submatrix rows' cols').adjugate i j) ≠ 0 ∧
        MinimaxLoomis.lam0 A * (∑ i, ∑ j, ((Matrix.of A).submatrix rows' cols').adjugate i j)
          = ((Matrix.of A).submatrix rows' cols').det := by
  classical
  set V := MinimaxLoomis.lam0 A with hV
  set B := (Matrix.of A).submatrix rows cols with hBdef
  have hxmem : x ∈ optimalRowStrategies A V := extremePoints_subset hx
  have hymem : y ∈ optimalColStrategies A V := extremePoints_subset hy
  have hxs := hxmem.1
  have hys := hymem.1
  have hxne : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : (∑ i, x i) = 0 := Finset.sum_eq_zero fun i _ => hcon i
    rw [hxs.2] at hz
    norm_num at hz
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · exfalso
      subst hr0
      obtain ⟨i0, hi0⟩ := hxne
      obtain ⟨i', -⟩ := (hrows i0).mp hi0
      exact i'.elim0
    · exact hr0
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hx'nonneg : ∀ i' : Fin r, 0 ≤ x (rows i') := fun i' => hxs.1 (rows i')
  have hy'nonneg : ∀ j' : Fin r, 0 ≤ y (cols j') := fun j' => hys.1 (cols j')
  have hx'sum : ∑ i' : Fin r, x (rows i') = 1 := by
    rw [sum_embedding_eq_sum_of_range_eq_support rows (fun i hi => (hrows i).mp hi) x
      (fun k hk => hk)]
    exact hxs.2
  have hy'sum : ∑ j' : Fin r, y (cols j') = 1 := by
    rw [sum_embedding_eq_sum_of_range_eq_support cols (fun j hj => (hcols j).mp hj) y
      (fun k hk => hk)]
    exact hys.2
  let xr : stdSimplex ℝ (Fin r) := ⟨fun i' => x (rows i'), hx'nonneg, hx'sum⟩
  let yr : stdSimplex ℝ (Fin r) := ⟨fun j' => y (cols j'), hy'nonneg, hy'sum⟩
  have hxr_tight : ∀ j' : Fin r, wsum xr (fun i' => B i' j') = V := by
    intro j'
    have hyj' : y (cols j') ≠ 0 := (hcols (cols j')).mpr ⟨j', rfl⟩
    have htight := tight_of_optimal_col_support hxmem hymem hyj'
    change (∑ i' : Fin r, x (rows i') * B i' j') = V
    simp only [hBdef, Matrix.submatrix_apply, Matrix.of_apply]
    rw [sum_embedding_eq_sum_of_range_eq_support rows (fun i hi => (hrows i).mp hi)
      (fun i => x i * A i (cols j')) (fun k hk => by rw [hk, zero_mul])]
    exact htight
  have hyr_tight : ∀ i' : Fin r, wsum yr (fun j' => B i' j') = V := by
    intro i'
    have hxi' : x (rows i') ≠ 0 := (hrows (rows i')).mpr ⟨i', rfl⟩
    have htight := tight_of_optimal_row_support hxmem hymem hxi'
    change (∑ j' : Fin r, y (cols j') * B i' j') = V
    simp only [hBdef, Matrix.submatrix_apply, Matrix.of_apply]
    rw [sum_embedding_eq_sum_of_range_eq_support cols (fun j hj => (hcols j).mp hj)
      (fun j => y j * A (rows i') j) (fun k hk => by rw [hk, zero_mul])]
    exact htight
  obtain ⟨hlamB, hadjne, heq⟩ :=
    exists_kernel_of_equalizing_of_adjugateSum_ne
      B xr yr V hxr_tight hyr_tight hB
  refine ⟨r, hr, rows, cols, hadjne, ?_⟩
  change MinimaxLoomis.lam0 A * (∑ i, ∑ j, B.adjugate i j) = B.det
  rw [← hV, ← hlamB]
  exact heq

end SquareKernelReassembly

/-! ### Bordered and adjugate kernel interfaces

For an extreme optimal row strategy, complementary slackness and
`eq_zero_of_extreme_optimalRow_bordered` show that the mass functional
together with all tight-column functionals separates support directions and
the value coordinate. `exists_bordered_subfamily` selects a basis containing
the mass functional. Its other basis elements are exactly the square family
of tight columns produced by
`exists_extreme_tight_bordered_submatrix`.

`borderedKernelIdentity` identifies the Cramer denominator of that basis as
`det (borderedMatrix B)`. The capstone `exists_bordered_kernel` therefore
provides, for every nonempty finite matrix game,

```
det (borderedMatrix B) ≠ 0
lam0 A * det (borderedMatrix B) = det B.
```

This is the kernel interface consumed by
`exists_nonzero_poly_of_borderedKernel`, so that theorem has no separate
matrix-game existence hypothesis.

The adjugate API is also available. A nonzero adjugate sum and a left
equalizing strategy give the same value/determinant relation through
`kernel_of_tight_support_of_adjugateSum_ne`. The matching-support theorem
`exists_kernel_of_extreme_matching_support` is a symmetric reassembly
variant. `singular_equalizing_kernel_example` records that `B.det ≠ 0` is not
the relevant condition: a singular payoff submatrix can have a nonsingular
bordered system. -/

/-! ### Bivariate evaluation

`Polynomial (Polynomial ℝ)` is the bivariate polynomial ring: the outer variable is
`Polynomial.X` ("`v`"), the coefficients live in `Polynomial ℝ` ("`ℝ[λ]`"). -/

/-- Evaluate a bivariate polynomial at a point `(l, v) : ℝ × ℝ`: evaluate every
coefficient (an element of `ℝ[λ]`) at `l`, then evaluate the resulting real polynomial
(in the outer variable) at `v`. Packaged as a ring homomorphism so that evaluation
commutes with `det`/`adjugate`/`Finset.sum`/`Finset.prod` for free. -/
noncomputable def bivEval (l v : ℝ) : Polynomial (Polynomial ℝ) →+* ℝ :=
  (Polynomial.evalRingHom v).comp (Polynomial.mapRingHom (Polynomial.evalRingHom l))

@[simp]
theorem bivEval_X (l v : ℝ) : bivEval l v Polynomial.X = v := by
  simp [bivEval]

@[simp]
theorem bivEval_C_C (l v c : ℝ) :
    bivEval l v (Polynomial.C (Polynomial.C c)) = c := by
  simp [bivEval]

/-! ### Stage 2, abstract engine

The clean, general statement: a finite covering family of candidate polynomials, one of
which is nonzero and vanishes at each parameter's specialisation, packages into a single
fixed nonzero polynomial vanishing at every parameter. This is the algebraic core of the
parametric Shapley–Snow corollary and does not itself reference matrix games. -/

/-- **Finite covering-family construction.** If, for every `λ ∈ S`, some member of a
finite family `F` of bivariate polynomials is both nonzero and vanishes at
`(λ, val λ)`, then the product of the (finitely many) nonzero members of `F` is a single
polynomial that is itself nonzero and vanishes at `(λ, val λ)` for every `λ ∈ S`. -/
theorem exists_nonzero_poly_of_forall_mem_exists {ι : Type*} [Finite ι]
    (F : ι → Polynomial (Polynomial ℝ)) (S : Set ℝ) (val : ℝ → ℝ)
    (hcov : ∀ l ∈ S, ∃ k, F k ≠ 0 ∧ bivEval l (val l) (F k) = 0) :
    ∃ P : Polynomial (Polynomial ℝ), P ≠ 0 ∧ ∀ l ∈ S, bivEval l (val l) P = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∏ k, (if F k ≠ 0 then F k else 1), ?_, fun l hl => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k _
    split_ifs with h
    · exact h
    · exact one_ne_zero
  · obtain ⟨k, hk0, hkeval⟩ := hcov l hl
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [if_pos hk0]
    exact hkeval

/-! ### `bivEval` commutes with determinant, bordered determinant, and adjugate

Entrywise consequences of `RingHom.map_det` / `RingHom.map_adjugate`, phrased so they
compose directly with `Finset.sum` over matrix entries. -/

/-- `bivEval` commutes with `det` on a square bivariate-polynomial matrix. -/
theorem bivEval_det {r : ℕ} (l v : ℝ) (B : Matrix (Fin r) (Fin r) (Polynomial (Polynomial ℝ))) :
    bivEval l v B.det = (B.map (bivEval l v)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

/-- `bivEval` commutes with the determinant of the bordered matrix. -/
theorem bivEval_borderedMatrix_det
    {r : ℕ} (l v : ℝ)
    (B : Matrix (Fin r) (Fin r)
      (Polynomial (Polynomial ℝ))) :
    bivEval l v (borderedMatrix B).det =
      (borderedMatrix (B.map (bivEval l v))).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply,
    map_borderedMatrix]

/-- `bivEval` commutes with `adjugate`, entrywise, on a square bivariate-polynomial
matrix. -/
theorem bivEval_adjugate_apply {r : ℕ} (l v : ℝ)
    (B : Matrix (Fin r) (Fin r) (Polynomial (Polynomial ℝ))) (i j : Fin r) :
    bivEval l v (B.adjugate i j) = (B.map (bivEval l v)).adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (bivEval l v) B) i) j
  simpa [RingHom.mapMatrix_apply] using h

/-- `bivEval` commutes with the total adjugate sum of a square bivariate-polynomial
matrix. -/
theorem bivEval_sum_adjugate {r : ℕ} (l v : ℝ)
    (B : Matrix (Fin r) (Fin r) (Polynomial (Polynomial ℝ))) :
    bivEval l v (∑ i, ∑ j, B.adjugate i j) = ∑ i, ∑ j, (B.map (bivEval l v)).adjugate i j := by
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => bivEval_adjugate_apply l v B i j

/-! ### Stage 2, matrix-game corollary

The concrete instantiation: shapes `(r, rows, cols)` with `r ≤ m` index the finitely
many candidate kernel submatrices of an `m × n` bivariate matrix family. -/

/-- The index type of candidate kernel shapes: a size `r ≤ m` together with row/column
embeddings. Finite because `Fin r.val ↪ Fin m` and `Fin r.val ↪ Fin n` are finite for
every `r`, and there are finitely many `r ≤ m`. -/
def KernelShape (m n : ℕ) : Type :=
  Σ r : Fin (m + 1), (Fin r.val ↪ Fin m) × (Fin r.val ↪ Fin n)

noncomputable instance instFiniteKernelShape (m n : ℕ) : Finite (KernelShape m n) := by
  unfold KernelShape
  infer_instance

/-- The bivariate kernel polynomial `F_B := det B - X * (∑ adjugate B)` associated to a
kernel shape, for a bivariate matrix family `E`. -/
noncomputable def kernelPoly {m n : ℕ} (E : Fin m → Fin n → Polynomial (Polynomial ℝ)) :
    KernelShape m n → Polynomial (Polynomial ℝ) :=
  fun ⟨_r, rows, cols⟩ =>
    let B := (Matrix.of E).submatrix rows cols
    B.det - Polynomial.X * ∑ i, ∑ j, B.adjugate i j

/-- The bordered-kernel polynomial
`det B - X * det (borderedMatrix B)` associated to a kernel shape. -/
noncomputable def borderedKernelPoly
    {m n : ℕ}
    (E : Fin m → Fin n → Polynomial (Polynomial ℝ)) :
    KernelShape m n → Polynomial (Polynomial ℝ) :=
  fun ⟨_r, rows, cols⟩ =>
    let B := (Matrix.of E).submatrix rows cols
    B.det - Polynomial.X * (borderedMatrix B).det

/-- **Parametric matrix-game corollary using bordered kernels.**
The general bordered Shapley--Snow theorem supplies the kernel at every
parameter, so no matrix-game kernel hypothesis is exposed. The genericity
hypothesis only rules out a candidate polynomial being identically zero. -/
theorem exists_nonzero_poly_of_borderedKernel
    {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (E : Fin m → Fin n → Polynomial (Polynomial ℝ))
    (S : Set ℝ) (val : ℝ → ℝ)
    (hval : ∀ l ∈ S, val l =
      MinimaxLoomis.lam0
        (fun i j => bivEval l (val l) (E i j)))
    (hgen :
      ∀ (r : ℕ) (rows : Fin r ↪ Fin m)
        (cols : Fin r ↪ Fin n),
        (borderedMatrix
          ((Matrix.of E).submatrix rows cols)).det ≠ 0 →
        ((Matrix.of E).submatrix rows cols).det -
            Polynomial.X *
              (borderedMatrix
                ((Matrix.of E).submatrix rows cols)).det ≠ 0) :
    ∃ P : Polynomial (Polynomial ℝ),
      P ≠ 0 ∧ ∀ l ∈ S, bivEval l (val l) P = 0 := by
  apply exists_nonzero_poly_of_forall_mem_exists
    (borderedKernelPoly E) S val
  intro l hl
  set Al : Matrix (Fin m) (Fin n) ℝ :=
    fun i j => bivEval l (val l) (E i j) with hAl
  obtain ⟨r, hr, rows, cols, hborder, hval_eq⟩ :=
    exists_bordered_kernel Al
  have hrm : r ≤ m := by
    have := Fintype.card_le_of_embedding rows
    simpa using this
  have hcommute :
      ((Matrix.of E).submatrix rows cols).map
          (bivEval l (val l)) =
        Al.submatrix rows cols := by
    rw [← Matrix.submatrix_map]
    rfl
  refine
    ⟨⟨⟨r, by omega⟩, rows, cols⟩, ?_, ?_⟩
  · apply hgen
    intro hz
    apply hborder
    have heval := congrArg (bivEval l (val l)) hz
    rw [map_zero, bivEval_borderedMatrix_det,
      hcommute] at heval
    exact heval
  · show
      bivEval l (val l)
        (borderedKernelPoly E
          ⟨⟨r, by omega⟩, rows, cols⟩) = 0
    unfold borderedKernelPoly
    simp only [map_sub, map_mul, bivEval_X,
      bivEval_det, bivEval_borderedMatrix_det, hcommute]
    have hAlval : MinimaxLoomis.lam0 Al = val l :=
      (hval l hl).symm
    rw [hAlval] at hval_eq
    apply sub_eq_zero.mpr
    change
      val l *
          (borderedMatrix
            (Al.submatrix rows cols)).det =
        (Al.submatrix rows cols).det at hval_eq
    exact hval_eq.symm

/-- **Stage 2, concrete form.** The parametric Shapley–Snow corollary for a bivariate
`m × n` matrix family `E`, a self-referential value function `val`, and a genericity
hypothesis `hgen` ruling out the tautological degeneracy discussed above. The Stage-1
kernel property is the explicit hypothesis `hkernel`; the conclusion is the parametric
polynomial consequence of that interface. -/
theorem exists_nonzero_poly_of_kernel {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (E : Fin m → Fin n → Polynomial (Polynomial ℝ)) (S : Set ℝ) (val : ℝ → ℝ)
    (hval : ∀ l ∈ S, val l =
      MinimaxLoomis.lam0 (fun i j => bivEval l (val l) (E i j)))
    (hkernel : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      ∃ (r : ℕ) (_ : 0 < r) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
        (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j) ≠ 0 ∧
          MinimaxLoomis.lam0 A * (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j)
            = (A.submatrix rows cols).det)
    (hgen : ∀ (r : ℕ) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
      (∑ i, ∑ j, ((Matrix.of E).submatrix rows cols).adjugate i j) ≠ 0 →
        ((Matrix.of E).submatrix rows cols).det
            - Polynomial.X * ∑ i, ∑ j, ((Matrix.of E).submatrix rows cols).adjugate i j
          ≠ 0) :
    ∃ P : Polynomial (Polynomial ℝ), P ≠ 0 ∧ ∀ l ∈ S, bivEval l (val l) P = 0 := by
  apply exists_nonzero_poly_of_forall_mem_exists (kernelPoly E) S val
  intro l hl
  set Al : Matrix (Fin m) (Fin n) ℝ := fun i j => bivEval l (val l) (E i j) with hAl
  obtain ⟨r, hr, rows, cols, hsum, hval_eq⟩ := hkernel Al
  have hrm : r ≤ m := by
    have := Fintype.card_le_of_embedding rows
    simpa using this
  have hcommute :
      ((Matrix.of E).submatrix rows cols).map (bivEval l (val l)) = Al.submatrix rows cols := by
    rw [← Matrix.submatrix_map]
    rfl
  refine ⟨⟨⟨r, by omega⟩, rows, cols⟩, ?_, ?_⟩
  · apply hgen
    -- The abstract adjugate-sum polynomial is nonzero because its evaluation at
    -- `(l, val l)` (which computes the adjugate sum of `Al.submatrix rows cols`) is.
    intro hz
    apply hsum
    have := congrArg (bivEval l (val l)) hz
    rw [map_zero, bivEval_sum_adjugate, hcommute] at this
    exact this
  · show bivEval l (val l) (kernelPoly E ⟨⟨r, by omega⟩, rows, cols⟩) = 0
    unfold kernelPoly
    simp only [map_sub, map_mul, bivEval_X, bivEval_sum_adjugate, bivEval_det, hcommute]
    have hAlval : MinimaxLoomis.lam0 Al = val l := (hval l hl).symm
    rw [hAlval] at hval_eq
    linarith [hval_eq]

/-! ### Stage 3, the discounted-family application interface

The "one live state" zero-sum discounted stochastic game: reward matrix `r`, transition
weight matrix `P`, discount factor `λ ∈ (0, 1)`, and a self-referential continuation
value `w λ` satisfying the Shapley fixed-point equation
`w λ = lam0 (fun i j => (1 - λ) * r i j + λ * P i j * w λ)`. This packages the abstract
Stage 2 corollary into that concrete affine-in-`(λ, v)` entry family. -/

/-- The bivariate polynomial entry of a one-live-state discounted zero-sum game: reward
`r i j` blended with discounted continuation `P i j * v`, as a function of the outer
variable `λ` (`Polynomial.C Polynomial.X`) and the value variable `v` (`Polynomial.X`). -/
noncomputable def discountedEntry {m n : ℕ} (r P : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Polynomial (Polynomial ℝ) :=
  Polynomial.C (Polynomial.C (r i j)) * (1 - Polynomial.C Polynomial.X)
    + Polynomial.C Polynomial.X * Polynomial.C (Polynomial.C (P i j)) * Polynomial.X

@[simp]
theorem bivEval_discountedEntry {m n : ℕ} (r P : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (l v : ℝ) :
    bivEval l v (discountedEntry r P i j) = (1 - l) * r i j + l * P i j * v := by
  simp [discountedEntry, bivEval]
  ring

/-! ### A checkable sufficient condition replacing `hgen` for the discounted family

Setting the value variable `v` to `0` is itself a ring homomorphism
`Polynomial (Polynomial ℝ) →+* Polynomial ℝ`, under which the `v * Σadj(B)` term of
`kernelPoly` vanishes and `det B` reduces to `(1 - λ)^sz` times the determinant of the
*reward* submatrix (a real number, lifted to `ℝ[λ]`). Both factors are visibly nonzero
in the domain `ℝ[λ]` whenever the reward submatrix is nonsingular, giving a checkable
sufficient condition for `kernelPoly ≠ 0`. -/

/-- Setting `v = 0` sends a discounted entry to `(1 - λ) * r i j`. -/
theorem evalZero_discountedEntry {m n : ℕ} (r P : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Polynomial.evalRingHom (0 : Polynomial ℝ) (discountedEntry r P i j)
      = (1 - Polynomial.X) * Polynomial.C (r i j) := by
  simp [discountedEntry, Polynomial.coe_evalRingHom]
  ring

/-- Setting `v = 0` sends the kernel polynomial of a discounted-family shape to
`(1 - λ)^sz` times the (real, lifted to `ℝ[λ]`) determinant of the reward submatrix. -/
theorem evalZero_kernelPoly_discountedEntry {m n : ℕ} (r P : Fin m → Fin n → ℝ)
    {sz : ℕ} (hlt : sz < m + 1) (rows : Fin sz ↪ Fin m) (cols : Fin sz ↪ Fin n) :
    Polynomial.evalRingHom (0 : Polynomial ℝ)
        (kernelPoly (discountedEntry r P) ⟨⟨sz, hlt⟩, rows, cols⟩)
      = (1 - Polynomial.X) ^ sz * Polynomial.C (((Matrix.of r).submatrix rows cols).det) := by
  change Polynomial.evalRingHom (0 : Polynomial ℝ)
      (((Matrix.of (discountedEntry r P)).submatrix rows cols).det
        - Polynomial.X *
          ∑ i, ∑ j, ((Matrix.of (discountedEntry r P)).submatrix rows cols).adjugate i j)
      = (1 - Polynomial.X) ^ sz * Polynomial.C (((Matrix.of r).submatrix rows cols).det)
  have hX0 : Polynomial.evalRingHom (0 : Polynomial ℝ) Polynomial.X = 0 := by
    simp [Polynomial.coe_evalRingHom]
  rw [map_sub, map_mul, hX0, zero_mul, sub_zero, RingHom.map_det, RingHom.mapMatrix_apply,
    ← Matrix.submatrix_map]
  have hmap : (Matrix.of (discountedEntry r P)).map (Polynomial.evalRingHom (0 : Polynomial ℝ))
      = ((1 : Polynomial ℝ) - Polynomial.X) • (Matrix.of r).map Polynomial.C :=
    Matrix.ext fun i j => by
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact evalZero_discountedEntry r P i j
  rw [hmap, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.submatrix_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]

/-- **Sufficient condition replacing `hgen` for the discounted family.** If the reward
submatrix of a kernel shape has nonzero determinant, the associated `kernelPoly` is a
nonzero bivariate polynomial: its `v = 0` evaluation, `(1 - λ)^sz * C (det r_sub)`, is a
nonzero element of the domain `ℝ[λ]` (`1 - λ ≠ 0` and `det r_sub ≠ 0`), so `kernelPoly`
cannot be the zero polynomial. This is only a SUFFICIENT condition: a kernel shape whose
reward submatrix happens to be singular could still have `kernelPoly ≠ 0` via a
higher-degree-in-`v` coefficient, or Stage 1 might have selected a different,
nonsingular-reward shape for the same matrix. The theorem makes no claim for those
cases. -/
theorem kernelPoly_ne_zero_of_reward_det_ne_zero {m n : ℕ} (r P : Fin m → Fin n → ℝ)
    {sz : ℕ} (hlt : sz < m + 1) (rows : Fin sz ↪ Fin m) (cols : Fin sz ↪ Fin n)
    (hdet : ((Matrix.of r).submatrix rows cols).det ≠ 0) :
    kernelPoly (discountedEntry r P) ⟨⟨sz, hlt⟩, rows, cols⟩ ≠ 0 := by
  intro hz
  have heval := evalZero_kernelPoly_discountedEntry r P hlt rows cols
  rw [hz, map_zero] at heval
  have h1X : (1 - Polynomial.X : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval (0 : ℝ)) h
    simp at this
  have hCdet : Polynomial.C (((Matrix.of r).submatrix rows cols).det) ≠ (0 : Polynomial ℝ) :=
    Polynomial.C_ne_zero.mpr hdet
  exact (mul_ne_zero (pow_ne_zero sz h1X) hCdet) heval.symm

/-- **Stage 3.** The parametric Shapley–Snow corollary specialised to a one-live-state
discounted zero-sum stochastic game family: given the Shapley fixed-point property for
`w` on `(0, 1)` and the Stage-1 kernel property `hkernel`, strengthened with the
CHECKABLE conjunct "the reward submatrix of the kernel is nonsingular" in place of the
opaque genericity hypothesis `hgen` of `exists_nonzero_poly_of_kernel` (discharged via
`kernelPoly_ne_zero_of_reward_det_ne_zero` above) — there is a single nonzero bivariate
polynomial vanishing at `(λ, w λ)` for every discount factor `λ ∈ (0, 1)`. This is the
algebraic input for proving that discounted stochastic-game values are algebraic in the
discount factor.

The nonsingular-reward conjunct is a genuinely weaker, checkable ask than `hgen`: for a
concrete game it reduces to a single real-matrix determinant computation
(`norm_num`/`decide`), rather than a universally-quantified polynomial-nonvanishing
claim. It is still only sufficient, not necessary — see the docstring of
`kernelPoly_ne_zero_of_reward_det_ne_zero` for the singular-reward cases outside its
statement. -/
theorem exists_nonzero_poly_of_discounted {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (r P : Fin m → Fin n → ℝ) (w : ℝ → ℝ)
    (hw : ∀ l ∈ Set.Ioo (0 : ℝ) 1,
      w l = MinimaxLoomis.lam0 (fun i j => (1 - l) * r i j + l * P i j * w l))
    (hkernel : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      ∃ (sz : ℕ) (_ : 0 < sz) (rows : Fin sz ↪ Fin m) (cols : Fin sz ↪ Fin n),
        (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j) ≠ 0 ∧
          MinimaxLoomis.lam0 A * (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j)
            = (A.submatrix rows cols).det ∧
          ((Matrix.of r).submatrix rows cols).det ≠ 0) :
    ∃ Q : Polynomial (Polynomial ℝ), Q ≠ 0 ∧
      ∀ l ∈ Set.Ioo (0 : ℝ) 1, bivEval l (w l) Q = 0 := by
  apply exists_nonzero_poly_of_forall_mem_exists (kernelPoly (discountedEntry r P))
    (Set.Ioo (0 : ℝ) 1) w
  intro l hl
  set Al : Matrix (Fin m) (Fin n) ℝ := fun i j => (1 - l) * r i j + l * P i j * w l with hAl
  obtain ⟨sz, -, rows, cols, hsum, hval_eq, hreddet⟩ := hkernel Al
  have hszm : sz ≤ m := by
    have := Fintype.card_le_of_embedding rows
    simpa using this
  have hlt : sz < m + 1 := by omega
  have hmapAl : (Matrix.of (discountedEntry r P)).map (bivEval l (w l)) = Al := by
    ext i j
    simp [Matrix.map_apply, hAl, bivEval_discountedEntry]
  have hcommute :
      ((Matrix.of (discountedEntry r P)).submatrix rows cols).map (bivEval l (w l))
        = Al.submatrix rows cols := by
    rw [← Matrix.submatrix_map, hmapAl]
  refine ⟨⟨⟨sz, hlt⟩, rows, cols⟩,
    kernelPoly_ne_zero_of_reward_det_ne_zero r P hlt rows cols hreddet, ?_⟩
  show bivEval l (w l) (kernelPoly (discountedEntry r P) ⟨⟨sz, hlt⟩, rows, cols⟩) = 0
  unfold kernelPoly
  simp only [map_sub, map_mul, bivEval_X, bivEval_sum_adjugate, bivEval_det, hcommute]
  have hAlval : MinimaxLoomis.lam0 Al = w l := (hw l hl).symm
  rw [hAlval] at hval_eq
  linarith [hval_eq]

end ShapleySnow
