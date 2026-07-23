/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import Math.Minimax.MinimaxLoomis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Div

/-!
# Math.Minimax.ShapleySnow

The Shapley–Snow kernel theorem for finite matrix games, and its parametric corollary.

## Stage 1 (statement only — see the `TODO` block below)

For a matrix game `A : Matrix (Fin m) (Fin n) ℝ` the value `V := MinimaxLoomis.lam0 A`
satisfies a determinant identity over some square submatrix ("kernel") `B`:
`V * (∑ i j, B.adjugate i j) = B.det` with `∑ i j, B.adjugate i j ≠ 0`. This is the
1950 Shapley–Snow theorem. Its classical proof (extreme optimal strategies, tight payoff
equations on the support, nonsingularity of the bordered kernel system) is genuinely
substantial to formalise; it is recorded here as a precise `TODO` statement rather than
an unproved (`sorry`-laden) declaration, per this repository's "no `sorry`" rule.

## Stage 2 — the parametric product corollary

Given a family of matrices with entries that are bivariate polynomials
`E i j : Polynomial (Polynomial ℝ)` — outer variable `v` (`Polynomial.X`), coefficients
in `ℝ[λ]` — and a self-referential value function `val : ℝ → ℝ` with
`val λ = lam0 (fun i j => bivEval λ (val λ) (E i j))` for `λ` in some set `S`, Stage 1
(applied at each `λ`) produces, for each `λ`, a square "kernel" submatrix shape whose
associated bivariate polynomial `F_B := B.det - X * (∑ adjugate B)` vanishes at
`(λ, val λ)`. There are only finitely many possible kernel shapes (bounded by `m`, `n`),
so a single fixed polynomial — the product of the (finitely many, pairwise possibly
overlapping) nonzero `F_B` — vanishes at `(λ, val λ)` for every `λ ∈ S`.

The clean, fully general engine behind this argument is
`exists_nonzero_poly_of_forall_mem_exists` below: given *any* finite family of candidate
bivariate polynomials such that, for every parameter, at least one candidate is both
nonzero (as an abstract polynomial) and vanishes at that parameter's specialisation
point, their product is a single nonzero polynomial vanishing at every parameter.

### A statement adjustment, and why it is necessary

The concrete matrix-game instantiation (`exists_nonzero_poly_of_kernel`) additionally
carries a genericity hypothesis `hgen`, and takes the Stage-1 conclusion itself as an
explicit hypothesis `hkernel` (since Stage 1 is not proved in this file — see above).

`hgen` is needed because *nonzero adjugate sum* does not by itself imply *`F_B` is a
nonzero polynomial*. Counterexample: `m = n = 1`, `E 0 0 = Polynomial.X` (the entry is
literally the outer variable, i.e. the "matrix" is `[[v]]`). Then `B.adjugate = 1`
(`Matrix.adjugate_subsingleton`), so `∑ adjugate B = 1 ≠ 0` identically, yet
`F_B = X - X * 1 = 0` is the zero polynomial. In this example `val λ = lam0 [[val λ]] =
val λ` holds *tautologically* for every real number `val λ`, so `val` is entirely
unconstrained by the hypotheses — and indeed no single nonzero polynomial can force
`val` at every `λ` in this case. `hgen` rules out exactly this degeneracy: it says that
whenever a shape's adjugate sum is nonzero, its `F_B` is also nonzero. Genuine
applications (Stage 3: discounted stochastic games, entries affine in `v` with slope
`λ ∈ (0, 1)`, i.e. a *strict* contraction) are not of this degenerate form.

## Attribution

Shapley, L. S. and Snow, R. N., "Basic solutions of discrete games", 1950.
-/

open Finset BigOperators Matrix Polynomial

namespace ShapleySnow

/-! ### Stage 1 — TODO, the classical Shapley–Snow kernel theorem

```
theorem shapley_snow_kernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (r : ℕ) (hr : 0 < r) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
      (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j) ≠ 0 ∧
        MinimaxLoomis.lam0 A * (∑ i, ∑ j, (A.submatrix rows cols).adjugate i j)
          = (A.submatrix rows cols).det
```

Proof sketch (Shapley–Snow 1950), not yet formalised: take extreme optimal mixed
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

### Two named partial cases

The two cases of the induction sketch above are landed below as standalone, sorry-free
lemmas: `exists_kernel_of_saddlePoint` (the base case: a pure saddle point gives a
`1 × 1` kernel) and `exists_kernel_of_completelyMixed` (the classical Kaplansky
determinant formula for a completely-mixed square game: an *equalizing* pair of mixed
strategies for a nonsingular matrix gives the whole matrix as its own kernel). What
remains, and is NOT formalised here, is the reduction step: showing that every finite
matrix game falls into one of these two cases *after restricting to some square
submatrix* (i.e. producing the submatrix, and the nonsingularity / equalizing data, from
`lam0`/`mu0` alone via extreme-point or induction-on-size arguments). That reduction is
the genuinely hard core of Shapley–Snow 1950 and is left as the `TODO` above.
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

/-- **Completely-mixed kernel** (Kaplansky's determinant formula for a fully-mixed
square game). If `A` is nonsingular and admits an *equalizing pair* of mixed strategies
`x, y` for the same value `V` — every column's expected payoff under `x` is `V`, every
row's expected payoff under `y` is `V` — then `V = lam0 A`, and the whole matrix `A` is
its own kernel: the adjugate sum is nonzero and `V * (∑ adjugate) = det A`.

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
  classical
  have hVeq : MinimaxLoomis.lam0 A = V := by
    have hlamaux : MinimaxLoomis.lam.aux A x = V := by
      unfold MinimaxLoomis.lam.aux
      rw [show (fun j => wsum x (fun i => A i j)) = fun _ : Fin n => V from funext hxT]
      exact Finset.inf'_const Finset.univ_nonempty V
    have hmuaux : MinimaxLoomis.mu.aux A y = V := by
      unfold MinimaxLoomis.mu.aux
      rw [show (fun i => wsum y (fun j => A i j)) = fun _ : Fin n => V from funext hy]
      exact Finset.sup'_const Finset.univ_nonempty V
    have hVlam0 : V ≤ MinimaxLoomis.lam0 A := hlamaux ▸ MinimaxLoomis.lam.aux.le_lam0 A x
    have hmu0V : MinimaxLoomis.mu0 A ≤ V := hmuaux ▸ MinimaxLoomis.mu.aux.ge_mu0 A y
    exact le_antisymm ((MinimaxLoomis.lam0_le_mu0 A).trans hmu0V) hVlam0
  have hmulVec : A *ᵥ y.val = V • (1 : Fin n → ℝ) := by
    funext i
    have hrow : (A *ᵥ y.val) i = wsum y (fun j => A i j) := dotProduct_comm (A i) y.val
    rw [hrow, hy i]
    simp
  have hadj : Matrix.adjugate A *ᵥ (A *ᵥ y.val) = A.det • y.val := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hadj' :
      Matrix.adjugate A *ᵥ (A *ᵥ y.val) = V • (fun i => ∑ j, Matrix.adjugate A i j) := by
    rw [hmulVec, Matrix.mulVec_smul]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hkey : A.det • y.val = V • (fun i => ∑ j, Matrix.adjugate A i j) := hadj.symm.trans hadj'
  have hsum : A.det * (∑ i, y.val i) = V * (∑ i, ∑ j, Matrix.adjugate A i j) := by
    have hcongr := congrArg (fun f : Fin n → ℝ => ∑ i, f i) hkey
    simpa [Pi.smul_apply, smul_eq_mul, Finset.mul_sum] using hcongr
  rw [y.property.2, mul_one] at hsum
  have hSne : (∑ i, ∑ j, A.adjugate i j) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hsum
    exact hA.ne_zero hsum
  exact ⟨hVeq, hSne, hVeq ▸ hsum.symm⟩

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

/-! ### `bivEval` commutes with `det` / `adjugate`

Entrywise consequences of `RingHom.map_det` / `RingHom.map_adjugate`, phrased so they
compose directly with `Finset.sum` over matrix entries. -/

/-- `bivEval` commutes with `det` on a square bivariate-polynomial matrix. -/
theorem bivEval_det {r : ℕ} (l v : ℝ) (B : Matrix (Fin r) (Fin r) (Polynomial (Polynomial ℝ))) :
    bivEval l v B.det = (B.map (bivEval l v)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

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

/-- **Stage 2, concrete form.** The parametric Shapley–Snow corollary for a bivariate
`m × n` matrix family `E`, a self-referential value function `val`, and a genericity
hypothesis `hgen` ruling out the tautological degeneracy discussed above. The Stage-1
kernel property is taken as the explicit hypothesis `hkernel` (Stage 1 itself is
recorded as an unproved `TODO` above; this theorem shows exactly how the rest of the
argument goes through once it is supplied). -/
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
nonsingular-reward shape for the same matrix; neither residual case is handled here. -/
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
`w` on `(0, 1)` and the Stage-1 kernel property `hkernel` — now strengthened with the
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
`kernelPoly_ne_zero_of_reward_det_ne_zero` for the residual (singular-reward-kernel)
gap. -/
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
