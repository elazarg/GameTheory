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
an unproved (`sorry`-laden) declaration, per this repository's "no `sorry`" rule. The two
base cases of the proof sketch (`exists_kernel_of_saddlePoint`,
`exists_kernel_of_completelyMixed`) and, further down, convexity / compactness /
Krein–Milman existence of *extreme* optimal strategies together with the
complementary-slackness tightness step (`optimalRowStrategies`, `optimalColStrategies`,
`expectedPayoff_eq_of_optimal`, `tight_of_optimal_row_support`,
`tight_of_optimal_col_support`) ARE landed below, sorry-free. Of the three remaining
sub-steps (cardinality bound, square/basis selection, reassembly), the cardinality bound
(`card_support_le_card_tightCol_of_extreme`, `card_support_le_card_tightRow_of_extreme`)
and the reassembly (`exists_kernel_of_extreme_matching_support`) are ALSO now landed,
sorry-free; only the square/basis-selection step (matching support sizes and producing a
nonsingular submatrix on them) remains open, documented precisely at the end of that
section.

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

### Two named partial cases, and the extremality step

The two base cases of the induction sketch above are landed below as standalone,
sorry-free lemmas: `exists_kernel_of_saddlePoint` (a pure saddle point gives a `1 × 1`
kernel) and `exists_kernel_of_completelyMixed` (the classical Kaplansky determinant
formula for a completely-mixed square game: an *equalizing* pair of mixed strategies for
a nonsingular matrix gives the whole matrix as its own kernel). The "extremality forces
`|R| = |C|`" step of the reduction is *partially* landed: `eq_zero_of_extreme_optimalRow`
/ `eq_zero_of_extreme_optimalCol` (in the `OptimalStrategies` section below) prove,
sorry-free, that the tight-constraint linear system at an extreme optimal strategy has
trivial kernel on its support — the precise `openSegment`-based `x ± εd` perturbation
argument the reduction needs, reproved from scratch since Mathlib's `Set.extremePoints`
carries no vertex/basic-feasible-solution theory. Turning that trivial-kernel fact into
the cardinality bounds `|R| ≤ |C(x)| + 1`, `|C| ≤ |R(y)| + 1` (rank-nullity) and
reassembling a matching-support nonsingular submatrix back into the Shapley–Snow identity
for `A` itself ARE now also landed, sorry-free — see the "What remains" note after the
`OptimalStrategies` section for exactly what is landed and what precise gap (matching
`|R| = |C|` and selecting a nonsingular submatrix on the matching supports) remains;
`hkernel` is accordingly still an explicit, undischarged hypothesis of
`exists_nonzero_poly_of_kernel` / `exists_nonzero_poly_of_discounted` below.
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

/-! ### Optimal strategy sets: convexity, compactness, extreme optimizers

Building blocks for the classical Shapley–Snow reduction sketch (`x`, `y` "extreme
optimal mixed strategies" in the `TODO` proof sketch above). `optimalRowStrategies A V`
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
the support of an optimal pair, the payoff equations are tight. This is real progress
towards the sketch, but NOT the reduction itself — see the TODO note at the end of this
section for exactly what remains. -/

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
theorem eq_zero_of_extreme_optimalRow {A : I → J → ℝ} {V : ℝ}
    {x : I → ℝ} (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A V))
    {d : I → ℝ} (hd_supp : ∀ i, x i = 0 → d i = 0) (hd_sum : ∑ i, d i = 0)
    (hd_tight : ∀ j, ∑ i, x i * A i j = V → ∑ i, d i * A i j = 0) : d = 0 := by
  classical
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

/-- **Extremality forces the tight-constraint system to have trivial kernel (column
side).** The column-player mirror of `eq_zero_of_extreme_optimalRow`: if `y` is an
extreme point of `optimalColStrategies A V`, and `e` (i) is supported on `y`'s support,
(ii) sums to `0`, and (iii) is annihilated by every row tight at `y`, then `e = 0`. -/
theorem eq_zero_of_extreme_optimalCol {A : I → J → ℝ} {V : ℝ}
    {y : J → ℝ} (hy : y ∈ Set.extremePoints ℝ (optimalColStrategies A V))
    {e : J → ℝ} (he_supp : ∀ j, y j = 0 → e j = 0) (he_sum : ∑ j, e j = 0)
    (he_tight : ∀ i, ∑ j, y j * A i j = V → ∑ j, e j * A i j = 0) : e = 0 := by
  classical
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

/-- **Cardinality bound (row side): step 1 of "What remains" below.** If `x` is an extreme
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

/-- **Cardinality bound (column side): step 1 of "What remains" below, mirror.** If `y`
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

/-- **Reindexing a sum along an embedding whose range is exactly a support.** If
`e : Fin r ↪ κ` enumerates `z`'s support exactly (`z k ≠ 0 ↔ k ∈ Set.range e`) and `f`
vanishes off `z`'s support, then summing `f ∘ e` over `Fin r` recovers the sum of `f` over
all of `κ`. Used below (step 3 of "What remains") to transport tightness/normalisation
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

section SquareKernelReassembly

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

omit [Nonempty I] in
/-- **Reassembly (step 3 of "What remains" below).** If `x`, `y` are extreme optimal
strategies at `V := lam0 A` whose supports are *exactly* enumerated by embeddings `rows`,
`cols` of a common size `r` (`hrows`, `hcols`), and the resulting square submatrix
`A.submatrix rows cols` is nonsingular (`hB`), then that submatrix IS a Shapley–Snow
kernel for `A`: the restrictions `x ∘ rows`, `y ∘ cols` are themselves mixed strategies
(they inherit non-negativity from `x`, `y`, and sum to `1` since `rows`/`cols` exactly
enumerate the support, so no mass is lost), and they form an *equalizing pair* for the
submatrix at value `V` (complementary slackness, `tight_of_optimal_row_support` /
`tight_of_optimal_col_support`, applied since every row of `rows`/column of `cols` lies in
the support of `x`/`y`, hence in the region where the corresponding player's tightness is
known). `exists_kernel_of_completelyMixed` then gives `lam0 (submatrix) = V`, and
`V = lam0 A` by construction, yielding exactly the Shapley–Snow determinant identity for
`A` itself (not just for the submatrix in isolation) — the "reassembly" step. -/
theorem exists_kernel_of_extreme_matching_support {A : I → J → ℝ}
    {x : I → ℝ} (hx : x ∈ Set.extremePoints ℝ (optimalRowStrategies A (MinimaxLoomis.lam0 A)))
    {y : J → ℝ} (hy : y ∈ Set.extremePoints ℝ (optimalColStrategies A (MinimaxLoomis.lam0 A)))
    {r : ℕ} (rows : Fin r ↪ I) (cols : Fin r ↪ J)
    (hrows : ∀ i, x i ≠ 0 ↔ i ∈ Set.range rows) (hcols : ∀ j, y j ≠ 0 ↔ j ∈ Set.range cols)
    (hB : IsUnit ((Matrix.of A).submatrix rows cols).det) :
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
  obtain ⟨hlamB, hadjne, heq⟩ := exists_kernel_of_completelyMixed B hB xr yr V hxr_tight hyr_tight
  refine ⟨r, hr, rows, cols, hadjne, ?_⟩
  change MinimaxLoomis.lam0 A * (∑ i, ∑ j, B.adjugate i j) = B.det
  rw [← hV, ← hlamB]
  exact heq

end SquareKernelReassembly

/-! ### What remains: from "trivial kernel direction" to a square nonsingular submatrix

The building blocks above land the convexity/compactness/Krein–Milman half of the
reduction sketch: extreme optimal mixed strategies `x ∈ extremePoints ℝ
(optimalRowStrategies A (lam0 A))`, `y ∈ extremePoints ℝ (optimalColStrategies A (lam0
A))` exist (`extremePoints_optimalRowStrategies_nonempty`,
`extremePoints_optimalColStrategies_nonempty`), and on their supports the payoff
equations are tight (`tight_of_optimal_row_support`, `tight_of_optimal_col_support`) —
this holds for *any* optimal pair, not just extreme ones, since complementary slackness
only used the defining inequalities, not extremality.

`eq_zero_of_extreme_optimalRow` / `eq_zero_of_extreme_optimalCol` (above) land the
*extremality* step proper — precisely the "if the tight constraints had a nontrivial
kernel direction `d`, then `x ± εd` would both be optimal, contradicting extremality"
argument anticipated in the reduction sketch, reproved from Mathlib's bare
`openSegment`/`Set.extremePoints` definition (`Mathlib.Analysis.Convex.Extreme` carries no
higher-level vertex/basic-feasible-solution theory, so this had to be built directly: for
`x` extreme in `optimalRowStrategies A V`, any direction `d` that (i) is supported on
`x`'s support, (ii) sums to `0`, and (iii) is annihilated by every column tight at `x`,
must be `0` — i.e. the tight-constraint linear system has trivial kernel on the support).
This is the injectivity half of the classical "extreme point = basic feasible solution"
equivalence, made precise and PROVED (sorry-free) for this specific polytope.

What is NOT proved here, and is needed to finish `exists_kernel`/`shapley_snow_kernel`, is
turning that injectivity fact into the concrete combinatorial/linear-algebraic data the
theorem statement demands. Of the three sub-steps originally identified, **two are now
landed** (sorry-free) and one remains, sharpened to a precise standalone statement:

1. **Cardinality bound — LANDED** (`card_support_le_card_tightCol_of_extreme`,
   `card_support_le_card_tightRow_of_extreme`, just above). Injectivity of
   `d ↦ (∑ᵢ dᵢ, (∑ᵢ dᵢAᵢⱼ)_{j ∈ C(x)})` on the directions supported on `R := {i | x i ≠
   0}` is packaged as an explicit `LinearMap` on `(R → ℝ)`; rank-nullity
   (`LinearMap.finrank_le_finrank_of_injective`) then gives exactly `|R| ≤ |C(x)| + 1`
   (`C(x)` the columns tight at `x`), and symmetrically `|C| ≤ |R(y)| + 1` for the column
   side. (`sum_eq_sum_support`, right above the row/column lemmas, is the reindexing
   glue: a sum over the ambient type of a function vanishing off `x`'s support equals the
   sum over the support subtype, needed to translate `eq_zero_of_extreme_*`'s
   whole-type-indexed hypotheses onto that subtype.)
2. **Basis/square selection — the ONE REMAINING GAP**, isolated as precisely as possible.
   The cardinality bounds from step 1, together with the complementary-slackness
   inclusions `C ⊆ C(x)` and `R ⊆ R(y)` (`tight_of_optimal_col_support` /
   `tight_of_optimal_row_support`), give *rectangular* full-(row/column)-rank systems on
   each side, but do NOT by themselves give `|R| = |C|`: that equality is a genuine fact
   about *matching* linear-programming bases (`x`, `y` are extreme points of two *dual*
   polytopes, and their supports correspond to bases of the *same* LP tableau), not a
   generic rank-nullity consequence of the two one-sided bounds in isolation. Classically
   this is established by an induction on `m + n` (a pivoting/degenerate-case argument),
   which is a substantially larger undertaking than steps 1 and 3 and is NOT attempted
   here. The exact remaining obligation, sharpened to a single precise statement,
   is now exactly the hypothesis bundle of `exists_kernel_of_extreme_matching_support`
   below: given extreme optimal `x`, `y` at `V := lam0 A`, produce `r`, embeddings
   `rows : Fin r ↪ I`, `cols : Fin r ↪ J` whose ranges are EXACTLY `x`'s and `y`'s
   supports (`hrows`, `hcols`), such that `(A.submatrix rows cols)` is nonsingular
   (`hB`). No other input is missing: feeding any such `r`, `rows`, `cols`, `hB` (for
   *some* choice of extreme `x`, `y` — not necessarily the same ones on repeated
   invocations, since `exists_kernel` only needs existence) into that lemma finishes
   `exists_kernel` outright.
3. **Reassembly — LANDED** (`exists_kernel_of_extreme_matching_support`, just above,
   in the `SquareKernelReassembly` section). Granted the step-2 data, `x ∘ rows` and
   `y ∘ cols` are themselves valid mixed strategies (non-negativity inherited from `x`,
   `y`; they sum to `1` because `rows`/`cols` enumerate the support *exactly*, so no
   probability mass is dropped), and complementary slackness
   (`tight_of_optimal_row_support` / `tight_of_optimal_col_support`) makes them an
   *equalizing pair* for the submatrix `B` at value `V`, since every row of `rows`/column
   of `cols` lies in `x`'s/`y`'s own support. `exists_kernel_of_completelyMixed` then
   gives `lam0 B = V`, and since `V = lam0 A` by construction (not `lam0 B` a priori —
   this is precisely the "reassembly" content), substituting recovers the Shapley–Snow
   identity for `A` itself.

`hkernel` is consequently NOT discharged in this file: `exists_nonzero_poly_of_kernel`
and `exists_nonzero_poly_of_discounted` below still take it as an explicit hypothesis.
But the gap is now exactly step 2 above — a single precise square/nonsingular-selection
fact — rather than the three-part gap (rank-nullity + selection + reassembly) that stood
before this section; steps 1 and 3, the finite-dimensional linear algebra either side of
it, are fully formalised and sorry-free. -/

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
