/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.EquivFin

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Finite linear inequalities and their alternative certificates

A finite system of weak linear inequalities over a linearly ordered field has
an exact solution precisely when it has no nonnegative annihilating row
combination with a positive right-hand side. No topological closure or
completeness hypothesis is needed.

The proof eliminates one coordinate at a time by Fourier–Motzkin elimination.
The public theorem accepts arbitrary finite row and column types; the internal
induction uses finite ordinals only to select the last coordinate.

Adapted from `Maths.LinearProgramming.FourierMotzkin` in
[Elazar Gershuni's multitubes library](https://github.com/elazarg/multitubes).
The original author and Apache 2.0 license are retained above.
-/

open Finset

@[expose] public section

namespace GameTheory.Math.LinearInequality

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### The primal feasibility set and Farkas certificate set -/

/-- Evaluate the left-hand side of row `i` of the matrix `A : I → Fin n → 𝕜` at the point
`x : Fin n → 𝕜`. -/
private def rowEval {I : Type*} {n : ℕ} (A : I → Fin n → 𝕜) (i : I)
    (x : Fin n → 𝕜) : 𝕜 :=
  ∑ j, A i j * x j

/-- Primal feasibility of the system `A x ≥ b`. -/
private def IsFeasible {I : Type*} {n : ℕ} (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ x : Fin n → 𝕜, ∀ i, b i ≤ rowEval A i x

/-- `u : I → 𝕜` is a Farkas certificate of infeasibility of `A x ≥ b`: it is nonnegative,
annihilates every column of `A`, and pairs positively with `b`. -/
private def IsFarkasCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) (u : I → 𝕜) : Prop :=
  (∀ i, 0 ≤ u i) ∧
  (∀ j : Fin n, ∑ i, u i * A i j = 0) ∧
  (0 < ∑ i, u i * b i)

/-- Existence of a Farkas certificate of infeasibility of `A x ≥ b`. -/
private def HasFarkasCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ u : I → 𝕜, IsFarkasCertificate A b u

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Weighting the row evaluations by `u` is evaluating the `u`-weighted row combination. -/
private theorem sum_mul_rowEval {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (u : I → 𝕜) (x : Fin n → 𝕜) :
    ∑ i, u i * rowEval A i x = ∑ j, (∑ i, u i * A i j) * x j :=
  Matrix.dotProduct_mulVec u (Matrix.of A) x

/-! ### Disjointness: `IsFeasible` and `HasFarkasCertificate` cannot both hold -/

/-- A feasible system has no Farkas certificate: pairing a certificate `u` with `A x ≥ b`
gives `⟨u, b⟩ ≤ ⟨u, A x⟩ = ⟨uᵀA, x⟩ = 0 < ⟨u, b⟩`. -/
private theorem feas_cert_disjoint {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) (hcert : HasFarkasCertificate A b) : False := by
  obtain ⟨x, hx⟩ := hfeas
  obtain ⟨u, hu_nn, hu_zero, hu_pos⟩ := hcert
  have hweighted : ∑ i, u i * b i ≤ ∑ i, u i * rowEval A i x := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hx i) (hu_nn i)
  have hzero : ∑ i, u i * rowEval A i x = 0 := by
    rw [sum_mul_rowEval]
    simp [hu_zero]
  linarith

/-! ### Sign partition of rows by the last-column coefficient

For an `(n + 1)`-column matrix `A : I → Fin (n + 1) → 𝕜` over a finite row index `I`,
partition `I` into the three sign cases of `A i (Fin.last n)`. These are `abbrev`s so that
Lean's `Subtype.fintype` instances stay transparent. -/

variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- The rows where the last-column coefficient is zero. -/
private abbrev ZeroRows (A : I → Fin (n + 1) → 𝕜) : Type _ :=
  { i : I // A i (Fin.last n) = 0 }

/-- The rows where the last-column coefficient is strictly positive. -/
private abbrev PosRows (A : I → Fin (n + 1) → 𝕜) : Type _ :=
  { i : I // 0 < A i (Fin.last n) }

/-- The rows where the last-column coefficient is strictly negative. -/
private abbrev NegRows (A : I → Fin (n + 1) → 𝕜) : Type _ :=
  { i : I // A i (Fin.last n) < 0 }

/-- The reduced row index after Fourier-Motzkin elimination of the last column. -/
private abbrev FMRowIndex (A : I → Fin (n + 1) → 𝕜) : Type _ :=
  ZeroRows A ⊕ (PosRows A × NegRows A)

/-! ### The Fourier-Motzkin reduced matrix and right-hand side

The reduction keeps the zero rows, dropping their last entry, and replaces every pair
`(p, q) ∈ PosRows × NegRows` by the nonnegative combination `αq · row p + βp · row q` with
`αq = -A q last > 0` and `βp = A p last > 0`, which annihilates the last column. -/

/-- The Fourier-Motzkin reduced matrix coefficient. -/
private def fmA (A : I → Fin (n + 1) → 𝕜) (idx : FMRowIndex A) (j : Fin n) : 𝕜 :=
  match idx with
  | Sum.inl k => A k.val j.castSucc
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc

/-- The Fourier-Motzkin reduced right-hand side. -/
private def fmB (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜) (idx : FMRowIndex A) : 𝕜 :=
  match idx with
  | Sum.inl k => b k.val
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * b p.val
        + A p.val (Fin.last n) * b q.val

omit [IsStrictOrderedRing 𝕜] [Fintype I] [DecidableEq I] in
/-- A zero row of the reduced matrix is the original row with its last entry dropped. -/
@[simp] private theorem fmA_inl (A : I → Fin (n + 1) → 𝕜) (k : ZeroRows A) (j : Fin n) :
    fmA A (Sum.inl k) j = A k.val j.castSucc := rfl

omit [IsStrictOrderedRing 𝕜] [Fintype I] [DecidableEq I] in
/-- A combination row of the reduced matrix is the sign-weighted combination of its two
source rows. -/
@[simp] private theorem fmA_inr (A : I → Fin (n + 1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (j : Fin n) :
    fmA A (Sum.inr (p, q)) j
      = (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc := rfl

omit [IsStrictOrderedRing 𝕜] [Fintype I] [DecidableEq I] in
/-- A zero row of the reduced right-hand side is the original entry. -/
@[simp] private theorem fmB_inl (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (k : ZeroRows A) : fmB A b (Sum.inl k) = b k.val := rfl

omit [IsStrictOrderedRing 𝕜] [Fintype I] [DecidableEq I] in
/-- A combination row of the reduced right-hand side is the sign-weighted combination of its
two source entries. -/
@[simp] private theorem fmB_inr (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (p : PosRows A) (q : NegRows A) :
    fmB A b (Sum.inr (p, q))
      = (-A q.val (Fin.last n)) * b p.val
        + A p.val (Fin.last n) * b q.val := rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Unfold `rowEval` to its defining sum. -/
@[simp] private theorem rowEval_def {I : Type*} {n : ℕ}
    (A : I → Fin n → 𝕜) (i : I) (x : Fin n → 𝕜) :
    rowEval A i x = ∑ j, A i j * x j := rfl

/-! ### Feasibility transfer, forward direction

If `(x 0, …, x n)` satisfies the original `(n + 1)`-variable system, then `(x 0, …, x (n-1))`
satisfies the reduced `n`-variable system. -/

omit [DecidableEq I] [Fintype I] in
/-- Truncating a solution of the original system gives a solution of the reduced system. -/
private theorem fm_feasible_of_feasible (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) : IsFeasible (fmA A) (fmB A b) := by
  obtain ⟨x, hx⟩ := hfeas
  refine ⟨fun j => x j.castSucc, ?_⟩
  intro idx
  -- Split each original row sum into its first `n` entries plus the last one.
  have hsplit (i : I) :
      rowEval A i x
        = (∑ j : Fin n, A i j.castSucc * x j.castSucc)
          + A i (Fin.last n) * x (Fin.last n) := by
    rw [rowEval, Fin.sum_univ_castSucc]
  rcases idx with k | ⟨p, q⟩
  · -- Zero-row pass-through.
    have hk := hx k.val
    rw [hsplit, k.property, zero_mul, add_zero] at hk
    simp only [fmB_inl, rowEval_def, fmA_inl]
    exact hk
  · -- Combined-row inequality.
    have hp := hx p.val
    have hq := hx q.val
    rw [hsplit] at hp hq
    have hαq_pos : 0 < -A q.val (Fin.last n) := by linarith [q.property]
    have hβp_pos : 0 < A p.val (Fin.last n) := p.property
    have hcomb :
        (-A q.val (Fin.last n)) * b p.val
          + A p.val (Fin.last n) * b q.val
        ≤ (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      have hp_strip :
          b p.val - A p.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A p.val j.castSucc * x j.castSucc := by linarith
      have hq_strip :
          b q.val - A q.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A q.val j.castSucc * x j.castSucc := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hp_strip hαq_pos.le,
        mul_le_mul_of_nonneg_left hq_strip hβp_pos.le]
    simp only [fmB_inr, rowEval_def, fmA_inr]
    have hRHS :
        (∑ j : Fin n,
          ((-A q.val (Fin.last n)) * A p.val j.castSucc
            + A p.val (Fin.last n) * A q.val j.castSucc)
            * x j.castSucc)
        = (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    exact hcomb

/-! ### The reduced-pair lower-upper bound

From the reduced inequality at `(p, q) ∈ PosRows × NegRows`, the lower bound `L p` is at most
the upper bound `U q`. This is the algebraic content of "max lower ≤ min upper" that makes the
choice of the eliminated coordinate possible. -/

omit [DecidableEq I] [Fintype I] in
/-- At every positive-negative row pair, the lower bound is at most the upper bound. -/
private theorem reduced_pair_ineq
    {A : I → Fin (n + 1) → 𝕜} {b : I → 𝕜} {x' : Fin n → 𝕜}
    (hx' : ∀ idx, fmB A b idx ≤ rowEval (fmA A) idx x')
    (p : PosRows A) (q : NegRows A) :
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
    ≤ (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n) := by
  have h_pq := hx' (Sum.inr (p, q))
  simp only [fmB_inr, rowEval_def, fmA_inr] at h_pq
  have hdist :
      (∑ j : Fin n,
        ((-A q.val (Fin.last n)) * A p.val j.castSucc
          + A p.val (Fin.last n) * A q.val j.castSucc) * x' j)
      = (-A q.val (Fin.last n))
          * (∑ j : Fin n, A p.val j.castSucc * x' j)
        + A p.val (Fin.last n)
          * (∑ j : Fin n, A q.val j.castSucc * x' j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hdist] at h_pq
  have hβp : 0 < A p.val (Fin.last n) := p.property
  have hαq : 0 < -A q.val (Fin.last n) := by linarith [q.property]
  -- Convert the negative denominator of the upper bound into a positive one.
  set sumQ := ∑ j : Fin n, A q.val j.castSucc * x' j with hsumQ_def
  have hUq_flip :
      (b q.val - sumQ) / A q.val (Fin.last n)
      = -(b q.val - sumQ) / (-A q.val (Fin.last n)) := by
    rw [neg_div_neg_eq]
  rw [hUq_flip, div_le_div_iff₀ hβp hαq]
  linarith

/-! ### Feasibility transfer, backward direction

Given a solution `x'` of the reduced system, the eliminated coordinate can be chosen so that
`Fin.snoc x' x_last` solves the original `(n + 1)`-variable system. -/

omit [DecidableEq I] in
/-- Extending a solution of the reduced system by a suitable last coordinate solves the
original system. -/
private theorem feasible_of_fm_feasible (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (hred : IsFeasible (fmA A) (fmB A b)) : IsFeasible A b := by
  obtain ⟨x', hx'⟩ := hred
  classical
  -- Per-row lower and upper bounds for the eliminated coordinate.
  let L : PosRows A → 𝕜 := fun p =>
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
  let U : NegRows A → 𝕜 := fun q =>
    (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n)
  -- Choose the last coordinate by case-splitting on emptiness of the two row classes.
  let x_last : 𝕜 :=
    if hPos : (Finset.univ : Finset (PosRows A)).Nonempty then
      Finset.univ.sup' hPos L
    else if hNeg : (Finset.univ : Finset (NegRows A)).Nonempty then
      Finset.univ.inf' hNeg U
    else (0 : 𝕜)
  refine ⟨Fin.snoc x' x_last, ?_⟩
  intro i
  have hsplit : rowEval A i (Fin.snoc x' x_last)
      = (∑ j : Fin n, A i j.castSucc * x' j)
        + A i (Fin.last n) * x_last := by
    rw [rowEval_def, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rcases lt_trichotomy (A i (Fin.last n)) 0 with hlt | heq | hgt
  · -- Negative last-column coefficient: `i` is a negative row.
    let hiN : NegRows A := ⟨i, hlt⟩
    have hUbound : x_last ≤ U hiN := by
      by_cases hPos : (Finset.univ : Finset (PosRows A)).Nonempty
      · change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dite_eq_left hPos]
        apply Finset.sup'_le
        intro p _
        exact reduced_pair_ineq hx' p hiN
      · have hNeg : (Finset.univ : Finset (NegRows A)).Nonempty :=
          ⟨hiN, Finset.mem_univ _⟩
        change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dite_eq_right hPos, dite_eq_left hNeg]
        exact Finset.inf'_le _ (Finset.mem_univ hiN)
    have hUval : A i (Fin.last n) * U hiN
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      change A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_lt hlt
      field_simp
    have hmul : A i (Fin.last n) * U hiN ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonpos_left hUbound hlt.le
    rw [hsplit]
    linarith
  · -- Zero last-column coefficient: `i` is a zero row.
    let hiZ : ZeroRows A := ⟨i, heq⟩
    have h := hx' (Sum.inl hiZ)
    simp only [fmB_inl, rowEval_def, fmA_inl] at h
    rw [hsplit, heq, zero_mul, add_zero]
    exact h
  · -- Positive last-column coefficient: `i` is a positive row.
    let hiP : PosRows A := ⟨i, hgt⟩
    have hPos : (Finset.univ : Finset (PosRows A)).Nonempty :=
      ⟨hiP, Finset.mem_univ _⟩
    have hLbound : L hiP ≤ x_last := by
      change L hiP ≤ (if h : _ then Finset.univ.sup' h L
                       else if h' : _ then Finset.univ.inf' h' U else 0)
      rw [dite_eq_left hPos]
      exact Finset.le_sup' _ (Finset.mem_univ hiP)
    have hLval : A i (Fin.last n) * L hiP
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      change A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_gt hgt
      field_simp
    have hmul : A i (Fin.last n) * L hiP ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonneg_left hLbound hgt.le
    rw [hsplit]
    linarith

/-! ### Certificate lift along the transposed reduction

The reduction is encoded by a matrix `liftCoeff A : FMRowIndex A → I → 𝕜` whose rows record
the nonnegative weights with which the original rows enter each reduced row. A Farkas
certificate `u'` of the reduced system lifts to the original one as `u = Lᵀ u'`. -/

/-- The Fourier-Motzkin lift coefficient: the weight with which original row `i` enters the
reduced row `idx`. -/
private def liftCoeff (A : I → Fin (n + 1) → 𝕜) (idx : FMRowIndex A) (i : I) : 𝕜 :=
  match idx with
  | Sum.inl k => if k.val = i then 1 else 0
  | Sum.inr (p, q) =>
      (if p.val = i then -A q.val (Fin.last n) else 0)
      + (if q.val = i then A p.val (Fin.last n) else 0)

omit [IsStrictOrderedRing 𝕜] [Fintype I] in
/-- The lift coefficients of a zero row form the indicator of that row. -/
private theorem liftCoeff_inl (A : I → Fin (n + 1) → 𝕜) (k : ZeroRows A)
    (i : I) :
    liftCoeff A (Sum.inl k) i = if k.val = i then 1 else 0 := rfl

omit [IsStrictOrderedRing 𝕜] [Fintype I] in
/-- The lift coefficients of a combination row are supported on its two source rows. -/
private theorem liftCoeff_inr (A : I → Fin (n + 1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (i : I) :
    liftCoeff A (Sum.inr (p, q)) i
      = (if p.val = i then -A q.val (Fin.last n) else 0)
        + (if q.val = i then A p.val (Fin.last n) else 0) := rfl

/-- The lift of a reduced certificate `u'`, given by `u i = ∑ idx, liftCoeff A idx i * u' idx`. -/
private def liftCert (A : I → Fin (n + 1) → 𝕜) (u' : FMRowIndex A → 𝕜)
    (i : I) : 𝕜 :=
  ∑ idx, liftCoeff A idx i * u' idx

/-- The lift of a nonnegative reduced certificate is nonnegative. -/
private theorem liftCert_nonneg (A : I → Fin (n + 1) → 𝕜) {u' : FMRowIndex A → 𝕜}
    (hu' : ∀ idx, 0 ≤ u' idx) (i : I) : 0 ≤ liftCert A u' i := by
  apply Finset.sum_nonneg
  intro idx _
  apply mul_nonneg _ (hu' idx)
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_inl]
    split_ifs <;> norm_num
  · simp only [liftCoeff_inr]
    apply add_nonneg
    · split_ifs with hp
      · linarith [q.property]
      · norm_num
    · split_ifs with hq
      · exact p.property.le
      · norm_num

omit [IsStrictOrderedRing 𝕜] in
/-- Pairing the lift with a vector `g` on the original rows equals pairing `u'` with the
weighted sums of `g` over the reduced rows. -/
private theorem liftCert_weighted_sum_swap (A : I → Fin (n + 1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) (g : I → 𝕜) :
    ∑ i, liftCert A u' i * g i
    = ∑ idx, u' idx * (∑ i, liftCoeff A idx i * g i) := by
  unfold liftCert
  rw [show (∑ i, (∑ idx, liftCoeff A idx i * u' idx) * g i)
      = ∑ i, ∑ idx, liftCoeff A idx i * u' idx * g i from ?_,
      Finset.sum_comm]
  · refine Finset.sum_congr rfl ?_
    intro idx _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]

omit [IsStrictOrderedRing 𝕜] in
/-- The weighted sum at a zero row picks out that row. -/
@[simp] private theorem liftCoeff_weighted_inl (A : I → Fin (n + 1) → 𝕜)
    (k : ZeroRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inl k) i * g i = g k.val := by
  classical
  simp only [liftCoeff_inl, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]

omit [IsStrictOrderedRing 𝕜] in
/-- The weighted sum at a combination row is the combination of its two source entries. -/
@[simp] private theorem liftCoeff_weighted_inr (A : I → Fin (n + 1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inr (p, q)) i * g i
    = (-A q.val (Fin.last n)) * g p.val + A p.val (Fin.last n) * g q.val := by
  classical
  simp only [liftCoeff_inr, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
             Fintype.sum_ite_eq]

omit [IsStrictOrderedRing 𝕜] in
/-- The lift annihilates every column of `A` coming from the reduced system. -/
private theorem liftCert_column_zero_castSucc (A : I → Fin (n + 1) → 𝕜)
    {u' : FMRowIndex A → 𝕜}
    (hu'_zero : ∀ j : Fin n, ∑ idx, u' idx * fmA A idx j = 0) (j : Fin n) :
    ∑ i, liftCert A u' i * A i j.castSucc = 0 := by
  rw [liftCert_weighted_sum_swap]
  have hinner (idx) : ∑ i, liftCoeff A idx i * A i j.castSucc = fmA A idx j := by
    rcases idx with k | ⟨p, q⟩
    · simp [liftCoeff_weighted_inl]
    · simp [liftCoeff_weighted_inr]
  simp_rw [hinner]
  exact hu'_zero j

omit [IsStrictOrderedRing 𝕜] in
/-- The lift annihilates the eliminated column: this is the design of the reduction. -/
private theorem liftCert_column_zero_last (A : I → Fin (n + 1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * A i (Fin.last n) = 0 := by
  rw [liftCert_weighted_sum_swap]
  apply Finset.sum_eq_zero
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_weighted_inl, k.property, mul_zero]
  · simp only [liftCoeff_weighted_inr]
    ring

omit [IsStrictOrderedRing 𝕜] in
/-- The lift pairs with `b` exactly as the reduced certificate pairs with the reduced
right-hand side. -/
private theorem liftCert_rhs (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * b i = ∑ idx, u' idx * fmB A b idx := by
  rw [liftCert_weighted_sum_swap]
  refine Finset.sum_congr rfl ?_
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp [liftCoeff_weighted_inl]
  · simp [liftCoeff_weighted_inr]

omit [DecidableEq I] in
/-- **Farkas certificate lift**: if `u'` certifies the reduced system, then `liftCert A u'`
certifies the original one. -/
private theorem fm_cert_lift (A : I → Fin (n + 1) → 𝕜) (b : I → 𝕜)
    (hred : HasFarkasCertificate (fmA A) (fmB A b)) : HasFarkasCertificate A b := by
  classical
  obtain ⟨u', hu'_nn, hu'_zero, hu'_pos⟩ := hred
  refine ⟨liftCert A u', liftCert_nonneg A hu'_nn, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · exact liftCert_column_zero_last A u'
    · intro j'
      exact liftCert_column_zero_castSucc A hu'_zero j'
  · rw [liftCert_rhs]
    exact hu'_pos

/-! ### The base case of zero columns

For a system with no variables, `rowEval A i x = 0` for every `i`, so feasibility collapses to
`∀ i, b i ≤ 0`. Its negation yields a single row with `0 < b i`, whose indicator is a Farkas
certificate. -/

/-- The theorem of the alternative for a system with no variables. -/
private theorem theorem_of_alternative_base
    {I : Type*} [Fintype I] (A : I → Fin 0 → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasFarkasCertificate A b := by
  classical
  refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
  intro hinf
  have h_pick : ∃ i : I, 0 < b i := by
    by_contra hall
    push Not at hall
    apply hinf
    refine ⟨fun j : Fin 0 => Fin.elim0 j, fun i => ?_⟩
    have h_row_zero : rowEval A i (fun j : Fin 0 => Fin.elim0 j) = 0 := by
      unfold rowEval
      apply Finset.sum_eq_zero
      intro j _
      exact Fin.elim0 j
    rw [h_row_zero]
    exact hall i
  obtain ⟨i₀, hi₀⟩ := h_pick
  refine ⟨fun i => if i₀ = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i
    change 0 ≤ if i₀ = i then (1 : 𝕜) else 0
    split_ifs <;> norm_num
  · intro j
    exact Fin.elim0 j
  · change 0 < ∑ i, (if i₀ = i then (1 : 𝕜) else 0) * b i
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
    exact hi₀

/-! ### Induction on the number of columns

Feasibility transfer carries `¬ IsFeasible A b` to `¬ IsFeasible (fmA A) (fmB A b)`; the
inductive hypothesis then produces a reduced certificate, which `fm_cert_lift` lifts back. -/

/-- The theorem of the alternative, proved by induction on the number of columns. -/
private theorem theorem_of_alternative_aux :
    ∀ (n : ℕ) {I : Type*} [Fintype I]
      (A : I → Fin n → 𝕜) (b : I → 𝕜),
      ¬ IsFeasible A b ↔ HasFarkasCertificate A b := by
  intro n
  induction n with
  | zero =>
      intro I _ A b
      exact theorem_of_alternative_base A b
  | succ n ih =>
      intro I _ A b
      refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
      intro hinf
      have h_red_inf : ¬ IsFeasible (fmA A) (fmB A b) :=
        fun h => hinf (feasible_of_fm_feasible A b h)
      have h_red_cert : HasFarkasCertificate (fmA A) (fmB A b) :=
        (ih (fmA A) (fmB A b)).mp h_red_inf
      exact fm_cert_lift A b h_red_cert

/-! ### The packaged theorem -/

/-- **Theorem of the alternative**: for a finite system of weak linear inequalities `A x ≥ b`
over a linearly ordered field, exactly one of the primal set `{x | A x ≥ b}` and the Farkas
certificate set `{u ≥ 0 | uᵀA = 0, ⟨u, b⟩ > 0}` is nonempty.

This combines `feas_cert_disjoint` for disjointness with the existence direction proved by
Fourier-Motzkin elimination and induction on the number of variables. -/
private theorem theorem_of_alternative {I : Type*} [Fintype I] {n : ℕ}
    (A : I → Fin n → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasFarkasCertificate A b :=
  theorem_of_alternative_aux n A b


/-- A finite system of weak linear inequalities has a solution exactly when
there is no nonnegative row combination that annihilates all coefficients and
has a strictly positive right-hand side. Rows and columns may be empty. -/
theorem exists_solution_iff_no_certificate
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    (A : Row → Col → 𝕜) (b : Row → 𝕜) :
    (∃ x : Col → 𝕜, ∀ i, b i ≤ ∑ j, A i j * x j) ↔
      ¬ ∃ u : Row → 𝕜, (∀ i, 0 ≤ u i) ∧
        (∀ j, ∑ i, u i * A i j = 0) ∧ 0 < ∑ i, u i * b i := by
  classical
  let e := Fintype.equivFin Col
  let indexedA : Row → Fin (Fintype.card Col) → 𝕜 := fun i j => A i (e.symm j)
  have primal : (∃ x : Col → 𝕜, ∀ i, b i ≤ ∑ j, A i j * x j) ↔
      IsFeasible indexedA b := by
    constructor
    · rintro ⟨x, solution⟩
      refine ⟨fun j => x (e.symm j), fun i => ?_⟩
      change b i ≤ ∑ j, A i (e.symm j) * x (e.symm j)
      rw [e.symm.sum_comp (fun j => A i j * x j)]
      exact solution i
    · rintro ⟨x, solution⟩
      refine ⟨fun j => x (e j), fun i => ?_⟩
      have reindex := e.sum_comp (fun j => indexedA i j * x j)
      simp only [indexedA, Equiv.symm_apply_apply] at reindex
      rw [reindex]
      exact solution i
  have dual : (∃ u : Row → 𝕜, (∀ i, 0 ≤ u i) ∧
      (∀ j, ∑ i, u i * A i j = 0) ∧ 0 < ∑ i, u i * b i) ↔
      HasFarkasCertificate indexedA b := by
    constructor
    · rintro ⟨u, nonnegative, annihilates, positive⟩
      exact ⟨u, nonnegative, fun j => annihilates (e.symm j), positive⟩
    · rintro ⟨u, nonnegative, annihilates, positive⟩
      refine ⟨u, nonnegative, fun j => ?_, positive⟩
      simpa only [indexedA, Equiv.symm_apply_apply] using annihilates (e j)
  rw [primal, dual]
  simpa only [not_not] using not_congr (theorem_of_alternative indexedA b)

end GameTheory.Math.LinearInequality
