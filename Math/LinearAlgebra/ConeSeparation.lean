/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt

/-!
# Normalized separation from a finitely generated cone

This file packages the finite-dimensional separation statement needed by the
stochastic-flow obstruction argument.  If a vector does not belong to the
nonnegative span of finitely many columns, the theorem of alternatives gives
a dual functional which is nonnegative on every column and strictly negative
on the target.  Dividing by its Euclidean norm makes the witness bounded
without changing either sign.

The stronger metric identity in which the detected target equals its exact
distance from the cone additionally requires a nearest-point construction for
the finitely generated cone.  The theorem here isolates the algebraic and
normalization content independently of that topological layer.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra

/-- Rows used to encode equality with a conic combination.  The two Boolean
rows impose the two orientations of each equality; the final rows impose
nonnegativity of the coefficients. -/
abbrev ConicMembershipRow (d m : ℕ) := (Fin d × Bool) ⊕ Fin m

/-- Inequality matrix encoding `∑ j, α j • A j = b` with `α ≥ 0`. -/
def conicMembershipMatrix {d m : ℕ} (A : Fin d → Fin m → ℝ) :
    ConicMembershipRow d m → Fin m → ℝ
  | Sum.inl (i, true), j => A i j
  | Sum.inl (i, false), j => -A i j
  | Sum.inr k, j => if k = j then 1 else 0

/-- Right-hand side paired with `conicMembershipMatrix`. -/
def conicMembershipTarget {d m : ℕ} (b : Fin d → ℝ) :
    ConicMembershipRow d m → ℝ
  | Sum.inl (i, true) => b i
  | Sum.inl (i, false) => -b i
  | Sum.inr _ => 0

/-- Feasibility of the encoded weak-inequality system is exactly membership in
the nonnegative span of the columns. -/
theorem conicMembership_feasible_iff {d m : ℕ}
    (A : Fin d → Fin m → ℝ) (b : Fin d → ℝ) :
    IsFeasible (conicMembershipMatrix A) (conicMembershipTarget b) ↔
      ∃ α : Fin m → ℝ, (∀ j, 0 ≤ α j) ∧
        ∀ i, (∑ j, α j * A i j) = b i := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_, ?_⟩
    · intro j
      have h := hα (Sum.inr j)
      simpa [rowEval, conicMembershipMatrix, conicMembershipTarget] using h
    · intro i
      have hpos := hα (Sum.inl (i, true))
      have hneg := hα (Sum.inl (i, false))
      simp only [rowEval, conicMembershipMatrix, conicMembershipTarget] at hpos hneg
      have hpos' : b i ≤ ∑ j, α j * A i j := by
        simpa [mul_comm] using hpos
      have hneg' : -(∑ j, α j * A i j) ≥ -b i := by
        calc
          -(∑ j, α j * A i j) = ∑ j, -A i j * α j := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
          _ ≥ -b i := hneg
      linarith
  · rintro ⟨α, hα_nonneg, hα_eq⟩
    refine ⟨α, ?_⟩
    intro row
    rcases row with ⟨i, positive⟩ | j
    · cases positive
      · simp only [conicMembershipTarget, rowEval, conicMembershipMatrix]
        rw [show (∑ k, -A i k * α k) = -(∑ k, α k * A i k) by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring]
        rw [hα_eq i]
      · simp only [conicMembershipTarget, rowEval, conicMembershipMatrix]
        simpa [mul_comm] using (hα_eq i).ge
    · simpa [conicMembershipTarget, rowEval, conicMembershipMatrix] using
        hα_nonneg j

/-- **Normalized conic separation.**  A vector outside a finitely generated
cone has a Euclidean-unit dual witness which is nonnegative on every
generator and strictly negative on the target.

The normalization is expressed without choosing a norm instance on function
spaces: `∑ i, h i ^ 2 = 1` is exactly the squared Euclidean norm condition. -/
theorem exists_euclideanUnit_conicSeparator {d m : ℕ}
    (A : Fin d → Fin m → ℝ) (b : Fin d → ℝ)
    (hnot : ¬ ∃ α : Fin m → ℝ, (∀ j, 0 ≤ α j) ∧
      ∀ i, (∑ j, α j * A i j) = b i) :
    ∃ h : Fin d → ℝ,
      (∑ i, h i ^ 2) = 1 ∧
      (∀ j, 0 ≤ ∑ i, h i * A i j) ∧
      (∑ i, h i * b i) < 0 := by
  have hinfeasible :
      ¬ IsFeasible (conicMembershipMatrix A) (conicMembershipTarget b) := by
    rwa [conicMembership_feasible_iff]
  obtain ⟨u, hu_nonneg, hu_zero, hu_pos⟩ :=
    (theorem_of_alternative
      (conicMembershipMatrix A) (conicMembershipTarget b)).mp hinfeasible
  let raw : Fin d → ℝ :=
    fun i => u (Sum.inl (i, false)) - u (Sum.inl (i, true))
  have hraw_columns : ∀ j, 0 ≤ ∑ i, raw i * A i j := by
    intro j
    have hzero := hu_zero j
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hzero
    simp only [Fintype.sum_bool, conicMembershipMatrix, mul_neg] at hzero
    change
      0 ≤ ∑ i,
        (u (Sum.inl (i, false)) - u (Sum.inl (i, true))) * A i j
    have hnonneg := hu_nonneg (Sum.inr j)
    change 0 ≤ u (Sum.inr j) at hnonneg
    have hinr :
        (∑ x, u (Sum.inr x) * if x = j then 1 else 0) =
          u (Sum.inr j) := by
      classical
      simp
    rw [hinr] at hzero
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hzero
    have hrearrange :
        (∑ i,
          (u (Sum.inl (i, false)) - u (Sum.inl (i, true))) * A i j) =
            u (Sum.inr j) := by
      simp only [sub_mul]
      rw [Finset.sum_sub_distrib]
      linarith
    rw [hrearrange]
    exact hnonneg
  have hraw_target : (∑ i, raw i * b i) < 0 := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hu_pos
    simp only [Fintype.sum_bool, conicMembershipTarget, mul_neg,
      mul_zero, Finset.sum_const_zero, add_zero] at hu_pos
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hu_pos
    change (∑ i,
      (u (Sum.inl (i, false)) - u (Sum.inl (i, true))) * b i) < 0
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    linarith
  have hraw_ne : raw ≠ 0 := by
    intro hzero
    have : (∑ i, raw i * b i) = 0 := by simp [hzero]
    linarith
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hraw_ne
  have hsquares_pos : 0 < ∑ k, raw k ^ 2 := by
    refine Finset.sum_pos' (fun k _ => sq_nonneg (raw k)) ?_
    exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  let scale : ℝ := Real.sqrt (∑ k, raw k ^ 2)
  have hscale_pos : 0 < scale := by
    exact Real.sqrt_pos.2 hsquares_pos
  let h : Fin d → ℝ := fun i => raw i / scale
  refine ⟨h, ?_, ?_, ?_⟩
  · change (∑ i, (raw i / scale) ^ 2) = 1
    have hsquare_scale : scale ^ 2 = ∑ i, raw i ^ 2 := by
      exact Real.sq_sqrt hsquares_pos.le
    calc
      (∑ i, (raw i / scale) ^ 2) =
          (∑ i, raw i ^ 2) / scale ^ 2 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := by rw [hsquare_scale, div_self hsquares_pos.ne']
  · intro j
    change 0 ≤ ∑ i, (raw i / scale) * A i j
    have heq :
        (∑ i, (raw i / scale) * A i j) =
          (∑ i, raw i * A i j) / scale := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    exact div_nonneg (hraw_columns j) hscale_pos.le
  · change (∑ i, (raw i / scale) * b i) < 0
    have heq :
        (∑ i, (raw i / scale) * b i) =
          (∑ i, raw i * b i) / scale := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    exact div_neg_of_neg_of_pos hraw_target hscale_pos

/-! ### Markov-flow specialization -/

/-- A transition difference outside the nonnegative baseline-flow cone has a
bounded superharmonic separator with strictly positive controlled drift.

No stochastic assumptions are needed for the linear-algebraic implication
itself.  When `P s` and `Q` are probability vectors, the displayed
inequalities have their usual Markov-potential interpretation. -/
theorem exists_bounded_superharmonicSeparator_of_not_mem_transitionCone
    {n : ℕ} (P : Fin n → Fin n → ℝ) (Q : Fin n → ℝ)
    (source : Fin n)
    (hnot : ¬ ∃ α : Fin n → ℝ, (∀ s, 0 ≤ α s) ∧
      ∀ x,
        (∑ s, α s * (P s x - if s = x then 1 else 0)) =
          Q x - P source x) :
    ∃ V : Fin n → ℝ,
      (∑ x, V x ^ 2) = 1 ∧
      (∀ x, |V x| ≤ 1) ∧
      (∀ s, (∑ x, P s x * V x) ≤ V s) ∧
      0 < ∑ x, (Q x - P source x) * V x := by
  let A : Fin n → Fin n → ℝ :=
    fun x s => P s x - if s = x then 1 else 0
  let b : Fin n → ℝ := fun x => Q x - P source x
  have hnot' : ¬ ∃ α : Fin n → ℝ, (∀ s, 0 ≤ α s) ∧
      ∀ x, (∑ s, α s * A x s) = b x := by
    simpa [A, b] using hnot
  obtain ⟨h, hunit, hcolumns, htarget⟩ :=
    exists_euclideanUnit_conicSeparator A b hnot'
  let V : Fin n → ℝ := fun x => -h x
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · simpa [V] using hunit
  · intro x
    have hterm : V x ^ 2 ≤ ∑ y, V y ^ 2 := by
      refine Finset.single_le_sum
        (f := fun y : Fin n => V y ^ 2) (s := Finset.univ) ?_
          (Finset.mem_univ x)
      intro y _
      exact sq_nonneg (V y)
    have hsquare : V x ^ 2 ≤ 1 := by
      simpa [hunit, V] using hterm
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (V x - 1), sq_nonneg (V x + 1)]
  · intro s
    have hcolumn := hcolumns s
    change
      0 ≤ ∑ x, h x * (P s x - if s = x then 1 else 0)
        at hcolumn
    have hindicator :
        (∑ x, h x * if s = x then 1 else 0) = h s := by
      classical
      simp
    simp_rw [mul_sub] at hcolumn
    rw [Finset.sum_sub_distrib, hindicator] at hcolumn
    change (∑ x, P s x * (-h x)) ≤ -h s
    have hcommute :
        (∑ x, P s x * (-h x)) = -(∑ x, h x * P s x) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hcommute]
    linarith
  · change 0 < ∑ x, (Q x - P source x) * (-h x)
    have hcommute :
        (∑ x, (Q x - P source x) * (-h x)) =
          -(∑ x, h x * (Q x - P source x)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hcommute]
    exact neg_pos.mpr htarget

end LinearAlgebra
end Math
