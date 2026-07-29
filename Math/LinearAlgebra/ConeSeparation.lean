/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.HausdorffDistance

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

/-! ### Closedness and exact metric separation -/

/-- The nonnegative span of the columns of `A`, represented in Euclidean
coordinates. -/
def euclideanConicSpan {d m : ℕ} (A : Fin d → Fin m → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ α : Fin m → ℝ, (∀ j, 0 ≤ α j) ∧
    ∀ i, (∑ j, α j * A i j) = x i}

theorem zero_mem_euclideanConicSpan {d m : ℕ}
    (A : Fin d → Fin m → ℝ) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ euclideanConicSpan A := by
  refine ⟨0, by simp, ?_⟩
  simp

theorem euclideanConicSpan_convex {d m : ℕ}
    (A : Fin d → Fin m → ℝ) :
    Convex ℝ (euclideanConicSpan A) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨α, hα, hαx⟩ := hx
  obtain ⟨β, hβ, hβy⟩ := hy
  refine ⟨fun j => a * α j + b * β j, ?_, ?_⟩
  · intro j
    exact add_nonneg (mul_nonneg ha (hα j)) (mul_nonneg hb (hβ j))
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply]
    calc
      (∑ j, (a * α j + b * β j) * A i j) =
          (∑ j, a * (α j * A i j)) +
            ∑ j, b * (β j * A i j) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = a * (∑ j, α j * A i j) +
            b * (∑ j, β j * A i j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = a * x i + b * y i := by rw [hαx i, hβy i]

theorem euclideanConicSpan_add_mem {d m : ℕ}
    {A : Fin d → Fin m → ℝ}
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ euclideanConicSpan A)
    (hy : y ∈ euclideanConicSpan A) :
    x + y ∈ euclideanConicSpan A := by
  obtain ⟨α, hα, hαx⟩ := hx
  obtain ⟨β, hβ, hβy⟩ := hy
  refine ⟨fun j => α j + β j, fun j => add_nonneg (hα j) (hβ j), ?_⟩
  intro i
  simp only [PiLp.add_apply]
  calc
    (∑ j, (α j + β j) * A i j) =
        (∑ j, α j * A i j) + ∑ j, β j * A i j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = x i + y i := by rw [hαx i, hβy i]

theorem euclideanConicSpan_nonneg_smul_mem {d m : ℕ}
    {A : Fin d → Fin m → ℝ}
    {x : EuclideanSpace ℝ (Fin d)}
    {c : ℝ} (hc : 0 ≤ c)
    (hx : x ∈ euclideanConicSpan A) :
    c • x ∈ euclideanConicSpan A := by
  obtain ⟨α, hα, hαx⟩ := hx
  refine ⟨fun j => c * α j, fun j => mul_nonneg hc (hα j), ?_⟩
  intro i
  simp only [PiLp.smul_apply]
  calc
    (∑ j, c * α j * A i j) =
        c * (∑ j, α j * A i j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = c * x i := by rw [hαx i]

/-- A column of `A`, regarded as a Euclidean vector. -/
def euclideanColumn {d m : ℕ} (A : Fin d → Fin m → ℝ) (j : Fin m) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => A i j

theorem euclideanColumn_mem_euclideanConicSpan {d m : ℕ}
    (A : Fin d → Fin m → ℝ) (j : Fin m) :
    euclideanColumn A j ∈ euclideanConicSpan A := by
  classical
  refine ⟨fun k => if k = j then 1 else 0, ?_, ?_⟩
  · intro k
    change 0 ≤ if k = j then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · intro i
    simp [euclideanColumn]

/-- A finitely generated cone is closed.  The proof uses the theorem of
alternatives to identify it with the intersection of all dual halfspaces. -/
theorem euclideanConicSpan_isClosed {d m : ℕ}
    (A : Fin d → Fin m → ℝ) :
    IsClosed (euclideanConicSpan A) := by
  let D : Set (EuclideanSpace ℝ (Fin d)) :=
    ⋂ h : Fin d → ℝ,
      ⋂ (_ : ∀ j, 0 ≤ ∑ i, h i * A i j),
        {x | 0 ≤ ∑ i, h i * x i}
  have hDclosed : IsClosed D := by
    apply isClosed_iInter
    intro h
    apply isClosed_iInter
    intro _
    exact isClosed_Ici.preimage <|
      continuous_finsetSum _ fun i _ =>
        (continuous_const :
          Continuous (fun _ : EuclideanSpace ℝ (Fin d) => h i)).mul
            (PiLp.continuous_apply 2 _ i)
  have hCD : euclideanConicSpan A = D := by
    ext x
    constructor
    · rintro ⟨α, hα, hαx⟩
      simp only [D, Set.mem_iInter, Set.mem_setOf_eq]
      intro h hh
      calc
        0 ≤ ∑ j, α j * (∑ i, h i * A i j) :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hα j) (hh j)
        _ = ∑ j, ∑ i, α j * (h i * A i j) :=
          Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum]
        _ = ∑ i, ∑ j, α j * (h i * A i j) := Finset.sum_comm
        _ = ∑ i, h i * (∑ j, α j * A i j) :=
          Finset.sum_congr rfl fun i _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ i, h i * x i :=
          Finset.sum_congr rfl fun i _ => by rw [hαx i]
    · intro hx
      by_contra hnot
      obtain ⟨h, _, hhA, hhx⟩ :=
        exists_euclideanUnit_conicSeparator A x hnot
      have := hx
      simp only [D, Set.mem_iInter, Set.mem_setOf_eq] at this
      exact (not_lt_of_ge (this h hhA)) hhx
  rw [hCD]
  exact hDclosed

/-- **Exact metric conic separation.**  A point outside a finitely generated
cone has a Euclidean-unit separator whose value on the point is exactly the
negative Euclidean distance to the cone. -/
theorem exists_euclideanUnit_conicSeparator_eq_neg_infDist {d m : ℕ}
    (A : Fin d → Fin m → ℝ) (b : Fin d → ℝ)
    (hnot : ¬ ∃ α : Fin m → ℝ, (∀ j, 0 ≤ α j) ∧
      ∀ i, (∑ j, α j * A i j) = b i) :
    let bE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b
    ∃ h : Fin d → ℝ,
      0 < Metric.infDist bE (euclideanConicSpan A) ∧
      (∑ i, h i ^ 2) = 1 ∧
      (∀ j, 0 ≤ ∑ i, h i * A i j) ∧
      (∑ i, h i * b i) =
        -Metric.infDist bE (euclideanConicSpan A) := by
  let bE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b
  have hbE_not : bE ∉ euclideanConicSpan A := by
    rintro ⟨α, hα, hαb⟩
    apply hnot
    exact ⟨α, hα, fun i => by simpa [bE] using hαb i⟩
  obtain ⟨p, hp, hpdist⟩ :=
    (euclideanConicSpan_isClosed A).exists_infDist_eq_dist
      ⟨0, zero_mem_euclideanConicSpan A⟩ bE
  let δ := Metric.infDist bE (euclideanConicSpan A)
  have hδnorm : δ = ‖bE - p‖ := by
    simpa only [δ, dist_eq_norm] using hpdist
  have hbE_ne_p : bE ≠ p := fun h => hbE_not (h ▸ hp)
  have hδpos : 0 < δ := by
    rw [hδnorm, norm_pos_iff]
    exact sub_ne_zero.mpr hbE_ne_p
  have hminimal :
      ‖bE - p‖ =
        ⨅ w : euclideanConicSpan A, ‖bE - w‖ := by
    calc
      ‖bE - p‖ = δ := hδnorm.symm
      _ = ⨅ w : euclideanConicSpan A, dist bE w :=
        Metric.infDist_eq_iInf
      _ = ⨅ w : euclideanConicSpan A, ‖bE - w‖ := by
        simp only [dist_eq_norm]
  have hprojection :
      ∀ w ∈ euclideanConicSpan A,
        inner ℝ (bE - p) (w - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero
      (euclideanConicSpan_convex A) hp).mp hminimal
  have hzero := hprojection 0 (zero_mem_euclideanConicSpan A)
  have htwice :=
    hprojection (p + p) (euclideanConicSpan_add_mem hp hp)
  have hortho : inner ℝ (bE - p) p = 0 := by
    have hnonneg : 0 ≤ inner ℝ (bE - p) p := by
      rw [zero_sub, inner_neg_right] at hzero
      linarith
    have hnonpos : inner ℝ (bE - p) p ≤ 0 := by
      have hsub : p + p - p = p := by abel
      rwa [hsub] at htwice
    exact le_antisymm hnonpos hnonneg
  let v : EuclideanSpace ℝ (Fin d) := bE - p
  let hE : EuclideanSpace ℝ (Fin d) := (-δ⁻¹) • v
  have hnorm_v : ‖v‖ = δ := by
    simpa only [v] using hδnorm.symm
  have hnorm_hE : ‖hE‖ = 1 := by
    calc
      ‖hE‖ = ‖(-δ⁻¹ : ℝ)‖ * ‖v‖ := by simp only [hE, norm_smul]
      _ = δ⁻¹ * δ := by
        rw [Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos hδpos, hnorm_v]
      _ = 1 := inv_mul_cancel₀ hδpos.ne'
  have hsquares : (∑ i, (hE i) ^ 2) = 1 := by
    have hsquareNorm := EuclideanSpace.real_norm_sq_eq hE
    rw [hnorm_hE] at hsquareNorm
    nlinarith
  have hcolumns : ∀ j, 0 ≤ ∑ i, hE i * A i j := by
    intro j
    let column := euclideanColumn A j
    have hpcolumn :
        p + column ∈ euclideanConicSpan A :=
      euclideanConicSpan_add_mem hp
        (euclideanColumn_mem_euclideanConicSpan A j)
    have hvcolumn : inner ℝ v column ≤ 0 := by
      have := hprojection (p + column) hpcolumn
      have hsub : p + column - p = column := by abel
      simpa only [v, hsub] using this
    have hhcolumn : 0 ≤ inner ℝ hE column := by
      simp only [hE, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      exact mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr (inv_nonneg.mpr hδpos.le)) hvcolumn
    simpa [PiLp.inner_apply, Real.inner_apply, column, euclideanColumn,
      mul_comm] using
      hhcolumn
  have hvb : inner ℝ v bE = δ ^ 2 := by
    have hbdecomp : bE = p + v := by simp [v]
    calc
      inner ℝ v bE = inner ℝ v (p + v) := by rw [hbdecomp]
      _ = inner ℝ v p + inner ℝ v v := inner_add_right _ _ _
      _ = 0 + inner ℝ v v := by
        rw [show inner ℝ v p = 0 by simpa only [v] using hortho]
      _ = 0 + ‖v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = δ ^ 2 := by rw [hnorm_v, zero_add]
  have htarget : (∑ i, hE i * b i) = -δ := by
    calc
      (∑ i, hE i * b i) = inner ℝ hE bE := by
        simp [PiLp.inner_apply, bE, mul_comm]
      _ = (-δ⁻¹) * inner ℝ v bE := by
        simp only [hE, inner_smul_left]
        simp
      _ = -δ := by
        rw [hvb, pow_two]
        field_simp
  exact ⟨fun i => hE i, hδpos, hsquares, hcolumns, htarget⟩

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

/-- Metric-strengthened Markov-flow separation.  The controlled drift of the
normalized superharmonic potential is exactly the Euclidean distance from the
transition difference to the baseline flow cone. -/
theorem exists_bounded_superharmonicSeparator_eq_infDist
    {n : ℕ} (P : Fin n → Fin n → ℝ) (Q : Fin n → ℝ)
    (source : Fin n)
    (hnot : ¬ ∃ α : Fin n → ℝ, (∀ s, 0 ≤ α s) ∧
      ∀ x,
        (∑ s, α s * (P s x - if s = x then 1 else 0)) =
          Q x - P source x) :
    let A : Fin n → Fin n → ℝ :=
      fun x s => P s x - if s = x then 1 else 0
    let b : Fin n → ℝ := fun x => Q x - P source x
    let bE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
    ∃ V : Fin n → ℝ,
      0 < Metric.infDist bE (euclideanConicSpan A) ∧
      (∑ x, V x ^ 2) = 1 ∧
      (∀ x, |V x| ≤ 1) ∧
      (∀ s, (∑ x, P s x * V x) ≤ V s) ∧
      (∑ x, (Q x - P source x) * V x) =
        Metric.infDist bE (euclideanConicSpan A) := by
  let A : Fin n → Fin n → ℝ :=
    fun x s => P s x - if s = x then 1 else 0
  let b : Fin n → ℝ := fun x => Q x - P source x
  let bE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  have hnot' : ¬ ∃ α : Fin n → ℝ, (∀ s, 0 ≤ α s) ∧
      ∀ x, (∑ s, α s * A x s) = b x := by
    simpa [A, b] using hnot
  obtain ⟨h, hdistpos, hunit, hcolumns, htarget⟩ :=
    exists_euclideanUnit_conicSeparator_eq_neg_infDist A b hnot'
  let V : Fin n → ℝ := fun x => -h x
  refine ⟨V, hdistpos, ?_, ?_, ?_, ?_⟩
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
  · change
      (∑ x, (Q x - P source x) * (-h x)) =
        Metric.infDist bE (euclideanConicSpan A)
    have hcommute :
        (∑ x, (Q x - P source x) * (-h x)) =
          -(∑ x, h x * (Q x - P source x)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hcommute]
    have hbtarget :
        (∑ x, h x * (Q x - P source x)) =
          -Metric.infDist bE (euclideanConicSpan A) := by
      simpa only [b] using htarget
    linarith

end LinearAlgebra
end Math
