/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite Linear Programming

Finite-dimensional primal/dual linear-programming vocabulary over arbitrary
finite row and column types.

The primal problem is in packing form:

* maximize `c ⬝ x`
* subject to `A x ≤ b` and `x ≥ 0`.

The dual problem is:

* minimize `b ⬝ y`
* subject to `y A ≥ c` and `y ≥ 0`.

This file proves weak duality and complementary-slackness consequences from a
zero duality gap. Strong duality and Farkas-type alternatives are deliberately
kept out of this basic algebraic layer.
-/

open scoped BigOperators

namespace Math
namespace LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- Finite dot product. -/
def dot {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ :=
  ∑ i, u i * v i

theorem dot_comm {ι : Type*} [Fintype ι] (u v : ι → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

/-- Row evaluation of a finite matrix against a column vector. -/
def rowEval (A : Row → Col → ℝ) (x : Col → ℝ) (i : Row) : ℝ :=
  ∑ j, A i j * x j

/-- Column evaluation of a finite matrix against a row vector. -/
def colEval (A : Row → Col → ℝ) (y : Row → ℝ) (j : Col) : ℝ :=
  ∑ i, y i * A i j

/-- Pointwise nonnegativity for a finite vector. -/
def Nonnegative {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

/-- Primal feasibility for `max c⬝x` subject to `Ax ≤ b`, `x ≥ 0`. -/
def PrimalFeasible (A : Row → Col → ℝ) (b : Row → ℝ) (x : Col → ℝ) : Prop :=
  Nonnegative x ∧ ∀ i, rowEval A x i ≤ b i

/-- Dual feasibility for `min b⬝y` subject to `yA ≥ c`, `y ≥ 0`. -/
def DualFeasible (A : Row → Col → ℝ) (c : Col → ℝ) (y : Row → ℝ) : Prop :=
  Nonnegative y ∧ ∀ j, c j ≤ colEval A y j

/-- Primal objective value. -/
def primalValue (c : Col → ℝ) (x : Col → ℝ) : ℝ :=
  dot c x

/-- Dual objective value. -/
def dualValue (b : Row → ℝ) (y : Row → ℝ) : ℝ :=
  dot b y

theorem dot_mono_of_nonnegative_right {ι : Type*} [Fintype ι]
    {u v w : ι → ℝ} (hle : ∀ i, u i ≤ v i) (hw : Nonnegative w) :
    dot u w ≤ dot v w := by
  dsimp [dot]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hw i)

theorem dot_mono_of_nonnegative_left {ι : Type*} [Fintype ι]
    {u v w : ι → ℝ} (hle : ∀ i, u i ≤ v i) (hw : Nonnegative w) :
    dot w u ≤ dot w v := by
  dsimp [dot]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hw i)

/-- The bilinear interchange identity `(yA)⬝x = y⬝(Ax)`. -/
theorem dot_colEval_eq_dot_rowEval (A : Row → Col → ℝ) (x : Col → ℝ) (y : Row → ℝ) :
    dot (colEval A y) x = dot y (rowEval A x) := by
  classical
  calc
    dot (colEval A y) x = ∑ j, (∑ i, y i * A i j) * x j := rfl
    _ = ∑ j, ∑ i, (y i * A i j) * x j := by
      simp [Finset.sum_mul]
    _ = ∑ i, ∑ j, (y i * A i j) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, y i * (A i j * x j) := by
      simp [mul_assoc]
    _ = ∑ i, y i * ∑ j, A i j * x j := by
      simp [Finset.mul_sum]
    _ = dot y (rowEval A x) := rfl

/-- Weak duality for finite packing-form LPs. -/
theorem weak_duality {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y) :
    primalValue c x ≤ dualValue b y := by
  calc
    primalValue c x = dot c x := rfl
    _ ≤ dot (colEval A y) x :=
      dot_mono_of_nonnegative_right hy.2 hx.1
    _ = dot y (rowEval A x) :=
      dot_colEval_eq_dot_rowEval A x y
    _ ≤ dot y b :=
      dot_mono_of_nonnegative_left hx.2 hy.1
    _ = dualValue b y := by
      rw [dualValue, dot_comm]

/-- The column slack of a dual-feasible point. -/
def dualSlack (A : Row → Col → ℝ) (c : Col → ℝ) (y : Row → ℝ) (j : Col) : ℝ :=
  colEval A y j - c j

/-- The row slack of a primal-feasible point. -/
def primalSlack (A : Row → Col → ℝ) (b : Row → ℝ) (x : Col → ℝ) (i : Row) : ℝ :=
  b i - rowEval A x i

omit [Fintype Col] in
theorem dualSlack_nonnegative {A : Row → Col → ℝ} {c : Col → ℝ} {y : Row → ℝ}
    (hy : DualFeasible A c y) : Nonnegative (dualSlack A c y) := by
  intro j
  dsimp [dualSlack]
  linarith [hy.2 j]

omit [Fintype Row] in
theorem primalSlack_nonnegative {A : Row → Col → ℝ} {b : Row → ℝ} {x : Col → ℝ}
    (hx : PrimalFeasible A b x) : Nonnegative (primalSlack A b x) := by
  intro i
  dsimp [primalSlack]
  linarith [hx.2 i]

theorem duality_gap_eq_slack_sum {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ} :
    dualValue b y - primalValue c x =
      dot (primalSlack A b x) y + dot (dualSlack A c y) x := by
  classical
  rw [dualValue, primalValue]
  calc
    dot b y - dot c x =
        (dot b y - dot y (rowEval A x)) + (dot (colEval A y) x - dot c x) := by
      rw [dot_colEval_eq_dot_rowEval A x y]
      ring
    _ = dot (primalSlack A b x) y + dot (dualSlack A c y) x := by
      simp [dot, primalSlack, dualSlack, Finset.sum_sub_distrib, mul_sub, mul_comm]

private theorem eq_zero_of_sum_nonneg_of_le_zero {ι : Type*} [Fintype ι]
    {f : ι → ℝ} (hnonneg : ∀ i, 0 ≤ f i) (hle : (∑ i, f i) ≤ 0) (i : ι) :
    f i = 0 := by
  have hsum_nonneg : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun j _ => hnonneg j
  have hsum : ∑ i, f i = 0 := le_antisymm hle hsum_nonneg
  exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)

private theorem slackTerm_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y)
    (hgap : primalValue c x = dualValue b y) (k : Row ⊕ Col) :
    Sum.elim
      (fun i => primalSlack A b x i * y i)
      (fun j => dualSlack A c y j * x j) k = 0 := by
  let ps := primalSlack A b x
  let ds := dualSlack A c y
  have hps : Nonnegative ps := primalSlack_nonnegative hx
  have hds : Nonnegative ds := dualSlack_nonnegative hy
  have hnonneg_terms : ∀ k : Row ⊕ Col,
      0 ≤ Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k := by
    intro k
    cases k with
    | inl i => exact mul_nonneg (hps i) (hy.1 i)
    | inr j => exact mul_nonneg (hds j) (hx.1 j)
  have hle : (∑ k : Row ⊕ Col,
      Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k) ≤ 0 := by
    rw [Fintype.sum_sum_type]
    have h := duality_gap_eq_slack_sum (A := A) (b := b) (c := c) (x := x) (y := y)
    change dot ps y + dot ds x ≤ 0
    rw [← h, ← hgap]
    simp
  exact eq_zero_of_sum_nonneg_of_le_zero hnonneg_terms hle k

/-- If primal and dual feasible points have equal objective values, every primal
slack is complementary to the corresponding dual variable. -/
theorem primalSlack_mul_dual_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y)
    (hgap : primalValue c x = dualValue b y) (i : Row) :
    primalSlack A b x i * y i = 0 := by
  simpa using slackTerm_eq_zero_of_gap_zero hx hy hgap (Sum.inl i)

/-- If primal and dual feasible points have equal objective values, every dual
slack is complementary to the corresponding primal variable. -/
theorem dualSlack_mul_primal_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : PrimalFeasible A b x) (hy : DualFeasible A c y)
    (hgap : primalValue c x = dualValue b y) (j : Col) :
    dualSlack A c y j * x j = 0 := by
  simpa using slackTerm_eq_zero_of_gap_zero hx hy hgap (Sum.inr j)

end LinearProgramming
end Math
