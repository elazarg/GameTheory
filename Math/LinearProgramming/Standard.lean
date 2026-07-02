/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.Basic

/-!
# Standard-Form Finite Linear Programming

The min-primal/max-dual orientation:

* primal: minimize `c ⬝ x` subject to `A x ≥ b` and `x ≥ 0`;
* dual: maximize `b ⬝ y` subject to `y A ≤ c` and `y ≥ 0`.

This is the orientation used by Farkas-style certificates and by many
cooperative-game applications.
-/

open scoped BigOperators

namespace Math
namespace LinearProgramming

variable {Row Col : Type*} [Fintype Row] [Fintype Col]

/-- Primal feasibility for `min c⬝x` subject to `Ax ≥ b`, `x ≥ 0`. -/
def MinPrimalFeasible (A : Row → Col → ℝ) (b : Row → ℝ) (x : Col → ℝ) : Prop :=
  Nonnegative x ∧ ∀ i, b i ≤ rowEval A x i

/-- Dual feasibility for `max b⬝y` subject to `yA ≤ c`, `y ≥ 0`. -/
def MaxDualFeasible (A : Row → Col → ℝ) (c : Col → ℝ) (y : Row → ℝ) : Prop :=
  Nonnegative y ∧ ∀ j, colEval A y j ≤ c j

/-- Standard-form minimization primal objective value. -/
def minPrimalValue (c : Col → ℝ) (x : Col → ℝ) : ℝ :=
  dot c x

/-- Standard-form maximization dual objective value. -/
def maxDualValue (b : Row → ℝ) (y : Row → ℝ) : ℝ :=
  dot b y

/-- Row slack `Ax - b` for a standard-form primal-feasible point. -/
def minPrimalSlack (A : Row → Col → ℝ) (b : Row → ℝ) (x : Col → ℝ) (i : Row) : ℝ :=
  rowEval A x i - b i

/-- Column slack `c - yA` for a standard-form dual-feasible point. -/
def maxDualSlack (A : Row → Col → ℝ) (c : Col → ℝ) (y : Row → ℝ) (j : Col) : ℝ :=
  c j - colEval A y j

omit [Fintype Row] in
theorem minPrimalSlack_nonnegative {A : Row → Col → ℝ} {b : Row → ℝ} {x : Col → ℝ}
    (hx : MinPrimalFeasible A b x) : Nonnegative (minPrimalSlack A b x) := by
  intro i
  dsimp [minPrimalSlack]
  linarith [hx.2 i]

omit [Fintype Col] in
theorem maxDualSlack_nonnegative {A : Row → Col → ℝ} {c : Col → ℝ} {y : Row → ℝ}
    (hy : MaxDualFeasible A c y) : Nonnegative (maxDualSlack A c y) := by
  intro j
  dsimp [maxDualSlack]
  linarith [hy.2 j]

/-- Weak duality for finite standard-form LPs. -/
theorem min_weak_duality {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : MinPrimalFeasible A b x) (hy : MaxDualFeasible A c y) :
    maxDualValue b y ≤ minPrimalValue c x := by
  calc
    maxDualValue b y = dot b y := rfl
    _ ≤ dot (rowEval A x) y :=
      dot_mono_of_nonnegative_right hx.2 hy.1
    _ = dot (colEval A y) x := by
      rw [dot_comm, dot_colEval_eq_dot_rowEval]
    _ ≤ dot c x :=
      dot_mono_of_nonnegative_right hy.2 hx.1
    _ = minPrimalValue c x := rfl

/-- The standard-form duality gap decomposes into primal and dual slack terms. -/
theorem min_duality_gap_eq_slack_sum
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ} :
    minPrimalValue c x - maxDualValue b y =
      dot (minPrimalSlack A b x) y + dot (maxDualSlack A c y) x := by
  classical
  rw [minPrimalValue, maxDualValue]
  calc
    dot c x - dot b y =
        (dot y (rowEval A x) - dot b y) + (dot c x - dot (colEval A y) x) := by
      rw [← dot_colEval_eq_dot_rowEval A x y]
      ring
    _ = dot (minPrimalSlack A b x) y + dot (maxDualSlack A c y) x := by
      simp [dot, minPrimalSlack, maxDualSlack, Finset.sum_sub_distrib, mul_sub, mul_comm]

private theorem standardSlackTerm_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : MinPrimalFeasible A b x) (hy : MaxDualFeasible A c y)
    (hgap : minPrimalValue c x = maxDualValue b y) (k : Row ⊕ Col) :
    Sum.elim
      (fun i => minPrimalSlack A b x i * y i)
      (fun j => maxDualSlack A c y j * x j) k = 0 := by
  let ps := minPrimalSlack A b x
  let ds := maxDualSlack A c y
  have hps : Nonnegative ps := minPrimalSlack_nonnegative hx
  have hds : Nonnegative ds := maxDualSlack_nonnegative hy
  have hnonneg_terms : ∀ k : Row ⊕ Col,
      0 ≤ Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k := by
    intro k
    cases k with
    | inl i => exact mul_nonneg (hps i) (hy.1 i)
    | inr j => exact mul_nonneg (hds j) (hx.1 j)
  have hle : (∑ k : Row ⊕ Col,
      Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k) ≤ 0 := by
    rw [Fintype.sum_sum_type]
    have h := min_duality_gap_eq_slack_sum (A := A) (b := b) (c := c) (x := x) (y := y)
    change dot ps y + dot ds x ≤ 0
    rw [← h, hgap]
    simp
  have hsum_nonneg : 0 ≤ ∑ k : Row ⊕ Col,
      Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k :=
    Finset.sum_nonneg fun k _ => hnonneg_terms k
  have hsum : (∑ k : Row ⊕ Col,
      Sum.elim (fun i => ps i * y i) (fun j => ds j * x j) k) = 0 :=
    le_antisymm hle hsum_nonneg
  exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun k _ => hnonneg_terms k)).mp hsum k (Finset.mem_univ k)

/-- At zero standard-form duality gap, every primal slack is complementary to
the corresponding dual variable. -/
theorem minPrimalSlack_mul_dual_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : MinPrimalFeasible A b x) (hy : MaxDualFeasible A c y)
    (hgap : minPrimalValue c x = maxDualValue b y) (i : Row) :
    minPrimalSlack A b x i * y i = 0 := by
  simpa using standardSlackTerm_eq_zero_of_gap_zero hx hy hgap (Sum.inl i)

/-- At zero standard-form duality gap, every dual slack is complementary to
the corresponding primal variable. -/
theorem maxDualSlack_mul_primal_eq_zero_of_gap_zero
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (hx : MinPrimalFeasible A b x) (hy : MaxDualFeasible A c y)
    (hgap : minPrimalValue c x = maxDualValue b y) (j : Col) :
    maxDualSlack A c y j * x j = 0 := by
  simpa using standardSlackTerm_eq_zero_of_gap_zero hx hy hgap (Sum.inr j)

end LinearProgramming
end Math
