/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bonferroni bounds for independent absorption

For weights `w j ∈ [0, 1]` indexed by a finite set `s`, the quantity
`1 - ∏ j ∈ s, (1 - w j)` is the probability that at least one of `s`
independent events occurs.  Inclusion-exclusion truncated after one term
gives the union bound

  `1 - ∏ j ∈ s, (1 - w j) ≤ ∑ j ∈ s, w j`,

and truncated after two terms gives the opposite Bonferroni bound

  `∑ j ∈ s, w j - ∑ j < k, w j * w k ≤ 1 - ∏ j ∈ s, (1 - w j)`.

Both are stated over an arbitrary `Finset`; nothing here refers to a game.

The pair sum is packaged as `Math.pairMulSum`, defined order-free as half of
the off-diagonal sum `∑ j ≠ k, w j * w k`.  Each unordered pair `{j, k}`
contributes `w j * w k` exactly twice to the off-diagonal sum, so this is the
usual `∑ j < k, w j * w k`; `Math.pairMulSum_eq` pins it down without any
choice of order as `((∑ w) ^ 2 - ∑ w ^ 2) / 2`.

Since `pairMulSum w s ≤ (∑ j ∈ s, w j) ^ 2 / 2`, the two bounds combine into
the single two-sided estimate

  `|(1 - ∏ j ∈ s, (1 - w j)) - ∑ j ∈ s, w j| ≤ (∑ j ∈ s, w j) ^ 2 / 2`,

which is the form that makes absorption and total weight asymptotically
equal along any family whose total weight vanishes.

Mathlib has `Finset.prod_one_sub_ordered` (an exact identity) but neither of
these inequalities.
-/

set_option autoImplicit false

namespace Math

variable {ι : Type*}

/-! ## The unordered pair sum -/

/-- The unordered pair sum `∑ j < k, w j * w k` over `s`, defined without a
choice of order as half of the off-diagonal sum `∑ j ≠ k, w j * w k`. -/
noncomputable def pairMulSum (w : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ p ∈ s.offDiag, w p.1 * w p.2) / 2

/-- The off-diagonal sum `∑ j ≠ k, w j * w k` is `(∑ w) ^ 2 - ∑ w ^ 2`. -/
theorem sum_offDiag_mul_eq (w : ι → ℝ) (s : Finset ι) :
    ∑ p ∈ s.offDiag, w p.1 * w p.2 =
      (∑ j ∈ s, w j) ^ 2 - ∑ j ∈ s, w j ^ 2 := by
  classical
  have hsplit :
      (∑ p ∈ s.diag, w p.1 * w p.2) + ∑ p ∈ s.offDiag, w p.1 * w p.2 =
        ∑ p ∈ s ×ˢ s, w p.1 * w p.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag s),
      Finset.diag_union_offDiag]
  have hdiag : ∑ p ∈ s.diag, w p.1 * w p.2 = ∑ j ∈ s, w j ^ 2 := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsquare : ∑ p ∈ s ×ˢ s, w p.1 * w p.2 = (∑ j ∈ s, w j) ^ 2 := by
    rw [Finset.sum_product, sq, Finset.sum_mul_sum]
  linarith

/-- Order-free description of the pair sum. -/
theorem pairMulSum_eq (w : ι → ℝ) (s : Finset ι) :
    pairMulSum w s = ((∑ j ∈ s, w j) ^ 2 - ∑ j ∈ s, w j ^ 2) / 2 := by
  unfold pairMulSum
  rw [sum_offDiag_mul_eq]

@[simp] theorem pairMulSum_empty (w : ι → ℝ) :
    pairMulSum w (∅ : Finset ι) = 0 := by
  simp [pairMulSum]

/-- Adjoining one index adds its weight times the previous total. -/
theorem pairMulSum_insert [DecidableEq ι] (w : ι → ℝ) {a : ι}
    {s : Finset ι} (ha : a ∉ s) :
    pairMulSum w (insert a s) = pairMulSum w s + w a * ∑ j ∈ s, w j := by
  rw [pairMulSum_eq, pairMulSum_eq]
  simp only [Finset.sum_insert ha]
  ring

/-- Nonnegative weights have a nonnegative pair sum. -/
theorem pairMulSum_nonneg (w : ι → ℝ) (s : Finset ι)
    (h0 : ∀ j ∈ s, 0 ≤ w j) : 0 ≤ pairMulSum w s := by
  have hsum : 0 ≤ ∑ p ∈ s.offDiag, w p.1 * w p.2 :=
    Finset.sum_nonneg fun p hp => by
      rw [Finset.mem_offDiag] at hp
      exact mul_nonneg (h0 p.1 hp.1) (h0 p.2 hp.2.1)
  unfold pairMulSum
  linarith

/-- The pair sum is at most half the squared total. -/
theorem pairMulSum_le_sq_sum_div_two (w : ι → ℝ) (s : Finset ι) :
    pairMulSum w s ≤ (∑ j ∈ s, w j) ^ 2 / 2 := by
  have hsq : 0 ≤ ∑ j ∈ s, w j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (w j)
  rw [pairMulSum_eq]
  linarith

/-! ## The two Bonferroni bounds -/

/-- **First Bonferroni bound (union bound).**  Independent absorption is at
most the total weight. -/
theorem one_sub_prod_one_sub_le_sum (w : ι → ℝ) (s : Finset ι)
    (h0 : ∀ j ∈ s, 0 ≤ w j) (h1 : ∀ j ∈ s, w j ≤ 1) :
    1 - ∏ j ∈ s, (1 - w j) ≤ ∑ j ∈ s, w j := by
  classical
  revert h0 h1
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih h0 h1
  have ha0 : 0 ≤ w a := h0 a (Finset.mem_insert_self a s)
  have h0' : ∀ j ∈ s, 0 ≤ w j := fun j hj =>
    h0 j (Finset.mem_insert_of_mem hj)
  have h1' : ∀ j ∈ s, w j ≤ 1 := fun j hj =>
    h1 j (Finset.mem_insert_of_mem hj)
  have hprod : ∏ j ∈ s, (1 - w j) ≤ 1 :=
    Finset.prod_le_one (fun j hj => by linarith [h1' j hj])
      (fun j hj => by linarith [h0' j hj])
  have hih := ih h0' h1'
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  nlinarith [mul_le_mul_of_nonneg_left hprod ha0]

/-- **Second Bonferroni bound.**  Independent absorption is at least the
total weight minus the sum over unordered pairs. -/
theorem sum_sub_pairMulSum_le_one_sub_prod_one_sub (w : ι → ℝ)
    (s : Finset ι) (h0 : ∀ j ∈ s, 0 ≤ w j) (h1 : ∀ j ∈ s, w j ≤ 1) :
    ∑ j ∈ s, w j - pairMulSum w s ≤ 1 - ∏ j ∈ s, (1 - w j) := by
  classical
  revert h0 h1
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih h0 h1
  have ha0 : 0 ≤ w a := h0 a (Finset.mem_insert_self a s)
  have ha1 : w a ≤ 1 := h1 a (Finset.mem_insert_self a s)
  have h0' : ∀ j ∈ s, 0 ≤ w j := fun j hj =>
    h0 j (Finset.mem_insert_of_mem hj)
  have h1' : ∀ j ∈ s, w j ≤ 1 := fun j hj =>
    h1 j (Finset.mem_insert_of_mem hj)
  have hpair : 0 ≤ pairMulSum w s := pairMulSum_nonneg w s h0'
  have hih := ih h0' h1'
  rw [Finset.sum_insert ha, Finset.prod_insert ha, pairMulSum_insert w ha]
  nlinarith [mul_nonneg ha0 hpair,
    mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hih)]

/-- Crude form of the second Bonferroni bound: the quadratic correction is at
most half the squared total weight. -/
theorem sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub (w : ι → ℝ)
    (s : Finset ι) (h0 : ∀ j ∈ s, 0 ≤ w j) (h1 : ∀ j ∈ s, w j ≤ 1) :
    ∑ j ∈ s, w j - (∑ j ∈ s, w j) ^ 2 / 2 ≤ 1 - ∏ j ∈ s, (1 - w j) := by
  have hsharp := sum_sub_pairMulSum_le_one_sub_prod_one_sub w s h0 h1
  have hpair := pairMulSum_le_sq_sum_div_two w s
  linarith

/-- **Two-sided Bonferroni estimate.**  Independent absorption differs from
the total weight by at most half the squared total weight.  Along a family
with `∑ j ∈ s, w j → 0` this forces the ratio of absorption to total weight
to tend to `1`. -/
theorem abs_one_sub_prod_one_sub_sub_sum_le_sq_sum_div_two (w : ι → ℝ)
    (s : Finset ι) (h0 : ∀ j ∈ s, 0 ≤ w j) (h1 : ∀ j ∈ s, w j ≤ 1) :
    |(1 - ∏ j ∈ s, (1 - w j)) - ∑ j ∈ s, w j| ≤ (∑ j ∈ s, w j) ^ 2 / 2 := by
  have hupper := one_sub_prod_one_sub_le_sum w s h0 h1
  have hlower := sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub w s h0 h1
  have hsq : 0 ≤ (∑ j ∈ s, w j) ^ 2 / 2 := by positivity
  rw [abs_le]
  constructor <;> linarith

end Math
