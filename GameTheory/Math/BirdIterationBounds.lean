import GameTheory.Math.IntegerSumBounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer magnitude bounds for Bird's division-free determinant recurrence.

Each stage uses only sums and products. A uniform entry bound therefore grows
by at most a linear factor in the dimension and the input magnitude per stage,
giving polynomial binary widths throughout the determinant computation.
-/

namespace GameTheory.Math.BirdIterationBounds

open scoped BigOperators
open Function

/-- Every partial diagonal sum has the same dimension-times-entry bound. -/
theorem diagonal_sum_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℤ) (T : ℕ)
    (hF : ∀ i j, (F i j).natAbs ≤ T) (s : Finset (Fin n)) :
    (∑ k ∈ s, F k k).natAbs ≤ n * T :=
  by simpa using IntegerSumBounds.natAbs_sum_le_card s (fun k => F k k) T (fun k _ => hF k k)

/-- Any partial row product sum is bounded before cancellation. -/
theorem row_product_sum_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B T : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) (hF : ∀ i j, (F i j).natAbs ≤ T)
    (s : Finset (Fin n)) (i j : Fin n) :
    (∑ k ∈ s, F i k * A k j).natAbs ≤ n * T * B := by
  have hs := IntegerSumBounds.natAbs_sum_le_card s (fun k => F i k * A k j) (T * B)
    (fun k _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hF i k) (hA k j))
  simpa only [Nat.mul_assoc, Fintype.card_fin] using hs

/-- One recurrence step has at most two sums of `n` products of bounded entries. -/
theorem step_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B T : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) (hF : ∀ i j, (F i j).natAbs ≤ T)
    (i j : Fin n) : (BirdDet.Spec.stepEntry A F i j).natAbs ≤ 2 * n * T * B := by
  have hdiag := IntegerSumBounds.natAbs_sum_le_card
    (Finset.Ioi i) (fun k => F k k) T (fun k _ => hF k k)
  have hsum := IntegerSumBounds.natAbs_sum_le_card (Finset.Ioi i) (fun k => F i k * A k j) (T * B)
    (fun k _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hF i k) (hA k j))
  simp only [Fintype.card_fin] at hdiag hsum
  change ((-∑ k ∈ Finset.Ioi i, F k k) * A i j +
    ∑ k ∈ Finset.Ioi i, F i k * A k j).natAbs ≤ _
  calc
    _ ≤ ((-∑ k ∈ Finset.Ioi i, F k k) * A i j).natAbs +
        (∑ k ∈ Finset.Ioi i, F i k * A k j).natAbs := Int.natAbs_add_le _ _
    _ ≤ (n * T) * B + n * (T * B) := by
      rw [Int.natAbs_mul, Int.natAbs_neg]
      exact Nat.add_le_add (Nat.mul_le_mul hdiag (hA i j)) hsum
    _ = 2 * n * T * B := by ring

/-- Magnitude growth of the existing matrix recurrence, with no new stage semantics. -/
theorem stages_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) (t : ℕ) (i j : Fin n) :
    (((BirdDet.Spec.stepEntry A)^[t] A) i j).natAbs ≤ (2 * n * B) ^ t * B := by
  induction t generalizing i j with
  | zero => simpa using hA i j
  | succ t ih =>
    rw [iterate_succ_apply']
    exact (step_bound A _ B ((2 * n * B) ^ t * B) hA ih i j).trans_eq (by
      rw [pow_succ]
      ring)

/-- A polynomial width controlling all entries throughout at most `n` stages. -/
def width (n h : ℕ) : ℕ := (n + 1) * (h + n + 2) + 1

/-- A generous stored field width covering stages and arithmetic prefixes, including a sign bit. -/
def workWidth (n h : ℕ) : ℕ := 2 * width n h + h + 2 * n + 6

theorem workWidth_pos (n h : ℕ) : 0 < workWidth n h := by unfold workWidth; omega

/-- The working field has capacity for both sums and temporary diagonal products. -/
theorem workWidth_capacity (n h : ℕ) :
    2 * n * 2 ^ width n h * 2 ^ h < 2 ^ (workWidth n h - 1) := by
  have hb : 2 * n * 2 ^ width n h * 2 ^ h ≤ 2 ^ (width n h + h + n + 1) := by
    calc
      2 * n * 2 ^ width n h * 2 ^ h ≤
          2 * 2 ^ n * 2 ^ width n h * 2 ^ h := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left 2 n.lt_two_pow_self.le))
      _ = 2 ^ (width n h + h + n + 1) := by simp only [pow_add, pow_one]; ring
  have hexp : width n h + h + n + 1 < workWidth n h - 1 := by unfold workWidth; omega
  exact hb.trans_lt (Nat.pow_lt_pow_right (by decide) hexp)

/-- Working fields also cover every stage entry even in dimension zero. -/
theorem stageWidth_lt_workWidth (n h : ℕ) : width n h < workWidth n h - 1 := by
  unfold workWidth
  omega

/-- Every intermediate stage of the determinant algorithm has polynomial binary width. -/
theorem stages_natAbs_lt_two_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h t : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (ht : t ≤ n) (i j : Fin n) :
    (((BirdDet.Spec.stepEntry A)^[t] A) i j).natAbs < 2 ^ width n h := by
  have hfactor : 2 * n * 2 ^ h ≤ 2 ^ (h + n + 1) := by
    calc
      2 * n * 2 ^ h ≤ 2 * 2 ^ n * 2 ^ h :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 n.lt_two_pow_self.le)
      _ = 2 ^ (h + n + 1) := by simp only [pow_add, pow_one]; ring
  have hgrowth : (2 * n * 2 ^ h) ^ t * 2 ^ h ≤ 2 ^ ((h + n + 1) * t + h) := by
    calc
      (2 * n * 2 ^ h) ^ t * 2 ^ h ≤ (2 ^ (h + n + 1)) ^ t * 2 ^ h :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hfactor t)
      _ = 2 ^ ((h + n + 1) * t + h) := by rw [← pow_mul, ← pow_add]
  have hexp : (h + n + 1) * t + h < width n h := by
    unfold width
    nlinarith
  exact ((stages_bound A (2 ^ h) hA t i j).trans hgrowth).trans_lt
    (Nat.pow_lt_pow_right (by decide) hexp)

end GameTheory.Math.BirdIterationBounds
