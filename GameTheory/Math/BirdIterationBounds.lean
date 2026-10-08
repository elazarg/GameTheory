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

private theorem sum_bound {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℤ) (T : ℕ)
    (hf : ∀ k ∈ s, (f k).natAbs ≤ T) : (∑ k ∈ s, f k).natAbs ≤ n * T := by
  calc
    (∑ k ∈ s, f k).natAbs ≤ ∑ k ∈ s, (f k).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k ∈ s, T := Finset.sum_le_sum hf
    _ = s.card * T := by simp
    _ ≤ n * T := Nat.mul_le_mul_right T (by simpa using Finset.card_le_univ s)

/-- One recurrence step has at most two sums of `n` products of bounded entries. -/
theorem step_bound {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (B T : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) (hF : ∀ i j, (F i j).natAbs ≤ T)
    (i j : Fin n) : (BirdDet.Spec.stepEntry A F i j).natAbs ≤ 2 * n * T * B := by
  have hdiag := sum_bound (Finset.Ioi i) (fun k => F k k) T (fun k _ => hF k k)
  have hsum := sum_bound (Finset.Ioi i) (fun k => F i k * A k j) (T * B)
    (fun k _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hF i k) (hA k j))
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
