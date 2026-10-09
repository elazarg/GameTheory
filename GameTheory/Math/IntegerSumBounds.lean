import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! Uniform integer magnitude bounds for finite sums before cancellation. -/
namespace GameTheory.Math.IntegerSumBounds
open scoped BigOperators

/-- Bound a finite integer sum by the number of terms times their common magnitude. -/
theorem natAbs_sum_le_card_mul {α : Type*} (s : Finset α) (f : α → ℤ) (C : ℕ)
    (hf : ∀ i ∈ s, (f i).natAbs ≤ C) : (∑ i ∈ s, f i).natAbs ≤ s.card * C := by
  calc
    _ ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ s, C := Finset.sum_le_sum hf
    _ = s.card * C := by simp

/-- The ambient finite cardinality also bounds sums over any subset. -/
theorem natAbs_sum_le_card {α : Type*} [Fintype α] (s : Finset α) (f : α → ℤ)
    (C : ℕ) (hf : ∀ i ∈ s, (f i).natAbs ≤ C) :
    (∑ i ∈ s, f i).natAbs ≤ Fintype.card α * C :=
  (natAbs_sum_le_card_mul s f C hf).trans (Nat.mul_le_mul_right C (Finset.card_le_univ s))

/-- A bounded prefix has at most the full number of uniformly bounded terms. -/
theorem natAbs_sum_range_le (f : ℕ → ℤ) (n t C : ℕ) (ht : t ≤ n)
    (hf : ∀ i < n, (f i).natAbs ≤ C) : (∑ i ∈ Finset.range t, f i).natAbs ≤ n * C := by
  have h := natAbs_sum_le_card_mul (Finset.range t) f C (fun i hi =>
    hf i ((Finset.mem_range.mp hi).trans_le ht))
  rw [Finset.card_range] at h
  exact h.trans (Nat.mul_le_mul_right C ht)

end GameTheory.Math.IntegerSumBounds
