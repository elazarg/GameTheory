import Mathlib.Data.List.Basic

/-! Length and indexed extraction of equal-width blocks concatenated from a list. -/
namespace GameTheory.Math.FixedBlockList

/-- Concatenating equal-width blocks multiplies their count by their width. -/
theorem length_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) :
    (xs.flatMap f).length = xs.length * w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ha, ih ht]
    simp [Nat.add_mul, Nat.add_comm]

/-- Dropping whole blocks and taking one width recovers the indexed block. -/
theorem block_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) (k : ℕ) (hk : k < xs.length) :
    ((xs.flatMap f).drop (k * w)).take w = f xs[k] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    cases k with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
      rw [← ha, List.take_append_length]
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      simp only [List.flatMap_cons, Nat.succ_mul, List.getElem_cons_succ]
      rw [Nat.add_comm, ← ha, List.drop_length_add_append]
      simpa only [ha] using ih ht k hk'

end GameTheory.Math.FixedBlockList
