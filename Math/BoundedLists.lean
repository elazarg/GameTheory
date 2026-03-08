import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union

/-!
# Bounded Lists

Finite enumeration of lists of bounded length over a finite alphabet.

- `listsOfLength s n` — lists of length exactly `n` with elements from `s`
- `listsUpToLength s n` — lists of length at most `n` with elements from `s`
-/

namespace Math.BoundedLists

variable {α : Type}

/-- Finite enumeration of lists of length exactly `n` over a finite alphabet
`s`. -/
def listsOfLength [DecidableEq α] (s : Finset α) : Nat → Finset (List α)
  | 0 => {[]}
  | n + 1 => (s ×ˢ (listsOfLength s n)).image (fun p => p.1 :: p.2)

/-- Finite enumeration of lists of length at most `n` over a finite alphabet
`s`. -/
def listsUpToLength [DecidableEq α] (s : Finset α) (n : Nat) : Finset (List α) :=
  (Finset.range (n + 1)).biUnion (fun k => listsOfLength s k)

theorem mem_listsOfLength_of_forall_mem [DecidableEq α]
    {s : Finset α} :
    ∀ {xs : List α} {n : Nat},
      xs.length = n →
      (∀ x ∈ xs, x ∈ s) →
      xs ∈ listsOfLength s n
  | [], 0, hlen, _ => by simp [listsOfLength]
  | [], n + 1, hlen, _ => by cases hlen
  | x :: xs, 0, hlen, _ => by cases hlen
  | x :: xs, n + 1, hlen, hmem => by
      have hx : x ∈ s := hmem x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ s := by
        intro y hy
        exact hmem y (by simp [hy])
      have htail : xs.length = n := by simpa using Nat.succ.inj hlen
      have hrec : xs ∈ listsOfLength s n :=
        mem_listsOfLength_of_forall_mem htail hxs
      refine Finset.mem_image.mpr ?_
      refine ⟨(x, xs), ?_, by simp⟩
      simp [hx, hrec]

theorem mem_listsUpToLength_of_forall_mem [DecidableEq α]
    {s : Finset α} {xs : List α} {n : Nat}
    (hlen : xs.length ≤ n)
    (hmem : ∀ x ∈ xs, x ∈ s) :
    xs ∈ listsUpToLength s n := by
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨xs.length, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlen)
  · exact mem_listsOfLength_of_forall_mem (s := s) rfl hmem

end Math.BoundedLists
