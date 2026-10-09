import GameTheoryComplexity.Backend.BinarySignedAddition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Signed summation over a fixed, compile-time number of indexed queries. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

/-- Sum a fixed number of signed queries; indexed rulers have canonical false contents. -/
def binarySignedFiniteSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool) :
    ℕ → (Fin p → List Bool) → List Bool
  | 0, _ => []
  | n + 1, params => binarySignedAdd (binarySignedFiniteSum term n params)
      (term (Fin.cons (List.replicate n false) params))

/-- The count is fixed in the polynomial-time certificate. -/
theorem binarySignedFiniteSum_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) (n : ℕ) :
    Cobham (binarySignedFiniteSum term n) := by
  induction n with
  | zero => exact Cobham.empty
  | succ n ih =>
    have hg : ∀ i : Fin (p + 1), Cobham fun v : Fin p → List Bool =>
        (Fin.cons (List.replicate n false) v : Fin (p + 1) → List Bool) i := by
      intro i
      exact Fin.cases (Cobham.const (List.replicate n false)) (fun a => .proj a) i
    exact Cobham.comp₂ binarySignedAdd_cobham ih (Cobham.comp ht hg)

theorem binarySignedFiniteSum_mem_FPn {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) (n : ℕ) :
    FPn (binarySignedFiniteSum term n) := cobham_iff_FPn.mp (binarySignedFiniteSum_cobham ht n)

/-- Signed values add exactly, without field-width or sign assumptions. -/
theorem binarySignedFiniteSum_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (n : ℕ) (params : Fin p → List Bool) :
    binarySignedValue (binarySignedFiniteSum term n params) =
      ∑ i ∈ Finset.range n,
        binarySignedValue (term (Fin.cons (List.replicate i false) params)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binarySignedFiniteSum, binarySignedAdd_value, ih, Finset.sum_range_succ]

/-- Add a fixed list of signed query machines; the list is fixed in its FP certificate. -/
def binarySignedQuerySum {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool)) (v : Fin p → List Bool) : List Bool :=
  queries.foldr (fun query rest => binarySignedAdd (query v) rest) []

/-- A fixed finite collection of polynomial-time queries has a polynomial-time signed sum. -/
theorem binarySignedQuerySum_cobham {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool))
    (hq : ∀ query ∈ queries, Cobham query) : Cobham (binarySignedQuerySum queries) := by
  induction queries with
  | nil => exact Cobham.empty
  | cons query queries ih =>
    have ht : Cobham (binarySignedQuerySum queries) :=
      ih (fun q h => hq q (List.mem_cons_of_mem _ h))
    exact (Cobham.comp₂ binarySignedAdd_cobham (hq query (List.mem_cons_self)) ht).of_eq
      fun _ => rfl

theorem binarySignedQuerySum_mem_FPn {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool))
    (hq : ∀ query ∈ queries, Cobham query) : FPn (binarySignedQuerySum queries) :=
  cobham_iff_FPn.mp (binarySignedQuerySum_cobham queries hq)

/-- Signed values add without overflow or representation assumptions. -/
theorem binarySignedQuerySum_value {p : ℕ}
    (queries : List ((Fin p → List Bool) → List Bool)) (v : Fin p → List Bool) :
    binarySignedValue (binarySignedQuerySum queries v) =
      (queries.map fun query => binarySignedValue (query v)).sum := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    change binarySignedValue (binarySignedAdd (query v) (binarySignedQuerySum queries v)) = _
    rw [binarySignedAdd_value, ih]
    rfl

end GameTheory.Complexity.Backend
