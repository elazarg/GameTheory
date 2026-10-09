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
      ∑ i ∈ Finset.range n, binarySignedValue (term (Fin.cons (List.replicate i false) params)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binarySignedFiniteSum, binarySignedAdd_value, ih, Finset.sum_range_succ]

end GameTheory.Complexity.Backend
