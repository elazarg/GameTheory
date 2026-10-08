import GameTheory.Math.FiniteBasisExchange
import GameTheory.Math.DictionaryReindex

/-! Sorted finite sets give one dictionary for each basis. Sorting a column
replacement permutes the basis coordinates and preserves symbolic feasibility.
-/
namespace GameTheory.Math.CanonicalDictionary
open GameTheory.Math GameTheory.Math.PerturbedDictionary FiniteBasisExchange
variable {α K : Type*} [LinearOrder α] [DecidableEq α] [Field K] {n : ℕ}

/-- Basis columns enumerated in their canonical increasing order. -/
def basisMatrix (columns : Matrix (Fin n) α K) (s : Finset α) (hs : s.card = n) :
    Matrix (Fin n) (Fin n) K := fun i j => columns i (s.orderEmbOfFin hs j)

omit [Field K] in
/-- Sorting an exchanged basis only reorders the raw matrix column replacement. -/
theorem basisMatrix_exchange (columns : Matrix (Fin n) α K)
    (s : Finset α) (hs : s.card = n) (l : Fin n) (entering : α) (he : entering ∉ s) :
    basisMatrix columns (exchange s (s.orderEmbOfFin hs l) entering)
      ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs) =
    ((basisMatrix columns s hs).updateCol l (fun i => columns i entering)).submatrix
      (Equiv.refl _) (exchangePermutation s hs l entering he) := by
  ext i j
  simp only [basisMatrix, Matrix.submatrix_apply, Equiv.refl_apply, Matrix.updateCol_apply]
  rw [exchangePermutation_apply s hs l entering he j]
  unfold exchangeEnumeration
  split <;> rfl

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

/-- An invertible dictionary with strictly positive symbolic coordinates. -/
def IsFeasible (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) : Prop :=
  (basisMatrix columns s hs).det ≠ 0 ∧
    ∀ i, 0 < toLex (dictionaryCoefficients (basisMatrix columns s hs) q i)

omit [DecidableEq α] [IsStrictOrderedRing K] in
/-- An entering column has a unique leaving row whenever an eligible row exists. -/
theorem exists_unique_leavingRow (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) (h : IsFeasible columns q s hs)
    (entering : α) (hexit : ∃ i, 0 < (basisMatrix columns s hs)⁻¹.mulVec
      (fun j => columns j entering) i) :
    ∃! l, IsLeavingRow (dictionaryCoefficients (basisMatrix columns s hs) q)
      ((basisMatrix columns s hs)⁻¹.mulVec (fun j => columns j entering)) l :=
  exists_unique_dictionary_leavingRow _ _ _ h.1 hexit

/-- Replacing the selected column and canonically sorting preserves feasibility. -/
theorem exchange_feasible (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) (h : IsFeasible columns q s hs)
    (l : Fin n) (entering : α) (he : entering ∉ s)
    (hl : IsLeavingRow (dictionaryCoefficients (basisMatrix columns s hs) q)
      ((basisMatrix columns s hs)⁻¹.mulVec (fun j => columns j entering)) l) :
    IsFeasible columns q (exchange s (s.orderEmbOfFin hs l) entering)
      ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs) := by
  unfold IsFeasible
  rw [basisMatrix_exchange columns s hs l entering he]
  exact ⟨(determinant_column_permutation_ne_zero_iff _ _).mpr
    (updated_det_ne_zero _ _ _ h.1 hl.1.ne'),
    (dictionary_positive_column_permutation_iff _ _ _).mpr
      (dictionaryCoefficients_updated_positive _ _ _ _ h.1 h.2 hl)⟩

/-- In the sorted successor, the old column selects the corresponding reverse row. -/
theorem exchange_reverse_leavingRow (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) (h : IsFeasible columns q s hs)
    (l : Fin n) (entering : α) (he : entering ∉ s)
    (hl : IsLeavingRow (dictionaryCoefficients (basisMatrix columns s hs) q)
      ((basisMatrix columns s hs)⁻¹.mulVec (fun j => columns j entering)) l) :
    IsLeavingRow (dictionaryCoefficients (basisMatrix columns
      (exchange s (s.orderEmbOfFin hs l) entering)
      ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs)) q)
      ((basisMatrix columns (exchange s (s.orderEmbOfFin hs l) entering)
      ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs))⁻¹.mulVec
        (fun i => columns i (s.orderEmbOfFin hs l)))
      ((exchangePermutation s hs l entering he).symm l) := by
  rw [basisMatrix_exchange columns s hs l entering he]
  apply (dictionary_isLeavingRow_column_permutation_iff _ _ _ _ _).mpr
  exact dictionary_reverse_isLeavingRow _ _ _ _ h.1 h.2 hl

end Ordered
end GameTheory.Math.CanonicalDictionary
