import GameTheory.Finite.BimatrixComplementarity
import GameTheory.Math.LexicographicPivot
import Mathlib.Logic.Equiv.Fin.Basic

/-! The first symbolic pivot of the bimatrix complementarity system.

The all-slack basis represents the artificial zero source. Strictly positive
payoffs supply an eligible leaving row for every entering label; symbolic
perturbations select it uniquely even for fully degenerate games.
-/

namespace GameTheory.Finite

open GameTheory.Math GameTheory.Math.PerturbedDictionary

variable {m n : ℕ}

/-- The payoff-variable column in the equation `w - M z = 1`. -/
def bimatrixEnteringColumn (A B : Fin m → Fin n → ℤ)
    (label : Fin m ⊕ Fin n) : Fin (m + n) → ℚ :=
  fun i => -bimatrixComplementaryMatrix A B (finSumFinEquiv.symm i) label

/-- Positive payoffs ensure that every label has an eligible source pivot row. -/
theorem bimatrixEnteringColumn_positive (A B : Fin m → Fin n → ℤ)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (label : Fin m ⊕ Fin n) : ∃ i, 0 < bimatrixEnteringColumn A B label i := by
  cases label with
  | inl i =>
    refine ⟨finSumFinEquiv (.inr ⟨0, hn⟩), ?_⟩
    simpa only [bimatrixEnteringColumn, Equiv.symm_apply_apply,
      bimatrixComplementaryMatrix, neg_neg] using
      (show (0 : ℚ) < (B i ⟨0, hn⟩ : ℚ) by exact_mod_cast hB i ⟨0, hn⟩)
  | inr j =>
    refine ⟨finSumFinEquiv (.inl ⟨0, hm⟩), ?_⟩
    simpa only [bimatrixEnteringColumn, Equiv.symm_apply_apply,
      bimatrixComplementaryMatrix, neg_neg] using
      (show (0 : ℚ) < (A ⟨0, hm⟩ j : ℚ) by exact_mod_cast hA ⟨0, hm⟩ j)

/-- Every all-slack source coordinate has a strictly positive constant term. -/
theorem bimatrixSource_coefficients_positive (i : Fin (m + n)) :
    0 < toLex (dictionaryCoefficients (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)
      (fun _ => 1) i) := by
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact (Fin.not_lt_zero j hj).elim
  · change 0 < dictionaryCoefficients (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)
      (fun _ => 1) i 0
    simp

/-- The source has a unique symbolic minimum-ratio leaving row. -/
theorem exists_unique_bimatrixSource_leavingRow (A B : Fin m → Fin n → ℤ)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (label : Fin m ⊕ Fin n) :
    ∃! l, IsLeavingRow
      (dictionaryCoefficients (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ) (fun _ => 1))
      (bimatrixEnteringColumn A B label) l := by
  simpa only [inv_one, Matrix.one_mulVec] using
    exists_unique_dictionary_leavingRow
      (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ) (fun _ => 1)
      (bimatrixEnteringColumn A B label) (by simp)
      (by simpa only [inv_one, Matrix.one_mulVec] using
        bimatrixEnteringColumn_positive A B hm hn hA hB label)

/-- A selected source pivot produces an invertible and strictly feasible basis. -/
theorem bimatrixSource_successor_feasible (A B : Fin m → Fin n → ℤ)
    (label : Fin m ⊕ Fin n) (l : Fin (m + n))
    (hl : IsLeavingRow
      (dictionaryCoefficients (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ) (fun _ => 1))
      (bimatrixEnteringColumn A B label) l) :
    ((1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ).updateCol l
      (bimatrixEnteringColumn A B label)).det ≠ 0 ∧
    ∀ i, 0 < toLex (dictionaryCoefficients
      ((1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ).updateCol l
        (bimatrixEnteringColumn A B label)) (fun _ => 1) i) := by
  have hl' : IsLeavingRow
      (dictionaryCoefficients (1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ) (fun _ => 1))
      ((1 : Matrix (Fin (m + n)) (Fin (m + n)) ℚ)⁻¹.mulVec
        (bimatrixEnteringColumn A B label)) l := by
    simpa only [inv_one, Matrix.one_mulVec] using hl
  exact ⟨updated_det_ne_zero _ _ _ (by simp) hl'.1.ne',
    dictionaryCoefficients_updated_positive _ _ _ _ (by simp)
      bimatrixSource_coefficients_positive hl'⟩

end GameTheory.Finite
