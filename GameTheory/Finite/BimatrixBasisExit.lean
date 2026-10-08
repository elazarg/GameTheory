import GameTheory.Finite.BimatrixBasis
import GameTheory.Math.NonnegativeDictionary

/-! # Every positive-payoff basis has an exit

All system columns are nonnegative, and every slack or payoff column has a
positive coordinate. Consequently each entering variable has a unique symbolic
leaving row in every feasible basis, including degenerate games.
-/

namespace GameTheory.Finite

open GameTheory.Math GameTheory.Math.CanonicalDictionary

variable {m n : ℕ}

/-- Nonnegative payoffs give nonnegative slack and payoff system columns. -/
theorem bimatrixBasisColumns_nonneg (A B : Fin m → Fin n → ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i : Fin (m + n)) (v : BimatrixVariable m n) :
    0 ≤ bimatrixBasisColumns A B i v := by
  unfold bimatrixBasisColumns
  split
  · unfold bimatrixEnteringColumn
    cases hi : finSumFinEquiv.symm i <;> cases hv : finSumFinEquiv.symm (ofLex v).1 <;>
      simp only [bimatrixComplementaryMatrix, neg_zero, neg_neg]
    · exact le_refl 0
    · exact_mod_cast hA _ _
    · exact_mod_cast hB _ _
    · exact le_refl 0
  · simp only [Pi.single_apply]
    split <;> norm_num

/-- Every system variable has a positive column coordinate when both players are nonempty. -/
theorem bimatrixBasisColumns_positive (A B : Fin m → Fin n → ℤ)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (v : BimatrixVariable m n) : ∃ i, 0 < bimatrixBasisColumns A B i v := by
  unfold bimatrixBasisColumns
  split
  · exact bimatrixEnteringColumn_positive A B hm hn hA hB _
  · refine ⟨(ofLex v).1, ?_⟩
    simp

namespace BimatrixBasis

/-- No entering variable can terminate in a ray in a positive-payoff basis. -/
theorem exists_positive_direction {A B : Fin m → Fin n → ℤ} (basis : BimatrixBasis A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (entering : BimatrixVariable m n) :
    ∃ i, 0 < (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
      (fun j => bimatrixBasisColumns A B j entering) i := by
  apply exists_positive_inverse_mulVec _ _ basis.feasible.1
  · intro i j
    exact bimatrixBasisColumns_nonneg A B (fun i j => (hA i j).le)
      (fun i j => (hB i j).le) i _
  · exact bimatrixBasisColumns_positive A B hm hn hA hB entering

/-- Every entering variable has exactly one symbolic minimum-ratio leaving row. -/
theorem exists_unique_leavingRow {A B : Fin m → Fin n → ℤ} (basis : BimatrixBasis A B)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (entering : BimatrixVariable m n) :
    ∃! l, IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality) (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns A B i entering)) l := by
  exact CanonicalDictionary.exists_unique_leavingRow _ _ _ _ basis.feasible entering
    (basis.exists_positive_direction hm hn hA hB entering)

end BimatrixBasis
end GameTheory.Finite
