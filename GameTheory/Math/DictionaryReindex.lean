import GameTheory.Math.LexicographicPivot

/-! # Permuting dictionary basis columns

Changing the order of basis columns only permutes solution coordinates.
Symbolic perturbation coordinates remain attached to the original equations,
so feasibility and the leaving-row rule survive canonical sorting of a basis.
-/

namespace GameTheory.Math

variable {K : Type*} [Field K] {n k : ℕ}

/-- Permuting basis columns permutes inverse-system coordinates. -/
theorem inverse_mulVec_column_permutation (B : Matrix (Fin n) (Fin n) K)
    (e : Fin n ≃ Fin n) (b : Fin n → K) :
    (B.submatrix (Equiv.refl _) e)⁻¹.mulVec b = fun i => B⁻¹.mulVec b (e i) := by
  rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mulVec_equiv]
  rfl

/-- Perturbation columns keep their original order when basis columns are reordered. -/
theorem dictionaryCoefficients_column_permutation (B : Matrix (Fin n) (Fin n) K)
    (e : Fin n ≃ Fin n) (q : Fin n → K) :
    PerturbedDictionary.dictionaryCoefficients (B.submatrix (Equiv.refl _) e) q =
      fun i => PerturbedDictionary.dictionaryCoefficients B q (e i) := by
  funext i a
  refine Fin.cases ?_ (fun j => ?_) a
  · exact congrFun (inverse_mulVec_column_permutation B e q) i
  · simp only [PerturbedDictionary.coefficient_succ, Matrix.inv_submatrix_equiv,
      Matrix.submatrix_apply, Equiv.refl_apply]

/-- Column reordering does not change whether the basis is invertible. -/
theorem determinant_column_permutation_ne_zero_iff (B : Matrix (Fin n) (Fin n) K)
    (e : Fin n ≃ Fin n) :
    (B.submatrix (Equiv.refl _) e).det ≠ 0 ↔ B.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.isUnit_submatrix_equiv _ _

/-- Coordinate pivoting commutes with permutation of the coordinate rows. -/
theorem pivotVector_permutation (d x : Fin n → K) (e : Fin n ≃ Fin n) (l : Fin n) :
    pivotVector (fun i => d (e i)) (e.symm l) (fun i => x (e i)) =
      fun i => pivotVector d l x (e i) := by
  funext i
  simp only [pivotVector, Equiv.apply_symm_apply]
  have he : i = e.symm l ↔ e i = l := by
    constructor
    · rintro rfl
      exact e.apply_symm_apply l
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply l).symm)
  simp only [he]

theorem pivotCoefficients_permutation (C : Fin n → Fin k → K) (d : Fin n → K)
    (e : Fin n ≃ Fin n) (l : Fin n) :
    pivotCoefficients (fun i => C (e i)) (fun i => d (e i)) (e.symm l) =
      fun i => pivotCoefficients C d l (e i) := by
  funext i a
  exact congrFun (pivotVector_permutation d (fun j => C j a) e l) i

omit [Field K] in
/-- Permuting columns before replacement moves the replacement index by the inverse permutation. -/
theorem updateCol_column_permutation (B : Matrix (Fin n) (Fin n) K)
    (c : Fin n → K) (e : Fin n ≃ Fin n) (l : Fin n) :
    (B.updateCol l c).submatrix (Equiv.refl _) e =
      (B.submatrix (Equiv.refl _) e).updateCol (e.symm l) c := by
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.refl_apply, Matrix.updateCol_apply]
  have he : e j = l ↔ j = e.symm l := by
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply l).symm)
    · rintro rfl
      exact e.apply_symm_apply l
  simp only [he]

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- The symbolic leaving-row condition is independent of basis enumeration. -/
theorem isLeavingRow_permutation_iff (C : Fin n → Fin k → K) (d : Fin n → K)
    (e : Fin n ≃ Fin n) (l : Fin n) :
    IsLeavingRow (fun i => C (e i)) (fun i => d (e i)) (e.symm l) ↔
      IsLeavingRow C d l := by
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨by simpa using hp, ?_⟩
    intro i hi
    simpa using hm (e.symm i) (by simpa using hi)
  · rintro ⟨hp, hm⟩
    refine ⟨by simpa using hp, ?_⟩
    intro i hi
    simpa using hm (e i) hi

omit [IsStrictOrderedRing K] in
theorem dictionary_positive_column_permutation_iff (B : Matrix (Fin n) (Fin n) K)
    (e : Fin n ≃ Fin n) (q : Fin n → K) :
    (∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients
      (B.submatrix (Equiv.refl _) e) q i)) ↔
      ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients B q i) := by
  rw [dictionaryCoefficients_column_permutation]
  constructor
  · intro h i
    simpa using h (e.symm i)
  · intro h i
    exact h (e i)

omit [IsStrictOrderedRing K] in
theorem dictionary_isLeavingRow_column_permutation_iff (B : Matrix (Fin n) (Fin n) K)
    (e : Fin n ≃ Fin n) (q c : Fin n → K) (l : Fin n) :
    IsLeavingRow (PerturbedDictionary.dictionaryCoefficients (B.submatrix (Equiv.refl _) e) q)
      ((B.submatrix (Equiv.refl _) e)⁻¹.mulVec c) (e.symm l) ↔
      IsLeavingRow (PerturbedDictionary.dictionaryCoefficients B q) (B⁻¹.mulVec c) l := by
  rw [dictionaryCoefficients_column_permutation, inverse_mulVec_column_permutation]
  exact isLeavingRow_permutation_iff _ _ e l

end Ordered
end GameTheory.Math
