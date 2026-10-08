import GameTheory.Math.FiniteLexicographic
import GameTheory.Math.PerturbedDictionary
import GameTheory.Math.DictionaryPivot
import Mathlib.Data.Finset.Max

/-! Exact symbolic ratio tests for feasible linear dictionaries.
Independent perturbation coefficients break ordinary ratio ties. The selected
column replacement preserves strict lexicographic feasibility, including rows
whose original constant coordinate becomes zero. -/
namespace GameTheory.Math
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n k : ℕ}

/-- A leaving row has positive direction and the least symbolic ratio. -/
def IsLeavingRow (C : Fin n → Fin k → K) (d : Fin n → K) (l : Fin n) : Prop :=
  0 < d l ∧ ∀ i, 0 < d i →
    toLex (fun j => C l j / d l) ≤ toLex (fun j => C i j / d i)

omit [IsStrictOrderedRing K] in
/-- Distinct eligible ratios make the finite minimum unique. -/
theorem exists_unique_leavingRow (C : Fin n → Fin k → K) (d : Fin n → K)
    (hexit : ∃ i, 0 < d i)
    (hdistinct : ∀ i j, 0 < d i → 0 < d j → i ≠ j →
      (fun a => C i a / d i) ≠ (fun a => C j a / d j)) :
    ∃! l, IsLeavingRow C d l := by
  classical
  let s := Finset.univ.filter (fun i => 0 < d i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hexit
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨l, hl, hmin⟩ := s.exists_min_image (fun i => toLex (fun a => C i a / d i)) hs
  have hp : 0 < d l := (Finset.mem_filter.mp hl).2
  have hleave : IsLeavingRow C d l :=
    ⟨hp, fun i hi => hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)⟩
  refine ⟨l, hleave, ?_⟩
  intro j hj
  by_contra hne
  have he := le_antisymm (hj.2 l hp) (hleave.2 j hj.1)
  exact hdistinct j l hj.1 hp hne (toLex_inj.mp he)

omit [IsStrictOrderedRing K] in
/-- The unique ratio minimum is strictly below every other eligible ratio. -/
theorem IsLeavingRow.ratio_lt {C : Fin n → Fin k → K} {d : Fin n → K} {l : Fin n}
    (hl : IsLeavingRow C d l)
    (hdistinct : ∀ i j, 0 < d i → 0 < d j → i ≠ j →
      (fun a => C i a / d i) ≠ (fun a => C j a / d j))
    {i : Fin n} (hi : 0 < d i) (hne : i ≠ l) :
    toLex (fun a => C l a / d l) < toLex (fun a => C i a / d i) := by
  apply lt_of_le_of_ne (hl.2 i hi)
  intro he
  exact hdistinct l i hl.1 hi (Ne.symm hne) (toLex_inj.mp he)

/-- Pivot each symbolic coefficient using the same rational direction. -/
def pivotCoefficients (C : Fin n → Fin k → K) (d : Fin n → K) (l : Fin n)
    (i : Fin n) (a : Fin k) : K := pivotVector d l (fun j => C j a) i

/-- Symbolic minimum-ratio pivoting preserves strict feasibility. -/
theorem pivotCoefficients_positive (C : Fin n → Fin k → K) (d : Fin n → K) (l : Fin n)
    (hC : ∀ i, 0 < toLex (C i)) (hl : IsLeavingRow C d l)
    (hdistinct : ∀ i j, 0 < d i → 0 < d j → i ≠ j →
      (fun a => C i a / d i) ≠ (fun a => C j a / d j)) :
    ∀ i, 0 < toLex (pivotCoefficients C d l i) := by
  have hratio : 0 < toLex (fun a => C l a / d l) := by
    have hh := (FiniteLexicographic.div_lt_div_iff
      (x := fun _ => 0) (y := C l) hl.1).mpr (hC l)
    have hz : toLex (fun _ : Fin k => (0 : K)) = (0 : Lex (Fin k → K)) := rfl
    simpa only [zero_div, hz] using hh
  intro i
  by_cases hil : i = l
  · subst i
    have heSelf : pivotCoefficients C d l l = fun a => C l a / d l := by
      funext a
      exact pivotVector_apply_self _ _ _
    rw [heSelf]
    exact hratio
  · have hePivot : pivotCoefficients C d l i =
        fun a => C i a - d i * (C l a / d l) := by
      funext a
      exact pivotVector_apply_of_ne _ _ _ hil
    rw [hePivot]
    by_cases hi : 0 < d i
    · have hh := (FiniteLexicographic.mul_lt_mul_iff hi).mpr
        (hl.ratio_lt hdistinct hi hil)
      have he : toLex (fun a => d i * (C i a / d i)) = toLex (C i) := by
        congr 1
        funext a
        field_simp
      rw [he] at hh
      exact sub_pos.mpr hh
    · have hn : 0 ≤ -d i := neg_nonneg.mpr (le_of_not_gt hi)
      have hh := FiniteLexicographic.mul_nonneg hn hratio.le
      have hp := add_pos_of_pos_of_nonneg (hC i) hh
      have heAdd : toLex (C i) + toLex (fun a => -d i * (C l a / d l)) =
          toLex (fun a => C i a - d i * (C l a / d l)) := by
        funext a
        change C i a + (-d i) * (C l a / d l) = C i a - d i * (C l a / d l)
        ring
      rw [heAdd] at hp
      exact hp

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- An actual basis-column replacement pivots every symbolic coefficient. -/
theorem dictionaryCoefficients_updated (B : Matrix (Fin n) (Fin n) K) (q c : Fin n → K)
    (l : Fin n) (hB : B.det ≠ 0) (hd : B⁻¹.mulVec c l ≠ 0) :
    PerturbedDictionary.dictionaryCoefficients (B.updateCol l c) q =
      pivotCoefficients (PerturbedDictionary.dictionaryCoefficients B q) (B⁻¹.mulVec c) l := by
  funext i a
  refine Fin.cases ?_ (fun j => ?_) a
  · exact congrFun (updated_inverse_mulVec B c l q hB hd) i
  · have hh := updated_inverse_mulVec B c l (Pi.single j 1) hB hd
    simp only [Matrix.mulVec_single_one] at hh
    exact congrFun hh i

omit [IsStrictOrderedRing K] in
/-- Inverse-basis perturbations supply the distinct eligible ratios automatically. -/
theorem exists_unique_dictionary_leavingRow (B : Matrix (Fin n) (Fin n) K)
    (q c : Fin n → K) (hB : B.det ≠ 0) (hexit : ∃ i, 0 < B⁻¹.mulVec c i) :
    ∃! l, IsLeavingRow (PerturbedDictionary.dictionaryCoefficients B q) (B⁻¹.mulVec c) l := by
  apply exists_unique_leavingRow _ _ hexit
  intro i j hi hj hij
  exact PerturbedDictionary.divided_coefficients_ne B hB q _ hij hi.ne'

/-- A feasible basis stays feasible after the unique symbolic minimum-ratio pivot. -/
theorem dictionaryCoefficients_updated_positive (B : Matrix (Fin n) (Fin n) K)
    (q c : Fin n → K) (l : Fin n) (hB : B.det ≠ 0)
    (hC : ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients B q i))
    (hl : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients B q) (B⁻¹.mulVec c) l) :
    ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients (B.updateCol l c) q i) := by
  rw [dictionaryCoefficients_updated B q c l hB hl.1.ne']
  apply pivotCoefficients_positive _ _ _ hC hl
  intro i j hi hj hij
  exact PerturbedDictionary.divided_coefficients_ne B hB q _ hij hi.ne'

/-- The same ratio rule chooses the old column when reversing a feasible pivot. -/
theorem reverse_isLeavingRow (C : Fin n → Fin k → K) (d : Fin n → K) (l : Fin n)
    (hC : ∀ i, 0 < toLex (C i)) (hl : IsLeavingRow C d l) :
    IsLeavingRow (pivotCoefficients C d l) (pivotVector d l (Pi.single l 1)) l := by
  let e := pivotVector d l (Pi.single l 1)
  have hdl : d l ≠ 0 := hl.1.ne'
  have he : e l = 1 / d l := reverse_pivot_entry d l
  have hp : 0 < e l := by rw [he]; exact one_div_pos.mpr hl.1
  have hratio : (fun a => pivotCoefficients C d l l a / e l) = C l := by
    funext a
    simp only [pivotCoefficients, pivotVector_apply_self, he]
    field_simp [hdl]
  refine ⟨hp, ?_⟩
  intro i hi
  by_cases hil : i = l
  · subst i; exact le_rfl
  · have hei : e i = -d i / d l := by
      simp only [e, pivotVector_apply_of_ne _ _ _ hil, Pi.single_eq_of_ne hil,
        Pi.single_eq_same, zero_sub]
      ring
    have hri : (fun a => pivotCoefficients C d l i a / e i) =
        fun a => C l a + C i a / e i := by
      funext a
      simp only [pivotCoefficients, pivotVector_apply_of_ne _ _ _ hil]
      rw [hei]
      have hd : d i ≠ 0 := by
        intro hz
        have hz' : e i = 0 := by rw [hei, hz]; simp
        exact hi.ne' hz'
      field_simp [hdl, hd]
      ring
    have hpos : 0 < toLex (fun a => C i a / e i) := by
      have hh := (FiniteLexicographic.div_lt_div_iff
        (x := fun _ => 0) (y := C i) hi).mpr (hC i)
      have hz : toLex (fun _ : Fin k => (0 : K)) = (0 : Lex (Fin k → K)) := rfl
      simpa only [zero_div, hz] using hh
    have hh := lt_add_of_pos_right (toLex (C l)) hpos
    have heAdd : toLex (C l) + toLex (fun a => C i a / e i) =
        toLex (fun a => C l a + C i a / e i) := rfl
    rw [heAdd] at hh
    change toLex (fun a => pivotCoefficients C d l l a / e l) ≤
      toLex (fun a => pivotCoefficients C d l i a / e i)
    rw [hratio, hri]
    exact hh.le

/-- The old column is the selected reverse pivot in the updated dictionary. -/
theorem dictionary_reverse_isLeavingRow (B : Matrix (Fin n) (Fin n) K)
    (q c : Fin n → K) (l : Fin n) (hB : B.det ≠ 0)
    (hC : ∀ i, 0 < toLex (PerturbedDictionary.dictionaryCoefficients B q i))
    (hl : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients B q) (B⁻¹.mulVec c) l) :
    IsLeavingRow (PerturbedDictionary.dictionaryCoefficients (B.updateCol l c) q)
      ((B.updateCol l c)⁻¹.mulVec (fun i => B i l)) l := by
  rw [dictionaryCoefficients_updated B q c l hB hl.1.ne',
    updated_inverse_oldColumn B c l hB hl.1.ne']
  exact reverse_isLeavingRow _ _ _ hC hl

end GameTheory.Math
