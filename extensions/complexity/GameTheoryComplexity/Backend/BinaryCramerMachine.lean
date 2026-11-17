module

public import GameTheoryComplexity.Backend.BinaryBirdDeterminantMachine

@[expose] public section

/-! Packed column replacement and signed Cramer numerator machines.
All scalar and matrix buffers retain their supplied field width. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Sign of an arbitrary signed word, including padded positive or negative zero. -/
def binarySignedSign (x : List Bool) : List Bool :=
  select (binarySignedLTFlag x []) [true, true]
    (select (binarySignedLTFlag [] x) [false, true] [false])

theorem binarySignedSign_value (x : List Bool) :
    binarySignedValue (binarySignedSign x) = Int.sign (binarySignedValue x) := by
  rw [binarySignedSign, binarySignedLTFlag_value, binarySignedLTFlag_value]
  have hz : binarySignedValue [] = 0 := rfl
  rw [hz]
  simp only [select, List.headD_cons, decide_eq_true_eq]
  rcases lt_trichotomy (binarySignedValue x) 0 with h | h | h
  · rw [ite_eq_left h, Int.sign_eq_neg_one_of_neg h]
    rfl
  · simp only [h, lt_self_iff_false, ↓reduceIte, Int.sign_zero]
    rfl
  · rw [ite_eq_right (not_lt_of_ge h.le), ite_eq_left h, Int.sign_eq_one_of_pos h]
    rfl

@[fun_prop] theorem binarySignedSign_polyTime :
    ComputableInPolyTime binarySignedSign encBits encBits := by
  have hid : ComputableInPolyTime (fun x : List Bool => x) encBits encBits := .id'
  have hnegative := binarySignedLTFlag_polyTime hid (ComputableInPolyTime.const [])
  have hpositive := binarySignedLTFlag_polyTime (ComputableInPolyTime.const []) hid
  have hnonnegative := select_polyTime.comp
    (hpositive.prod ((ComputableInPolyTime.const [false, true]).prod
      (ComputableInPolyTime.const [false])))
  exact select_polyTime.comp
    (hnegative.prod ((ComputableInPolyTime.const [true, true]).prod hnonnegative))

/-- Arguments: row, column, dimension, field width, matrix, replacement vector, replaced column. -/
def binaryCramerEntry (v : Fin 7 → List Bool) : List Bool :=
  if (v 1).length = (v 6).length then
    binarySignedRowField ![v 0, v 3, v 5]
  else binaryBirdField ![v 0, v 1, v 2, v 3, v 4]

@[fun_prop] theorem binaryCramerEntry_polyTime :
    ComputableInPolyTime binaryCramerEntry (encPi encBits) encBits := by
  have hrowArgs : ComputableInPolyTime
      (fun v : Fin 7 → List Bool => ![v 0, v 3, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 5
  have hfieldArgs : ComputableInPolyTime
      (fun v : Fin 7 → List Bool => ![v 0, v 1, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
  have hcol : ComputableInPolyTime (fun v : Fin 7 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hreplaced : ComputableInPolyTime (fun v : Fin 7 → List Bool => v 6)
      (encPi encBits) encBits := .pi_apply encBits 6
  have hcondition := ComputableTidilyInPolyTime.decide_eq'
    (ComputableInPolyTime.length_bits_comp hcol).tidy
    (ComputableInPolyTime.length_bits_comp hreplaced).tidy
  exact .of_tidy (.ite_decide hcondition (binarySignedRowField_polyTime.comp hrowArgs).tidy
    (binaryBirdField_polyTime.comp hfieldArgs).tidy)

private def cramerRowTerm (v : Fin 7 → List Bool) : List Bool :=
  binaryCramerEntry ![v 6, v 0, v 1, v 2, v 3, v 4, v 5]

private theorem cramerRowTerm_polyTime :
    ComputableInPolyTime cramerRowTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 7 → List Bool => ![v 6, v 0, v 1, v 2, v 3, v 4, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 6
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
  exact binaryCramerEntry_polyTime.comp hargs

/-- Arguments: dimension, field width, matrix, replacement vector, replaced column, row. -/
def binaryCramerRow (v : Fin 6 → List Bool) : List Bool :=
  binarySignedTable cramerRowTerm (v 0) (v 1) v

@[simp] theorem binaryCramerRow_length (v : Fin 6 → List Bool) :
    (binaryCramerRow v).length = (v 0).length * (v 1).length :=
  binarySignedTable_length _ _ _ _

@[fun_prop] theorem binaryCramerRow_polyTime :
    ComputableInPolyTime binaryCramerRow (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 6) (term := cramerRowTerm) cramerRowTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 0, v 1, v 0, v 1, v 2, v 3, v 4, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryCramerRow v = binarySignedTable cramerRowTerm (v 0) (v 1)
    (Fin.tail (Fin.tail (![v 0, v 1, v 0, v 1, v 2, v 3, v 4, v 5] : Fin 8 → List Bool)))
  unfold binaryCramerRow
  apply congrArg (binarySignedTable cramerRowTerm (v 0) (v 1))
  funext i
  fin_cases i <;> rfl

private def cramerMatrixTerm (v : Fin 6 → List Bool) : List Bool :=
  binaryCramerRow ![v 1, v 2, v 3, v 4, v 5, v 0]

private theorem cramerMatrixTerm_polyTime :
    ComputableInPolyTime cramerMatrixTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 1, v 2, v 3, v 4, v 5, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 5
    · exact .pi_apply encBits 0
  exact binaryCramerRow_polyTime.comp hargs

/-- Arguments: dimension, field width, matrix, replacement vector, replaced column. -/
def binaryCramerMatrix (v : Fin 5 → List Bool) : List Bool :=
  binarySignedTable cramerMatrixTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true) v

@[simp] theorem binaryCramerMatrix_length (v : Fin 5 → List Bool) :
    (binaryCramerMatrix v).length = (v 0).length * ((v 0).length * (v 1).length) := by
  rw [binaryCramerMatrix, binarySignedTable_length, List.length_replicate]

@[fun_prop] theorem binaryCramerMatrix_polyTime :
    ComputableInPolyTime binaryCramerMatrix (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 5) (term := cramerMatrixTerm) cramerMatrixTerm_polyTime
  have hdim : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hruler := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.length_bits_comp hdim)
      (ComputableInPolyTime.length_bits_comp hwidth))
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        ![v 0, List.replicate ((v 0).length * (v 1).length) true, v 0, v 1, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact hruler
    · exact hdim
    · exact hwidth
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryCramerMatrix v = binarySignedTable cramerMatrixTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true)
    (Fin.tail (Fin.tail (![v 0, List.replicate ((v 0).length * (v 1).length) true,
      v 0, v 1, v 2, v 3, v 4] : Fin 7 → List Bool)))
  unfold binaryCramerMatrix
  apply congrArg (binarySignedTable cramerMatrixTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true))
  funext i
  fin_cases i <;> rfl

/-- The determinant of the supplied matrix with one column replaced. -/
def binaryCramerDeterminant (v : Fin 5 → List Bool) : List Bool :=
  binaryBirdDeterminant ![v 0, v 1, binaryCramerMatrix v]

@[fun_prop] theorem binaryCramerDeterminant_polyTime :
    ComputableInPolyTime binaryCramerDeterminant (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 0, v 1, binaryCramerMatrix v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact binaryCramerMatrix_polyTime
  exact binaryBirdDeterminant_polyTime.comp hargs

/-- Sign-adjusted Cramer numerator; the determinant sign is computed by the same machine. -/
def binaryCramerNumerator (v : Fin 5 → List Bool) : List Bool :=
  binarySignedFixedMul (v 1)
    (binarySignedSign (binaryBirdDeterminant ![v 0, v 1, v 2]))
    (binaryCramerDeterminant v)

@[fun_prop] theorem binaryCramerNumerator_polyTime :
    ComputableInPolyTime binaryCramerNumerator (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 0, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
  have hdet := binaryBirdDeterminant_polyTime.comp hargs
  have hsign := binarySignedSign_polyTime.comp hdet
  have hwidth : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  exact binarySignedFixedMul_polyTime hwidth hsign binaryCramerDeterminant_polyTime

@[simp] theorem binaryCramerNumerator_length (v : Fin 5 → List Bool) :
    (binaryCramerNumerator v).length = (v 1).length := binarySignedFixedMul_length _ _ _

/-- Extracting a stored row recovers its byte representation exactly. -/
theorem binaryCramerMatrix_row (v : Fin 5 → List Bool) (i : ℕ) (hi : i < (v 0).length) :
    ((binaryCramerMatrix v).drop (i * ((v 0).length * (v 1).length))).take
      ((v 0).length * (v 1).length) =
      binaryCramerRow ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - i)] := by
  have h := binarySignedTable_field cramerMatrixTerm (v 0)
    (List.replicate ((v 0).length * (v 1).length) true) v i hi
  rw [List.length_replicate] at h
  change _ = binarySignedFixed (List.replicate ((v 0).length * (v 1).length) true)
    (binaryCramerRow _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · let packed : Fin 6 → List Bool := Fin.cons ((v 0).drop ((v 0).length - i)) v
    have hrow : binaryCramerRow ![packed 1, packed 2, packed 3, packed 4, packed 5, packed 0] =
        binaryCramerRow ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - i)] := by
      apply congrArg binaryCramerRow
      funext j
      fin_cases j <;> rfl
    simpa only [binaryCramerMatrix] using h.trans hrow
  · rw [binaryCramerRow_length, List.length_replicate]
    rfl

/-- A column field in a materialized Cramer row is normalized once. -/
theorem binaryCramerRow_field (v : Fin 6 → List Bool) (j : ℕ) (hj : j < (v 0).length) :
    ((binaryCramerRow v).drop (j * (v 1).length)).take (v 1).length =
      binarySignedFixed (v 1) (binaryCramerEntry
        ![v 5, (v 0).drop ((v 0).length - j), v 0, v 1, v 2, v 3, v 4]) := by
  exact binarySignedTable_field cramerRowTerm (v 0) (v 1) v j hj

/-- Exact byte extraction from the row-major replacement matrix. -/
theorem binaryCramerMatrix_field (v : Fin 5 → List Bool) (i j : ℕ)
    (hi : i < (v 0).length) (hj : j < (v 0).length) :
    ((binaryCramerMatrix v).drop ((i * (v 0).length + j) * (v 1).length)).take (v 1).length =
      binarySignedFixed (v 1) (binaryCramerEntry ![(v 0).drop ((v 0).length - i),
        (v 0).drop ((v 0).length - j), v 0, v 1, v 2, v 3, v 4]) := by
  have h := congrArg (fun x : List Bool => (x.drop (j * (v 1).length)).take (v 1).length)
    (binaryCramerMatrix_row v i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : (v 1).length ≤ (v 0).length * (v 1).length - j * (v 1).length := by
    have hb := Nat.mul_le_mul_right (v 1).length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (binaryCramerRow_field
    ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - i)] j hj)

end GameTheory.Complexity.Backend
