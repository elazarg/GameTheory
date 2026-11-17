module

public import GameTheoryComplexity.Backend.BinaryCramerMachine

@[expose] public section

/-! Packed symbolic dictionaries over a common positive determinant scale.
The constant column uses the all-ones right-hand side; later columns use unit
vectors. Entering directions use the supplied system column. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

private abbrev unitTerm (v : Fin 2 → List Bool) : List Bool :=
  if (v 0).length = (v 1).length then [false, true] else [false]

private theorem unitTerm_polyTime :
    ComputableInPolyTime unitTerm (encPi encBits) encBits := by
  have hindex : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hselected : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hcondition := ComputableTidilyInPolyTime.decide_eq'
    (ComputableInPolyTime.length_bits_comp hindex).tidy
    (ComputableInPolyTime.length_bits_comp hselected).tidy
  exact .of_tidy (.ite_decide hcondition (.const [false, true]) (.const [false]))

/-- Arguments: dimension, field width, selected coordinate ruler. -/
def binaryUnitVector (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable
    (fun args : Fin 2 → List Bool =>
      if (args 0).length = (args 1).length then [false, true] else [false])
    (v 0) (v 1) ![v 2]

@[fun_prop] theorem binaryUnitVector_polyTime :
    ComputableInPolyTime binaryUnitVector (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 1) (term := unitTerm) unitTerm_polyTime
  apply ComputableInPolyTime.of_tidy
  apply htable.tidy.of_enc_eq
  intro v
  change binaryUnitVector v = binarySignedTable unitTerm (v 0) (v 1) (Fin.tail (Fin.tail v))
  unfold binaryUnitVector
  apply congrArg (binarySignedTable unitTerm (v 0) (v 1))
  funext i
  fin_cases i
  rfl

/-- Arguments: dimension and field width. -/
def binaryOnesVector (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable (fun _ : Fin 1 → List Bool => [false, true]) (v 0) (v 1) ![]

@[fun_prop] theorem binaryOnesVector_polyTime :
    ComputableInPolyTime binaryOnesVector (encPi encBits) encBits := by
  have hterm : ComputableInPolyTime (fun _ : Fin 1 → List Bool => [false, true])
      (encPi encBits) encBits := .const [false, true]
  have htable := binarySignedTable_polyTime (p := 0)
    (term := fun _ : Fin 1 → List Bool => [false, true]) hterm
  apply ComputableInPolyTime.of_tidy
  apply htable.tidy.of_enc_eq
  intro v
  change binaryOnesVector v = binarySignedTable (fun _ : Fin 1 → List Bool => [false, true])
    (v 0) (v 1) (Fin.tail (Fin.tail v))
  unfold binaryOnesVector
  apply congrArg (binarySignedTable (fun _ : Fin 1 → List Bool => [false, true]) (v 0) (v 1))
  funext i
  exact Fin.elim0 i

/-- Coefficient zero uses ones; coefficient successor uses the corresponding unit vector. -/
def binaryDictionaryVector (v : Fin 3 → List Bool) : List Bool :=
  if (v 2).isEmpty then binaryOnesVector ![v 0, v 1]
  else binaryUnitVector ![v 0, v 1, (v 2).tail]

@[fun_prop] theorem binaryDictionaryVector_polyTime :
    ComputableInPolyTime binaryDictionaryVector (encPi encBits) encBits := by
  have hdim : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hcolumn : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hcolumn
  have honesArgs : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 0, v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact hwidth
  have hunitArgs : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 0, v 1, (v 2).tail])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact hwidth
    · exact htail
  have hempty := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsIsEmpty.comp hcolumn.tidy)
  exact hempty.ite (binaryOnesVector_polyTime.comp honesArgs)
    (binaryUnitVector_polyTime.comp hunitArgs)

@[simp] theorem binaryDictionaryVector_length (v : Fin 3 → List Bool) :
    (binaryDictionaryVector v).length = (v 0).length * (v 1).length := by
  unfold binaryDictionaryVector
  cases h : v 2 with
  | nil => simp [binaryOnesVector]
  | cons b r => simp [binaryUnitVector]

/-- Arguments: dimension, field width, matrix, row, coefficient. -/
def binaryDictionaryCoefficient (v : Fin 5 → List Bool) : List Bool :=
  binaryCramerNumerator ![v 0, v 1, v 2, binaryDictionaryVector ![v 0, v 1, v 4], v 3]

@[fun_prop] theorem binaryDictionaryCoefficient_polyTime :
    ComputableInPolyTime binaryDictionaryCoefficient (encPi encBits) encBits := by
  have hvectorArgs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 0, v 1, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 4
  have hvector := binaryDictionaryVector_polyTime.comp hvectorArgs
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        ![v 0, v 1, v 2, binaryDictionaryVector ![v 0, v 1, v 4], v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact hvector
    · exact .pi_apply encBits 3
  exact binaryCramerNumerator_polyTime.comp hargs

private abbrev coefficientTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryDictionaryCoefficient ![v 1, v 2, v 3, v 4, v 0]

private theorem coefficientTerm_polyTime :
    ComputableInPolyTime coefficientTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 1, v 2, v 3, v 4, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 0
  exact binaryDictionaryCoefficient_polyTime.comp hargs

/-- Materialize the `n+1` coefficients of one row. Arguments are dimension, width, matrix, row. -/
def binaryDictionaryRow (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable
    (fun args : Fin 5 → List Bool => binaryDictionaryCoefficient ![args 1, args 2, args 3, args 4, args 0])
    (true :: v 0) (v 1) v

@[simp] theorem binaryDictionaryRow_length (v : Fin 4 → List Bool) :
    (binaryDictionaryRow v).length = ((v 0).length + 1) * (v 1).length := by
  rw [binaryDictionaryRow, binarySignedTable_length, List.length_cons]

@[fun_prop] theorem binaryDictionaryRow_polyTime :
    ComputableInPolyTime binaryDictionaryRow (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 4)
    (term := coefficientTerm) coefficientTerm_polyTime
  have hclock : ComputableInPolyTime (fun v : Fin 4 → List Bool => true :: v 0)
      (encPi encBits) encBits := .bitsCons (.const true) (.pi_apply encBits 0)
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![true :: v 0, v 1, v 0, v 1, v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryDictionaryRow v = binarySignedTable coefficientTerm (true :: v 0) (v 1)
    (Fin.tail (Fin.tail (![true :: v 0, v 1, v 0, v 1, v 2, v 3] : Fin 6 → List Bool)))
  unfold binaryDictionaryRow
  apply congrArg (binarySignedTable coefficientTerm (true :: v 0) (v 1))
  funext i
  fin_cases i <;> rfl

private abbrev rowTerm (v : Fin 4 → List Bool) : List Bool :=
  binaryDictionaryRow ![v 1, v 2, v 3, v 0]

private theorem rowTerm_polyTime :
    ComputableInPolyTime rowTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 1, v 2, v 3, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 0
  exact binaryDictionaryRow_polyTime.comp hargs

/-- Row-major symbolic numerator table. Arguments are dimension, field width, matrix. -/
def binaryDictionaryCoefficients (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable
    (fun args : Fin 4 → List Bool => binaryDictionaryRow ![args 1, args 2, args 3, args 0])
    (v 0)
    (List.replicate (((v 0).length + 1) * (v 1).length) true) v

@[simp] theorem binaryDictionaryCoefficients_length (v : Fin 3 → List Bool) :
    (binaryDictionaryCoefficients v).length =
      (v 0).length * (((v 0).length + 1) * (v 1).length) := by
  rw [binaryDictionaryCoefficients, binarySignedTable_length, List.length_replicate]

@[fun_prop] theorem binaryDictionaryCoefficients_polyTime :
    ComputableInPolyTime binaryDictionaryCoefficients (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 3) (term := rowTerm) rowTerm_polyTime
  have hdim : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hclock : ComputableInPolyTime (fun v : Fin 3 → List Bool => true :: v 0)
      (encPi encBits) encBits := .bitsCons (.const true) hdim
  have hruler := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.length_bits_comp hclock)
      (ComputableInPolyTime.length_bits_comp hwidth))
  have hargs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        ![v 0, List.replicate (((v 0).length + 1) * (v 1).length) true, v 0, v 1, v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact hruler
    · exact hdim
    · exact hwidth
    · exact .pi_apply encBits 2
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryDictionaryCoefficients v = binarySignedTable rowTerm (v 0)
    (List.replicate (((v 0).length + 1) * (v 1).length) true)
    (Fin.tail (Fin.tail (![v 0, List.replicate (((v 0).length + 1) * (v 1).length) true,
      v 0, v 1, v 2] : Fin 5 → List Bool)))
  unfold binaryDictionaryCoefficients
  apply congrArg (binarySignedTable rowTerm (v 0)
    (List.replicate (((v 0).length + 1) * (v 1).length) true))
  funext i
  fin_cases i <;> rfl

private abbrev directionTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryCramerNumerator ![v 1, v 2, v 3, v 4, v 0]

private theorem directionTerm_polyTime :
    ComputableInPolyTime directionTerm (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => ![v 1, v 2, v 3, v 4, v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
    · exact .pi_apply encBits 0
  exact binaryCramerNumerator_polyTime.comp hargs

/-- Arguments: dimension, field width, matrix, entering system column. -/
def binaryDictionaryDirection (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable
    (fun args : Fin 5 → List Bool => binaryCramerNumerator ![args 1, args 2, args 3, args 4, args 0])
    (v 0) (v 1) v

@[simp] theorem binaryDictionaryDirection_length (v : Fin 4 → List Bool) :
    (binaryDictionaryDirection v).length = (v 0).length * (v 1).length :=
  binarySignedTable_length _ _ _ _

@[fun_prop] theorem binaryDictionaryDirection_polyTime :
    ComputableInPolyTime binaryDictionaryDirection (encPi encBits) encBits := by
  have htable := binarySignedTable_polyTime (p := 4)
    (term := directionTerm) directionTerm_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![v 0, v 1, v 0, v 1, v 2, v 3])
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
  have htable' := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply htable'.tidy.of_enc_eq
  intro v
  change binaryDictionaryDirection v = binarySignedTable directionTerm (v 0) (v 1)
    (Fin.tail (Fin.tail (![v 0, v 1, v 0, v 1, v 2, v 3] : Fin 6 → List Bool)))
  unfold binaryDictionaryDirection
  apply congrArg (binarySignedTable directionTerm (v 0) (v 1))
  funext i
  fin_cases i <;> rfl

/-- Exact extraction of a stored symbolic coefficient. -/
theorem binaryDictionaryRow_field (v : Fin 4 → List Bool) (j : ℕ)
    (hj : j < (v 0).length + 1) :
    ((binaryDictionaryRow v).drop (j * (v 1).length)).take (v 1).length =
      binaryDictionaryCoefficient ![v 0, v 1, v 2, v 3,
        (true :: v 0).drop ((v 0).length + 1 - j)] := by
  let packed : Fin 5 → List Bool :=
    Fin.cons ((true :: v 0).drop ((v 0).length + 1 - j)) v
  have h := binarySignedTable_field (p := 4) coefficientTerm (true :: v 0) (v 1) v j hj
  change _ = binarySignedFixed (v 1)
    (binaryDictionaryCoefficient ![packed 1, packed 2, packed 3, packed 4, packed 0]) at h
  rw [binarySignedFixed_eq_of_length] at h
  · have hfield :
        binaryDictionaryCoefficient ![packed 1, packed 2, packed 3, packed 4, packed 0] =
        binaryDictionaryCoefficient ![v 0, v 1, v 2, v 3,
          (true :: v 0).drop ((v 0).length + 1 - j)] := by
      apply congrArg binaryDictionaryCoefficient
      funext k
      fin_cases k <;> rfl
    simpa only [binaryDictionaryRow] using h.trans hfield
  · exact binaryCramerNumerator_length _

/-- Exact extraction of a packed symbolic row. -/
theorem binaryDictionaryCoefficients_row (v : Fin 3 → List Bool) (i : ℕ)
    (hi : i < (v 0).length) :
    ((binaryDictionaryCoefficients v).drop (i * (((v 0).length + 1) * (v 1).length))).take
      (((v 0).length + 1) * (v 1).length) =
      binaryDictionaryRow ![v 0, v 1, v 2, (v 0).drop ((v 0).length - i)] := by
  let packed : Fin 4 → List Bool := Fin.cons ((v 0).drop ((v 0).length - i)) v
  have h := binarySignedTable_field (p := 3) rowTerm (v 0)
    (List.replicate (((v 0).length + 1) * (v 1).length) true) v i hi
  rw [List.length_replicate] at h
  change _ = binarySignedFixed (List.replicate (((v 0).length + 1) * (v 1).length) true)
    (binaryDictionaryRow ![packed 1, packed 2, packed 3, packed 0]) at h
  rw [binarySignedFixed_eq_of_length] at h
  · have hrow : binaryDictionaryRow ![packed 1, packed 2, packed 3, packed 0] =
        binaryDictionaryRow ![v 0, v 1, v 2, (v 0).drop ((v 0).length - i)] := by
      apply congrArg binaryDictionaryRow
      funext k
      fin_cases k <;> rfl
    simpa only [binaryDictionaryCoefficients] using h.trans hrow
  · rw [binaryDictionaryRow_length, List.length_replicate]
    rfl

/-- Exact extraction of the row-major symbolic coefficient table. -/
theorem binaryDictionaryCoefficients_field (v : Fin 3 → List Bool) (i j : ℕ)
    (hi : i < (v 0).length) (hj : j < (v 0).length + 1) :
    ((binaryDictionaryCoefficients v).drop
      ((i * ((v 0).length + 1) + j) * (v 1).length)).take (v 1).length =
      binaryDictionaryCoefficient ![v 0, v 1, v 2, (v 0).drop ((v 0).length - i),
        (true :: v 0).drop ((v 0).length + 1 - j)] := by
  have h := congrArg (fun x : List Bool => (x.drop (j * (v 1).length)).take (v 1).length)
    (binaryDictionaryCoefficients_row v i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : (v 1).length ≤ ((v 0).length + 1) * (v 1).length - j * (v 1).length := by
    have hb := Nat.mul_le_mul_right (v 1).length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (binaryDictionaryRow_field
    ![v 0, v 1, v 2, (v 0).drop ((v 0).length - i)] j hj)

/-- Exact extraction of an entering-direction numerator. -/
theorem binaryDictionaryDirection_field (v : Fin 4 → List Bool) (i : ℕ)
    (hi : i < (v 0).length) :
    ((binaryDictionaryDirection v).drop (i * (v 1).length)).take (v 1).length =
      binaryCramerNumerator ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] := by
  let packed : Fin 5 → List Bool := Fin.cons ((v 0).drop ((v 0).length - i)) v
  have h := binarySignedTable_field (p := 4) directionTerm (v 0) (v 1) v i hi
  change _ = binarySignedFixed (v 1)
    (binaryCramerNumerator ![packed 1, packed 2, packed 3, packed 4, packed 0]) at h
  rw [binarySignedFixed_eq_of_length] at h
  · have hfield : binaryCramerNumerator ![packed 1, packed 2, packed 3, packed 4, packed 0] =
        binaryCramerNumerator ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] := by
      apply congrArg binaryCramerNumerator
      funext k
      fin_cases k <;> rfl
    simpa only [binaryDictionaryDirection] using h.trans hfield
  · exact binaryCramerNumerator_length _

end GameTheory.Complexity.Backend
