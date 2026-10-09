import GameTheoryComplexity.Backend.BinaryCramerMachine

/-! Packed symbolic dictionaries over a common positive determinant scale.
The constant column uses the all-ones right-hand side; later columns use unit
vectors. Entering directions use the supplied system column. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem reindex {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    (hf : Cobham f) (idx : Fin m → Fin n) :
    Cobham fun v : Fin n → List Bool => f (fun i => v (idx i)) :=
  Cobham.comp hf fun i => Cobham.proj (idx i)

private def unitTerm (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 0) (v 1)) [false, true] [false]

private theorem unitTerm_cobham : Cobham unitTerm :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) (.proj 1))
    (Cobham.const [false, true]) (Cobham.const [false])

/-- Arguments: dimension, field width, selected coordinate ruler. -/
def binaryUnitVector (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable unitTerm (v 0) (v 1) ![v 2]

theorem binaryUnitVector_cobham : Cobham binaryUnitVector :=
  (binarySignedTable_cobham unitTerm_cobham).of_eq fun v => by
    congr 1; ext i; fin_cases i; rfl

/-- Arguments: dimension and field width. -/
def binaryOnesVector (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable (fun _ : Fin 1 → List Bool => [false, true]) (v 0) (v 1) ![]

theorem binaryOnesVector_cobham : Cobham binaryOnesVector :=
  (binarySignedTable_cobham (Cobham.const [false, true])).of_eq fun v => by
    congr 1; ext i; exact Fin.elim0 i

/-- Coefficient zero uses ones; coefficient successor uses the corresponding unit vector. -/
def binaryDictionaryVector (v : Fin 3 → List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (v 2))
    (binaryUnitVector ![v 0, v 1, (v 2).tail]) (binaryOnesVector ![v 0, v 1])

theorem binaryDictionaryVector_cobham : Cobham binaryDictionaryVector :=
  Cobham.iteFn (Cobham.nonemptyFn (.proj 2))
    (Cobham.comp₃ binaryUnitVector_cobham (.proj 0) (.proj 1) (Cobham.tailFn (.proj 2)))
    (Cobham.comp₂ binaryOnesVector_cobham (.proj 0) (.proj 1))

@[simp] theorem binaryDictionaryVector_length (v : Fin 3 → List Bool) :
    (binaryDictionaryVector v).length = (v 0).length * (v 1).length := by
  unfold binaryDictionaryVector
  cases h : v 2 with
  | nil => simp [binaryOnesVector]
  | cons b r => simp [binaryUnitVector]

/-- Arguments: dimension, field width, matrix, row, coefficient. -/
def binaryDictionaryCoefficient (v : Fin 5 → List Bool) : List Bool :=
  binaryCramerNumerator ![v 0, v 1, v 2, binaryDictionaryVector ![v 0, v 1, v 4], v 3]

theorem binaryDictionaryCoefficient_cobham : Cobham binaryDictionaryCoefficient := by
  have hv : Cobham fun v : Fin 5 → List Bool => binaryDictionaryVector ![v 0, v 1, v 4] :=
    Cobham.comp₃ binaryDictionaryVector_cobham (.proj 0) (.proj 1) (.proj 4)
  apply Cobham.comp binaryCramerNumerator_cobham
  intro i
  fin_cases i
  · exact .proj 0
  · exact .proj 1
  · exact .proj 2
  · exact hv
  · exact .proj 3

private def coefficientTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryDictionaryCoefficient ![v 1, v 2, v 3, v 4, v 0]

private theorem coefficientTerm_cobham : Cobham coefficientTerm :=
  (reindex binaryDictionaryCoefficient_cobham (![1, 2, 3, 4, 0] : Fin 5 → Fin 5)).of_eq
    fun v => by congr 1; ext i; fin_cases i <;> rfl

/-- Materialize the `n+1` coefficients of one row. Arguments are dimension, width, matrix, row. -/
def binaryDictionaryRow (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable coefficientTerm (true :: v 0) (v 1) v

@[simp] theorem binaryDictionaryRow_length (v : Fin 4 → List Bool) :
    (binaryDictionaryRow v).length = ((v 0).length + 1) * (v 1).length := by
  rw [binaryDictionaryRow, binarySignedTable_length, List.length_cons]

theorem binaryDictionaryRow_cobham : Cobham binaryDictionaryRow := by
  have hg : ∀ i : Fin 6, Cobham fun v : Fin 4 → List Bool =>
      (Fin.cons (true :: v 0) (Fin.cons (v 1) v) : Fin 6 → List Bool) i := by
    intro i
    fin_cases i
    · exact Cobham.comp (.bit true) fun _ : Fin 1 => .proj 0
    all_goals exact .proj _
  exact (Cobham.comp (binarySignedTable_cobham coefficientTerm_cobham) hg).of_eq fun _ => rfl

private def rowTerm (v : Fin 4 → List Bool) : List Bool :=
  binaryDictionaryRow ![v 1, v 2, v 3, v 0]

private theorem rowTerm_cobham : Cobham rowTerm :=
  (reindex binaryDictionaryRow_cobham (![1, 2, 3, 0] : Fin 4 → Fin 4)).of_eq
    fun v => by congr 1; ext i; fin_cases i <;> rfl

/-- Row-major symbolic numerator table. Arguments are dimension, field width, matrix. -/
def binaryDictionaryCoefficients (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable rowTerm (v 0) (smash (true :: v 0) (v 1)) v

@[simp] theorem binaryDictionaryCoefficients_length (v : Fin 3 → List Bool) :
    (binaryDictionaryCoefficients v).length =
      (v 0).length * (((v 0).length + 1) * (v 1).length) := by
  rw [binaryDictionaryCoefficients, binarySignedTable_length, smash_length, List.length_cons]

theorem binaryDictionaryCoefficients_cobham : Cobham binaryDictionaryCoefficients := by
  have hw : Cobham fun v : Fin 3 → List Bool => smash (true :: v 0) (v 1) :=
    Cobham.comp₂ Cobham.smash (Cobham.comp (.bit true) fun _ : Fin 1 => .proj 0) (.proj 1)
  have hg : ∀ i : Fin 5, Cobham fun v : Fin 3 → List Bool =>
      (Fin.cons (v 0) (Fin.cons (smash (true :: v 0) (v 1)) v) : Fin 5 → List Bool) i := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact hw
    all_goals exact .proj _
  exact (Cobham.comp (binarySignedTable_cobham rowTerm_cobham) hg).of_eq fun _ => rfl

private def directionTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryCramerNumerator ![v 1, v 2, v 3, v 4, v 0]

private theorem directionTerm_cobham : Cobham directionTerm :=
  (reindex binaryCramerNumerator_cobham (![1, 2, 3, 4, 0] : Fin 5 → Fin 5)).of_eq
    fun v => by congr 1; ext i; fin_cases i <;> rfl

/-- Arguments: dimension, field width, matrix, entering system column. -/
def binaryDictionaryDirection (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable directionTerm (v 0) (v 1) v

@[simp] theorem binaryDictionaryDirection_length (v : Fin 4 → List Bool) :
    (binaryDictionaryDirection v).length = (v 0).length * (v 1).length :=
  binarySignedTable_length _ _ _ _

theorem binaryDictionaryDirection_cobham : Cobham binaryDictionaryDirection :=
  (reindex (binarySignedTable_cobham directionTerm_cobham)
    (![0, 1, 0, 1, 2, 3] : Fin 6 → Fin 4)).of_eq fun v => by
      change binarySignedTable directionTerm (v 0) (v 1) _ = _
      congr 1; ext i; fin_cases i <;> rfl

theorem binaryDictionaryCoefficients_mem_FPn : FPn binaryDictionaryCoefficients :=
  cobham_iff_FPn.mp binaryDictionaryCoefficients_cobham

theorem binaryDictionaryDirection_mem_FPn : FPn binaryDictionaryDirection :=
  cobham_iff_FPn.mp binaryDictionaryDirection_cobham

/-- Exact extraction of a stored symbolic coefficient. -/
theorem binaryDictionaryRow_field (v : Fin 4 → List Bool) (j : ℕ)
    (hj : j < (v 0).length + 1) :
    ((binaryDictionaryRow v).drop (j * (v 1).length)).take (v 1).length =
      binaryDictionaryCoefficient ![v 0, v 1, v 2, v 3,
        (true :: v 0).drop ((v 0).length + 1 - j)] := by
  have h := binarySignedTable_field coefficientTerm (true :: v 0) (v 1) v j hj
  change _ = binarySignedFixed (v 1) (binaryDictionaryCoefficient _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · exact binaryCramerNumerator_length _

/-- Exact extraction of a packed symbolic row. -/
theorem binaryDictionaryCoefficients_row (v : Fin 3 → List Bool) (i : ℕ)
    (hi : i < (v 0).length) :
    ((binaryDictionaryCoefficients v).drop (i * (((v 0).length + 1) * (v 1).length))).take
      (((v 0).length + 1) * (v 1).length) =
      binaryDictionaryRow ![v 0, v 1, v 2, (v 0).drop ((v 0).length - i)] := by
  have h := binarySignedTable_field rowTerm (v 0) (smash (true :: v 0) (v 1)) v i hi
  rw [smash_length, List.length_cons] at h
  change _ = binarySignedFixed (smash (true :: v 0) (v 1)) (binaryDictionaryRow _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · rw [binaryDictionaryRow_length, smash_length, List.length_cons]
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
  have h := binarySignedTable_field directionTerm (v 0) (v 1) v i hi
  change _ = binarySignedFixed (v 1) (binaryCramerNumerator _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · exact binaryCramerNumerator_length _

end GameTheory.Complexity.Backend
