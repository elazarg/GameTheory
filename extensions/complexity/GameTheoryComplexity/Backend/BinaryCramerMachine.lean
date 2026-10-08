import GameTheoryComplexity.Backend.BinaryBirdDeterminantMachine

/-! Packed column replacement and signed Cramer numerator machines.
All scalar and matrix buffers retain their supplied field width. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem reindex {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    (hf : Cobham f) (idx : Fin m → Fin n) :
    Cobham fun v : Fin n → List Bool => f (fun i => v (idx i)) :=
  Cobham.comp hf fun i => Cobham.proj (idx i)

/-- Sign of an arbitrary signed word, including padded positive or negative zero. -/
def binarySignedSign (x : List Bool) : List Bool :=
  caseBit₀ (binarySignedLTFlag x []) [true, true]
    (caseBit₀ (binarySignedLTFlag [] x) [false, true] [false])

theorem binarySignedSign_value (x : List Bool) :
    binarySignedValue (binarySignedSign x) = Int.sign (binarySignedValue x) := by
  rw [binarySignedSign, binarySignedLTFlag_value, binarySignedLTFlag_value]
  change binarySignedValue (caseBit₀ [decide (binarySignedValue x < 0)] [true, true]
    (caseBit₀ [decide (0 < binarySignedValue x)] [false, true] [false])) = _
  rcases lt_trichotomy (binarySignedValue x) 0 with h | h | h
  · simp only [caseBit₀, Bool.cond_decide, ite_eq_left h,
      Int.sign_eq_neg_one_of_neg h]
    rfl
  · simp only [h, caseBit₀, Bool.cond_decide, lt_self_iff_false,
      ↓reduceIte, Int.sign_zero]
    rfl
  · simp only [caseBit₀, Bool.cond_decide, ite_eq_right (not_lt_of_ge h.le),
      ite_eq_left h, Int.sign_eq_one_of_pos h]
    rfl

theorem binarySignedSign_cobham : Cobham fun v : Fin 1 → List Bool => binarySignedSign (v 0) :=
  Cobham.iteFn (Cobham.comp₂ binarySignedLTFlag_cobham (.proj 0) Cobham.empty)
    (Cobham.const [true, true])
    (Cobham.iteFn (Cobham.comp₂ binarySignedLTFlag_cobham Cobham.empty (.proj 0))
      (Cobham.const [false, true]) (Cobham.const [false]))

/-- Arguments: row, column, dimension, field width, matrix, replacement vector, replaced column. -/
def binaryCramerEntry (v : Fin 7 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 1) (v 6))
    (binarySignedRowField ![v 0, v 3, v 5])
    (binaryBirdField ![v 0, v 1, v 2, v 3, v 4])

theorem binaryCramerEntry_cobham : Cobham binaryCramerEntry := by
  have hf : Cobham fun v : Fin 7 → List Bool => binaryBirdField ![v 0, v 1, v 2, v 3, v 4] :=
    (reindex binaryBirdField_cobham (![0, 1, 2, 3, 4] : Fin 5 → Fin 7)).of_eq fun v => by
      congr 1; ext i; fin_cases i <;> rfl
  exact Cobham.iteFn (lenEqFlag_mem (.proj 1) (.proj 6))
    (Cobham.comp₃ binarySignedRowField_cobham (.proj 0) (.proj 3) (.proj 5)) hf

private def cramerRowTerm (v : Fin 7 → List Bool) : List Bool :=
  binaryCramerEntry ![v 6, v 0, v 1, v 2, v 3, v 4, v 5]

private theorem cramerRowTerm_cobham : Cobham cramerRowTerm :=
  (reindex binaryCramerEntry_cobham (![6, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 7)).of_eq fun v => by
    congr 1; ext i; fin_cases i <;> rfl

/-- Arguments: dimension, field width, matrix, replacement vector, replaced column, row. -/
def binaryCramerRow (v : Fin 6 → List Bool) : List Bool :=
  binarySignedTable cramerRowTerm (v 0) (v 1) v

@[simp] theorem binaryCramerRow_length (v : Fin 6 → List Bool) :
    (binaryCramerRow v).length = (v 0).length * (v 1).length :=
  binarySignedTable_length _ _ _ _

theorem binaryCramerRow_cobham : Cobham binaryCramerRow := by
  exact (reindex (binarySignedTable_cobham cramerRowTerm_cobham)
    (![0, 1, 0, 1, 2, 3, 4, 5] : Fin 8 → Fin 6)).of_eq fun v => by
      change binarySignedTable cramerRowTerm (v 0) (v 1) _ = _
      congr 1; ext i; fin_cases i <;> rfl

private def cramerMatrixTerm (v : Fin 6 → List Bool) : List Bool :=
  binaryCramerRow ![v 1, v 2, v 3, v 4, v 5, v 0]

private theorem cramerMatrixTerm_cobham : Cobham cramerMatrixTerm :=
  (reindex binaryCramerRow_cobham (![1, 2, 3, 4, 5, 0] : Fin 6 → Fin 6)).of_eq fun v => by
    congr 1; ext i; fin_cases i <;> rfl

/-- Arguments: dimension, field width, matrix, replacement vector, replaced column. -/
def binaryCramerMatrix (v : Fin 5 → List Bool) : List Bool :=
  binarySignedTable cramerMatrixTerm (v 0) (smash (v 0) (v 1)) v

@[simp] theorem binaryCramerMatrix_length (v : Fin 5 → List Bool) :
    (binaryCramerMatrix v).length = (v 0).length * ((v 0).length * (v 1).length) := by
  rw [binaryCramerMatrix, binarySignedTable_length, smash_length]

theorem binaryCramerMatrix_cobham : Cobham binaryCramerMatrix := by
  have args : ∀ i : Fin 7, Cobham fun v : Fin 5 → List Bool =>
      (Fin.cons (v 0) (Fin.cons (smash (v 0) (v 1)) v) : Fin 7 → List Bool) i := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact Cobham.comp₂ Cobham.smash (.proj 0) (.proj 1)
    all_goals exact .proj _
  exact (Cobham.comp (binarySignedTable_cobham cramerMatrixTerm_cobham) args).of_eq fun _ => rfl

/-- The determinant of the supplied matrix with one column replaced. -/
def binaryCramerDeterminant (v : Fin 5 → List Bool) : List Bool :=
  binaryBirdDeterminant ![v 0, v 1, binaryCramerMatrix v]

theorem binaryCramerDeterminant_cobham : Cobham binaryCramerDeterminant :=
  Cobham.comp₃ binaryBirdDeterminant_cobham (.proj 0) (.proj 1) binaryCramerMatrix_cobham

/-- Sign-adjusted Cramer numerator; the determinant sign is computed by the same machine. -/
def binaryCramerNumerator (v : Fin 5 → List Bool) : List Bool :=
  binarySignedFixedMul (v 1)
    (binarySignedSign (binaryBirdDeterminant ![v 0, v 1, v 2]))
    (binaryCramerDeterminant v)

theorem binaryCramerNumerator_cobham : Cobham binaryCramerNumerator := by
  have hd : Cobham fun v : Fin 5 → List Bool => binaryBirdDeterminant ![v 0, v 1, v 2] :=
    Cobham.comp₃ binaryBirdDeterminant_cobham (.proj 0) (.proj 1) (.proj 2)
  have hs := Cobham.comp binarySignedSign_cobham fun _ : Fin 1 => hd
  exact (Cobham.comp₃ binarySignedFixedMul_cobham (.proj 1) hs
    binaryCramerDeterminant_cobham).of_eq fun _ => rfl

@[simp] theorem binaryCramerNumerator_length (v : Fin 5 → List Bool) :
    (binaryCramerNumerator v).length = (v 1).length := binarySignedFixedMul_length _ _ _

theorem binaryCramerMatrix_mem_FPn : FPn binaryCramerMatrix :=
  cobham_iff_FPn.mp binaryCramerMatrix_cobham

theorem binaryCramerDeterminant_mem_FPn : FPn binaryCramerDeterminant :=
  cobham_iff_FPn.mp binaryCramerDeterminant_cobham

theorem binaryCramerNumerator_mem_FPn : FPn binaryCramerNumerator :=
  cobham_iff_FPn.mp binaryCramerNumerator_cobham

/-- Extracting a stored row recovers its byte representation exactly. -/
theorem binaryCramerMatrix_row (v : Fin 5 → List Bool) (i : ℕ) (hi : i < (v 0).length) :
    ((binaryCramerMatrix v).drop (i * ((v 0).length * (v 1).length))).take
      ((v 0).length * (v 1).length) =
      binaryCramerRow ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - i)] := by
  have h := binarySignedTable_field cramerMatrixTerm (v 0) (smash (v 0) (v 1)) v i hi
  rw [smash_length] at h
  change _ = binarySignedFixed (smash (v 0) (v 1)) (binaryCramerRow _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · rw [binaryCramerRow_length, smash_length]
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
