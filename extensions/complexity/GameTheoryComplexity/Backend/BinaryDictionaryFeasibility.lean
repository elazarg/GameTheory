import GameTheoryComplexity.Backend.BinarySignedRowSelection
import GameTheoryComplexity.Backend.BinaryIndexedAll

/-! Exact strict lexicographic positivity checks for packed symbolic rows. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Reject effective zero regardless of sign or magnitude padding. -/
def binarySignedNonzero (x : List Bool) : List Bool :=
  orBit (binarySignedLTFlag x []) (binarySignedLTFlag [] x)

theorem binarySignedNonzero_cobham : Cobham fun v : Fin 1 → List Bool =>
    binarySignedNonzero (v 0) :=
  Cobham.orFn (Cobham.comp₂ binarySignedLTFlag_cobham (.proj 0) Cobham.empty)
    (Cobham.comp₂ binarySignedLTFlag_cobham Cobham.empty (.proj 0))

theorem binarySignedNonzero_value (x : List Bool) :
    binarySignedNonzero x = [decide (binarySignedValue x ≠ 0)] := by
  rw [binarySignedNonzero, binarySignedLTFlag_value, binarySignedLTFlag_value]
  change orBit [decide (binarySignedValue x < 0)] [decide (0 < binarySignedValue x)] = _
  rcases lt_trichotomy (binarySignedValue x) 0 with h | h | h
  · simp [orBit, caseBit₀, h, h.ne]
  · simp [orBit, caseBit₀, h]
  · simp [orBit, caseBit₀, h, h.ne', not_lt_of_ge h.le]

/-- Arguments are row, coefficient count, field width and packed coefficients. -/
def binaryDictionaryRowPositive (v : Fin 4 → List Bool) : List Bool :=
  binarySignedRowLT ![v 1, v 2, [], binarySignedRowBlock v, [false, true], [false, true]]

theorem binaryDictionaryRowPositive_cobham : Cobham binaryDictionaryRowPositive := by
  apply Cobham.comp binarySignedRowLT_cobham
  intro i
  fin_cases i
  · exact .proj 1
  · exact .proj 2
  · exact Cobham.empty
  · exact binarySignedRowBlock_cobham
  · exact Cobham.const [false, true]
  · exact Cobham.const [false, true]

theorem binaryDictionaryRowPositive_value (v : Fin 4 → List Bool) :
    binaryDictionaryRowPositive v = [GameTheory.Math.FiniteLexicographicCompare.lexLT
      (fun _ : Fin (v 1).length => 0)
      (fun j => binarySignedMatrixValue (v 1) (v 2) (v 3) (v 0).length j.val)] := by
  rw [binaryDictionaryRowPositive, binarySignedRowLT_compare]
  congr 1
  unfold GameTheory.Math.IntegerRatioSelection.compare
  congr 1 <;> funext j
  · simp [binarySignedRowValue, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  · change binarySignedRowValue (v 2) (binarySignedRowBlock v) j.val * 1 = _
    exact mul_one _

/-- Check strict symbolic positivity of every stored row. Arguments are row count,
coefficient count, field width and packed coefficients. -/
def binaryDictionaryPositive (v : Fin 4 → List Bool) : List Bool :=
  binaryIndexedAll binaryDictionaryRowPositive (v 0) (Fin.tail v)

theorem binaryDictionaryPositive_cobham : Cobham binaryDictionaryPositive :=
  binaryIndexedAll_cobham binaryDictionaryRowPositive_cobham

theorem binaryDictionaryPositive_mem_FPn : FPn binaryDictionaryPositive :=
  cobham_iff_FPn.mp binaryDictionaryPositive_cobham

theorem binaryDictionaryPositive_value (v : Fin 4 → List Bool) :
    binaryDictionaryPositive v = [decide (∀ i < (v 0).length,
      GameTheory.Math.FiniteLexicographicCompare.lexLT (fun _ : Fin (v 1).length => 0)
        (fun j => binarySignedMatrixValue (v 1) (v 2) (v 3) i j.val) = true)] := by
  apply binaryIndexedAll_value
  intro r
  rw [binaryDictionaryRowPositive_value]
  change [GameTheory.Math.FiniteLexicographicCompare.lexLT
    (fun _ : Fin (v 1).length => 0)
    (fun j => binarySignedMatrixValue (v 1) (v 2) (v 3) r.length j.val)] = _
  congr 1
  generalize GameTheory.Math.FiniteLexicographicCompare.lexLT
    (fun _ : Fin (v 1).length => (0 : ℤ))
    (fun j => binarySignedMatrixValue (v 1) (v 2) (v 3) r.length j.val) = b
  cases b <;> rfl

end GameTheory.Complexity.Backend
