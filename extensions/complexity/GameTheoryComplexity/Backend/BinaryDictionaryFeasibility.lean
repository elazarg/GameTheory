module

public import GameTheoryComplexity.Backend.BinarySignedRowSelection
public import GameTheoryComplexity.Backend.BinaryIndexedAll

@[expose] public section

/-! Exact strict lexicographic positivity checks for packed symbolic rows. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Reject effective zero regardless of sign or magnitude padding. -/
def binarySignedNonzero (x : List Bool) : List Bool :=
  orFlag (binarySignedLTFlag x []) (binarySignedLTFlag [] x)

@[fun_prop] theorem binarySignedNonzero_polyTime :
    ComputableInPolyTime binarySignedNonzero encBits encBits := by
  have hnegative := binarySignedLTFlag_polyTime (ComputableInPolyTime.id' (encIn := encBits))
    (ComputableInPolyTime.const [])
  have hpositive := binarySignedLTFlag_polyTime (ComputableInPolyTime.const [])
    (ComputableInPolyTime.id' (encIn := encBits))
  exact orFlag_polyTime.comp (hnegative.prod hpositive)

theorem binarySignedNonzero_value (x : List Bool) :
    binarySignedNonzero x = [decide (binarySignedValue x ≠ 0)] := by
  rw [binarySignedNonzero, binarySignedLTFlag_value, binarySignedLTFlag_value]
  change orFlag [decide (binarySignedValue x < 0)] [decide (0 < binarySignedValue x)] = _
  rcases lt_trichotomy (binarySignedValue x) 0 with h | h | h
  · simp [orFlag, h, h.ne]
  · simp [orFlag, h]
  · simp [orFlag, h, h.ne', not_lt_of_ge h.le]

/-- Arguments are row, coefficient count, field width and packed coefficients. -/
def binaryDictionaryRowPositive (v : Fin 4 → List Bool) : List Bool :=
  binarySignedRowLT ![v 1, v 2, [], binarySignedRowBlock v, [false, true], [false, true]]

@[fun_prop] theorem binaryDictionaryRowPositive_polyTime :
    ComputableInPolyTime binaryDictionaryRowPositive (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        ![v 1, v 2, [], binarySignedRowBlock v, [false, true], [false, true]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .const []
    · exact binarySignedRowBlock_polyTime
    · exact .const [false, true]
    · exact .const [false, true]
  exact binarySignedRowLT_polyTime.comp hargs

theorem binaryDictionaryRowPositive_value (v : Fin 4 → List Bool) :
    binaryDictionaryRowPositive v = [GameTheory.Math.FiniteLexicographicCompare.lexLT
      (fun _ : Fin (v 1).length => 0)
      (fun j => binarySignedMatrixValue (v 1) (v 2) (v 3) (v 0).length j.val)] := by
  rw [binaryDictionaryRowPositive, binarySignedRowLT_compare]
  congr 1
  unfold GameTheory.Math.IntegerRatioSelection.compare
  congr 1 <;> funext j
  · simp [binarySignedRowValue, binarySignedValue, Turing.MultiTapeTM.ofBits]
  · change binarySignedRowValue (v 2) (binarySignedRowBlock v) j.val * 1 = _
    exact mul_one _

/-- Check strict symbolic positivity of every stored row. Arguments are row count,
coefficient count, field width and packed coefficients. -/
def binaryDictionaryPositive (v : Fin 4 → List Bool) : List Bool :=
  binaryIndexedAll binaryDictionaryRowPositive (v 0) (Fin.tail v)

@[fun_prop] theorem binaryDictionaryPositive_polyTime :
    ComputableInPolyTime binaryDictionaryPositive (encPi encBits) encBits :=
  binaryIndexedAll_polyTime (p := 3) binaryDictionaryRowPositive_polyTime

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

end GameTheory.Complexity.Backend
