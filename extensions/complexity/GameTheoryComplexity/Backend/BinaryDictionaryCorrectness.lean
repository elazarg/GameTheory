import GameTheoryComplexity.Backend.BinaryCramerCorrectness
import GameTheoryComplexity.Backend.BinaryDictionaryMachine
import GameTheory.Math.IntegerDictionaryComputation

/-! Signed packed dictionary fields agree with the canonical integer Cramer dictionary. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem unitVector_value (dim width column : List Bool) (i : ℕ) (hi : i < dim.length)
    (hr : 0 < width.length) (hc : 1 < 2 ^ (width.length - 1)) :
    binarySignedRowValue width (binaryUnitVector ![dim, width, column]) i =
      if i = column.length then 1 else 0 := by
  unfold binaryUnitVector
  apply binarySignedTable_value _ _ _ (fun t => if t = column.length then 1 else 0) _ hr _ _ i hi
  · intro r
    change binarySignedValue (caseBit₀ (lenEqFlag r column) [false, true] [false]) = _
    rcases lenEqFlag_flag r column with hf | hf
    · have he := (lenEqFlag_eq_true_iff _ _).mp hf
      simp [hf, he, caseBit₀, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
    · have he : r.length ≠ column.length := by
        intro he
        have ht := (lenEqFlag_eq_true_iff r column).mpr he
        simp [hf] at ht
      simp [hf, he, caseBit₀, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  · intro t ht
    split_ifs
    · exact hc
    · simp

private theorem onesVector_value (dim width : List Bool) (i : ℕ) (hi : i < dim.length)
    (hr : 0 < width.length) (hc : 1 < 2 ^ (width.length - 1)) :
    binarySignedRowValue width (binaryOnesVector ![dim, width]) i = 1 := by
  unfold binaryOnesVector
  apply binarySignedTable_value _ _ _ (fun _ => 1) _ hr _ _ i hi
  · intro r
    rfl
  · intro t ht
    exact hc

theorem binaryDictionaryVector_value (dim width column : List Bool)
    (k : Fin (dim.length + 1)) (hk : column.length = k.val)
    (hr : 0 < width.length) (hc : 1 < 2 ^ (width.length - 1)) (i : Fin dim.length) :
    binarySignedRowValue width (binaryDictionaryVector ![dim, width, column]) i.val =
      Fin.cases (fun _ => (1 : ℤ)) (fun j => Pi.single j 1) k i := by
  cases k using Fin.cases with
  | zero =>
    have he : column = [] := by simpa using hk
    subst column
    exact onesVector_value dim width i.val i.isLt hr hc
  | succ j =>
    cases column with
    | nil => simp at hk
    | cons b r =>
      have he : r.length = j.val := by simp only [List.length_cons, Fin.val_succ] at hk; omega
      unfold binaryDictionaryVector
      change binarySignedRowValue width (caseBit₀ (nonemptyFlag (b :: r))
        (binaryUnitVector ![dim, width, r]) (binaryOnesVector ![dim, width])) i.val = _
      rw [nonemptyFlag_cons]
      simp only [caseBit₀, Bool.cond_true]
      rw [unitVector_value dim width r i.val i.isLt hr hc, he]
      simp [Pi.single_apply, Fin.ext_iff]
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

theorem binaryDictionaryCoefficient_value (dim width A row column : List Bool) (h : ℕ)
    (i : Fin dim.length) (k : Fin (dim.length + 1))
    (hi : row.length = i.val) (hk : column.length = k.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h) :
    binarySignedValue (binaryDictionaryCoefficient ![dim, width, A, row, column]) =
      GameTheory.Math.IntegerDictionaryComputation.coefficients (binaryBirdMatrix dim width A) (fun _ => 1) i k := by
  have hr : 0 < width.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  have hcap : 1 < 2 ^ (width.length - 1) := by
    have hl : 2 ≤ width.length := by rw [hw]; unfold GameTheory.Math.BirdIterationBounds.workWidth; omega
    exact Nat.one_lt_two_pow (by omega)
  have hv : (fun j : Fin dim.length => binarySignedRowValue width
      (binaryDictionaryVector ![dim, width, column]) j.val) =
      Fin.cases (fun _ => (1 : ℤ)) (fun j => Pi.single j 1) k := by
    funext j
    exact binaryDictionaryVector_value dim width column k hk hr hcap j
  have hb : ∀ j : Fin dim.length,
      (binarySignedRowValue width (binaryDictionaryVector ![dim, width, column]) j.val).natAbs ≤ 2 ^ h := by
    change ∀ j, ((fun j : Fin dim.length => binarySignedRowValue width
      (binaryDictionaryVector ![dim, width, column]) j.val) j).natAbs ≤ _
    rw [hv]
    cases k using Fin.cases with
    | zero => intro j; exact Nat.one_le_pow h 2 (by decide)
    | succ a =>
      intro j
      simp only [Fin.cases_succ, Pi.single_apply]
      split_ifs
      · exact Nat.one_le_pow h 2 (by decide)
      · simp
  have hc := binaryCramerNumerator_value dim width A
    (binaryDictionaryVector ![dim, width, column]) row h i hi hw hlen hA hb
  rw [hv] at hc
  have he := congrArg (fun C => C i k)
    (GameTheory.Math.IntegerDictionaryComputation.coefficients_eq (binaryBirdMatrix dim width A) (fun _ => 1))
  cases k using Fin.cases <;> exact hc.trans he.symm
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

theorem binaryDictionaryRow_value (dim width A row : List Bool) (h : ℕ)
    (i : Fin dim.length) (hi : row.length = i.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (k : Fin (dim.length + 1)) :
    binarySignedRowValue width (binaryDictionaryRow ![dim, width, A, row]) k.val =
      GameTheory.Math.IntegerDictionaryComputation.coefficients (binaryBirdMatrix dim width A) (fun _ => 1) i k := by
  have hk : ((true :: dim).drop (dim.length + 1 - k.val)).length = k.val := by
    rw [List.length_drop, List.length_cons]
    omega
  exact (congrArg binarySignedValue
    (binaryDictionaryRow_field ![dim, width, A, row] k.val k.isLt)).trans
      (binaryDictionaryCoefficient_value dim width A row
        ((true :: dim).drop (dim.length + 1 - k.val)) h i k hi hk hw hlen hA)

theorem binaryDictionaryCoefficients_value (dim width A : List Bool) (h : ℕ)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (i : Fin dim.length) (k : Fin (dim.length + 1)) :
    binarySignedRowValue width (binaryDictionaryCoefficients ![dim, width, A])
      (i.val * (dim.length + 1) + k.val) =
      GameTheory.Math.IntegerDictionaryComputation.coefficients (binaryBirdMatrix dim width A) (fun _ => 1) i k := by
  have hi : (dim.drop (dim.length - i.val)).length = i.val := by rw [List.length_drop]; omega
  have hk : ((true :: dim).drop (dim.length + 1 - k.val)).length = k.val := by
    rw [List.length_drop, List.length_cons]
    omega
  exact (congrArg binarySignedValue
    (binaryDictionaryCoefficients_field ![dim, width, A] i.val k.val i.isLt k.isLt)).trans
      (binaryDictionaryCoefficient_value dim width A (dim.drop (dim.length - i.val))
        ((true :: dim).drop (dim.length + 1 - k.val)) h i k hi hk hw hlen hA)

theorem binaryDictionaryDirection_value (dim width A c : List Bool) (h : ℕ)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (hc : ∀ i : Fin dim.length, (binarySignedRowValue width c i.val).natAbs ≤ 2 ^ h)
    (i : Fin dim.length) :
    binarySignedRowValue width (binaryDictionaryDirection ![dim, width, A, c]) i.val =
      GameTheory.Math.IntegerDictionaryComputation.direction (binaryBirdMatrix dim width A)
        (fun j => binarySignedRowValue width c j.val) i := by
  have hi : (dim.drop (dim.length - i.val)).length = i.val := by rw [List.length_drop]; omega
  exact ((congrArg binarySignedValue
    (binaryDictionaryDirection_field ![dim, width, A, c] i.val i.isLt)).trans
      (binaryCramerNumerator_value dim width A c (dim.drop (dim.length - i.val)) h i hi hw hlen hA hc)).trans
        (GameTheory.Math.IntegerDictionaryComputation.direction_eq _ _ _).symm
end GameTheory.Complexity.Backend
