import GameTheoryComplexity.Backend.BinaryBirdDeterminantCorrectness
import GameTheoryComplexity.Backend.BinaryCramerMachine
import GameTheory.Math.IntegerCramerComputation

/-! Packed Cramer computation agrees with integer column replacement and signed Cramer fields. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem cramerEntry_value (v : Fin 7 → List Bool) :
    binarySignedValue (binaryCramerEntry v) =
      if (v 1).length = (v 6).length then binarySignedRowValue (v 3) (v 5) (v 0).length
      else binarySignedRowValue (v 3) (v 4) ((v 0).length * (v 2).length + (v 1).length) := by
  rcases lenEqFlag_flag (v 1) (v 6) with hf | hf
  · have he := (lenEqFlag_eq_true_iff _ _).mp hf
    simp only [binaryCramerEntry, hf, caseBit₀, Bool.cond_true, he, ↓reduceIte]
    rfl
  · have he : (v 1).length ≠ (v 6).length := by
      intro h
      have ht := (lenEqFlag_eq_true_iff (v 1) (v 6)).mpr h
      simp [hf] at ht
    simp only [binaryCramerEntry, hf, caseBit₀, Bool.cond_false, he, ↓reduceIte]
    exact binaryBirdField_value _

theorem binaryCramerMatrix_value (dim width A b column : List Bool) (h : ℕ)
    (k : Fin dim.length) (hk : column.length = k.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (hb : ∀ i : Fin dim.length, (binarySignedRowValue width b i.val).natAbs ≤ 2 ^ h) :
    binaryBirdMatrix dim width (binaryCramerMatrix ![dim, width, A, b, column]) =
      (binaryBirdMatrix dim width A).updateCol k (fun i => binarySignedRowValue width b i.val) := by
  have hr : 0 < width.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  have hpow : 2 ^ h < 2 ^ (width.length - 1) := by
    apply Nat.pow_lt_pow_right (by decide)
    rw [hw]
    unfold GameTheory.Math.BirdIterationBounds.workWidth GameTheory.Math.BirdIterationBounds.width
    omega
  ext i j
  let ri := dim.drop (dim.length - i.val)
  let rj := dim.drop (dim.length - j.val)
  have hi : ri.length = i.val := by dsimp [ri]; rw [List.length_drop]; omega
  have hj : rj.length = j.val := by dsimp [rj]; rw [List.length_drop]; omega
  have he : binarySignedValue (binaryCramerEntry ![ri, rj, dim, width, A, b, column]) =
      if j.val = k.val then binarySignedRowValue width b i.val
      else binarySignedRowValue width A (i.val * dim.length + j.val) := by
    have hh := cramerEntry_value ![ri, rj, dim, width, A, b, column]
    change binarySignedValue (binaryCramerEntry ![ri, rj, dim, width, A, b, column]) =
      (if rj.length = column.length then binarySignedRowValue width b ri.length
      else binarySignedRowValue width A (ri.length * dim.length + rj.length)) at hh
    rw [hi, hj, hk] at hh
    exact hh
  have hfit : (binarySignedValue (binaryCramerEntry ![ri, rj, dim, width, A, b, column])).natAbs <
      2 ^ (width.length - 1) := by
    rw [he]
    split_ifs
    · exact (hb i).trans_lt hpow
    · exact (hA i j).trans_lt hpow
  have hf := congrArg binarySignedValue
    (binaryCramerMatrix_field ![dim, width, A, b, column] i.val j.val i.isLt j.isLt)
  have hv := (binarySignedFixed_value width
    (binaryCramerEntry ![ri, rj, dim, width, A, b, column]) hr hfit).trans he
  have hfield := hf.trans hv
  change binaryBirdMatrix dim width (binaryCramerMatrix ![dim, width, A, b, column]) i j =
    (if j.val = k.val then binarySignedRowValue width b i.val
      else binarySignedRowValue width A (i.val * dim.length + j.val)) at hfield
  simpa only [Matrix.updateCol_apply, Fin.ext_iff, binaryBirdMatrix] using hfield
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

theorem binaryCramerDeterminant_det (dim width A b column : List Bool) (h : ℕ)
    (k : Fin dim.length) (hk : column.length = k.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (hb : ∀ i : Fin dim.length, (binarySignedRowValue width b i.val).natAbs ≤ 2 ^ h) :
    binarySignedValue (binaryCramerDeterminant ![dim, width, A, b, column]) =
      ((binaryBirdMatrix dim width A).updateCol k (fun i => binarySignedRowValue width b i.val)).det := by
  have he := binaryCramerMatrix_value dim width A b column h k hk hw hA hb
  have hf : ∀ i j,
      (binaryBirdMatrix dim width (binaryCramerMatrix ![dim, width, A, b, column]) i j).natAbs ≤ 2 ^ h := by
    rw [he]
    intro i j
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact hb i
    · exact hA i j
  have hl : (binaryCramerMatrix ![dim, width, A, b, column]).length =
      dim.length * dim.length * width.length := by
    have ht := binaryCramerMatrix_length ![dim, width, A, b, column]
    change _ = dim.length * (dim.length * width.length) at ht
    simpa only [Nat.mul_assoc] using ht
  exact (binaryBirdDeterminant_value dim width (binaryCramerMatrix ![dim, width, A, b, column]) h hw hl hf).trans
    (congrArg Matrix.det he)

theorem binaryCramerDeterminant_value (dim width A b column : List Bool) (h : ℕ)
    (k : Fin dim.length) (hk : column.length = k.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (hb : ∀ i : Fin dim.length, (binarySignedRowValue width b i.val).natAbs ≤ 2 ^ h) :
    binarySignedValue (binaryCramerDeterminant ![dim, width, A, b, column]) =
      GameTheory.Math.IntegerCramerComputation.determinant
        ((binaryBirdMatrix dim width A).updateCol k (fun i => binarySignedRowValue width b i.val)) :=
  (binaryCramerDeterminant_det dim width A b column h k hk hw hA hb).trans
    (GameTheory.Math.IntegerCramerComputation.determinant_eq _).symm

theorem binaryCramerNumerator_value (dim width A b column : List Bool) (h : ℕ)
    (k : Fin dim.length) (hk : column.length = k.val)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (hb : ∀ i : Fin dim.length, (binarySignedRowValue width b i.val).natAbs ≤ 2 ^ h) :
    binarySignedValue (binaryCramerNumerator ![dim, width, A, b, column]) =
      GameTheory.Math.IntegerCramerComputation.signedNumerator (binaryBirdMatrix dim width A)
        (fun i => binarySignedRowValue width b i.val) k := by
  have hr : 0 < width.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  have hbase := binaryBirdDeterminant_value dim width A h hw hlen hA
  have hd := binaryCramerDeterminant_det dim width A b column h k hk hw hA hb
  have hl : (binaryCramerDeterminant ![dim, width, A, b, column]).length = width.length :=
    binaryBirdDeterminant_length _
  have hmag := binarySignedFixed_natAbs_lt width (binaryCramerDeterminant ![dim, width, A, b, column])
  rw [binarySignedFixed_eq_of_length _ _ hl] at hmag
  have hm : (binarySignedValue (binarySignedSign (binaryBirdDeterminant ![dim, width, A])) *
      binarySignedValue (binaryCramerDeterminant ![dim, width, A, b, column])).natAbs <
        2 ^ (width.length - 1) := by
    rw [binarySignedSign_value, Int.natAbs_mul]
    by_cases hz : binarySignedValue (binaryBirdDeterminant ![dim, width, A]) = 0
    · simp only [hz, Int.sign_zero, Int.natAbs_zero, Nat.zero_mul]
      positivity
    · rw [Int.natAbs_sign_of_ne_zero hz, Nat.one_mul]
      exact hmag
  change binarySignedValue (binarySignedFixedMul width
    (binarySignedSign (binaryBirdDeterminant ![dim, width, A]))
    (binaryCramerDeterminant ![dim, width, A, b, column])) = _
  rw [binarySignedFixedMul_value _ _ _ hr hm, binarySignedSign_value, hbase, hd]
  exact (GameTheory.Math.IntegerCramerComputation.signedNumerator_eq _ _ _).symm
end GameTheory.Complexity.Backend
