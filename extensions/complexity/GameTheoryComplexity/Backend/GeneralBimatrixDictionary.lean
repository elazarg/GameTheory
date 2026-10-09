import GameTheoryComplexity.Backend.GeneralBimatrixMatrixWord
import GameTheoryComplexity.Backend.BinaryBirdWidth
import GameTheoryComplexity.Backend.BinaryDictionaryCorrectness
import GameTheoryComplexity.Backend.BinarySignedRowSelection

/-! Certified dictionary computations on serialized rectangular bimatrix instances.
Inputs are the instance, raw basis membership, and entering-variable position ruler.
Dimension and storage capacity are computed from the serialized instance itself. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The complementary-system dimension, derived from the input. -/
def generalBimatrixDictionaryDimension (v : Fin 3 → List Bool) := generalBimatrixDimensionWord (v 0)
/-- Magnitude exponent ruler for positively shifted integer columns. -/
def generalBimatrixDictionaryInputWidth (v : Fin 3 → List Bool) := generalBitsRuler (v 0) ++ [true, true]
/-- Polynomial working field width, including its sign bit. -/
def generalBimatrixDictionaryWidth (v : Fin 3 → List Bool) :=
  binaryBirdWorkWidth ![generalBimatrixDictionaryDimension v, generalBimatrixDictionaryInputWidth v]
/-- Canonically sorted basis columns in fixed-width row-major storage. -/
def generalBimatrixDictionaryMatrix (v : Fin 3 → List Bool) :=
  generalBimatrixBasisMatrixWord ![generalBimatrixDictionaryWidth v, v 1, v 0]
/-- The signed basis determinant. -/
def generalBimatrixDictionaryDeterminant (v : Fin 3 → List Bool) :=
  binaryBirdDeterminant ![generalBimatrixDictionaryDimension v, generalBimatrixDictionaryWidth v,
    generalBimatrixDictionaryMatrix v]
/-- All constant and perturbation numerators over a common determinant scale. -/
def generalBimatrixDictionaryCoefficients (v : Fin 3 → List Bool) :=
  binaryDictionaryCoefficients ![generalBimatrixDictionaryDimension v, generalBimatrixDictionaryWidth v,
    generalBimatrixDictionaryMatrix v]

private def dictionaryColumnTerm (v : Fin 4 → List Bool) :=
  generalBimatrixColumnWord ![v 0, binaryHalfRuler (v 3), binaryLengthParity (v 3), v 1]
/-- The entering system column, normalized to the working width. -/
def generalBimatrixDictionaryColumn (v : Fin 3 → List Bool) :=
  binarySignedTable dictionaryColumnTerm (generalBimatrixDictionaryDimension v)
    (generalBimatrixDictionaryWidth v) v
/-- Signed entering-direction numerators. -/
def generalBimatrixDictionaryDirection (v : Fin 3 → List Bool) :=
  binaryDictionaryDirection ![generalBimatrixDictionaryDimension v, generalBimatrixDictionaryWidth v,
    generalBimatrixDictionaryMatrix v, generalBimatrixDictionaryColumn v]
/-- Earliest eligible lexicographic minimum ratio, encoded by found header and index-ruler tail. -/
def generalBimatrixDictionarySelectedRow (v : Fin 3 → List Bool) :=
  binarySignedRowSelect ![generalBimatrixDictionaryDimension v, true :: generalBimatrixDictionaryDimension v,
    generalBimatrixDictionaryWidth v, generalBimatrixDictionaryCoefficients v,
    generalBimatrixDictionaryDirection v]

theorem generalBimatrixDictionaryDimension_cobham : Cobham generalBimatrixDictionaryDimension :=
  (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 0).of_eq fun _ => rfl

theorem generalBimatrixDictionaryInputWidth_cobham : Cobham generalBimatrixDictionaryInputWidth :=
  Cobham.appendFn ((Cobham.comp generalBitsRuler_cobham fun _ => .proj 0).of_eq fun _ => rfl)
    (Cobham.const [true, true])

theorem generalBimatrixDictionaryWidth_cobham : Cobham generalBimatrixDictionaryWidth :=
  Cobham.comp₂ binaryBirdWorkWidth_cobham generalBimatrixDictionaryDimension_cobham
    generalBimatrixDictionaryInputWidth_cobham

theorem generalBimatrixDictionaryMatrix_cobham : Cobham generalBimatrixDictionaryMatrix :=
  Cobham.comp₃ generalBimatrixBasisMatrixWord_cobham generalBimatrixDictionaryWidth_cobham (.proj 1) (.proj 0)

theorem generalBimatrixDictionaryDeterminant_cobham : Cobham generalBimatrixDictionaryDeterminant :=
  Cobham.comp₃ binaryBirdDeterminant_cobham generalBimatrixDictionaryDimension_cobham
    generalBimatrixDictionaryWidth_cobham generalBimatrixDictionaryMatrix_cobham

theorem generalBimatrixDictionaryCoefficients_cobham : Cobham generalBimatrixDictionaryCoefficients :=
  Cobham.comp₃ binaryDictionaryCoefficients_cobham generalBimatrixDictionaryDimension_cobham
    generalBimatrixDictionaryWidth_cobham generalBimatrixDictionaryMatrix_cobham

private theorem dictionaryColumnTerm_cobham : Cobham dictionaryColumnTerm := by
  apply Cobham.comp generalBimatrixColumnWord_cobham
  intro i
  fin_cases i
  · exact .proj 0
  · exact (Cobham.comp binaryHalfRuler_cobham fun _ => .proj 3).of_eq fun _ => rfl
  · exact (Cobham.comp binaryLengthParity_cobham fun _ => .proj 3).of_eq fun _ => rfl
  · exact .proj 1

theorem generalBimatrixDictionaryColumn_cobham : Cobham generalBimatrixDictionaryColumn := by
  have hi : ∀ i : Fin 5, Cobham fun v : Fin 3 → List Bool =>
      (Fin.cons (generalBimatrixDictionaryDimension v) (Fin.cons (generalBimatrixDictionaryWidth v) v) : Fin 5 → List Bool) i := by
    intro i
    fin_cases i
    · exact generalBimatrixDictionaryDimension_cobham
    · exact generalBimatrixDictionaryWidth_cobham
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
  exact (Cobham.comp (binarySignedTable_cobham dictionaryColumnTerm_cobham) hi).of_eq fun _ => rfl

theorem generalBimatrixDictionaryDirection_cobham : Cobham generalBimatrixDictionaryDirection := by
  apply Cobham.comp binaryDictionaryDirection_cobham
  intro i
  fin_cases i
  · exact generalBimatrixDictionaryDimension_cobham
  · exact generalBimatrixDictionaryWidth_cobham
  · exact generalBimatrixDictionaryMatrix_cobham
  · exact generalBimatrixDictionaryColumn_cobham

theorem generalBimatrixDictionarySelectedRow_cobham : Cobham generalBimatrixDictionarySelectedRow := by
  apply Cobham.comp binarySignedRowSelect_cobham
  intro i
  fin_cases i
  · exact generalBimatrixDictionaryDimension_cobham
  · exact Cobham.appendFn (Cobham.const [true]) generalBimatrixDictionaryDimension_cobham
  · exact generalBimatrixDictionaryWidth_cobham
  · exact generalBimatrixDictionaryCoefficients_cobham
  · exact generalBimatrixDictionaryDirection_cobham

theorem generalBimatrixDictionaryDimension_mem_FPn : FPn generalBimatrixDictionaryDimension :=
  cobham_iff_FPn.mp generalBimatrixDictionaryDimension_cobham
theorem generalBimatrixDictionaryInputWidth_mem_FPn : FPn generalBimatrixDictionaryInputWidth :=
  cobham_iff_FPn.mp generalBimatrixDictionaryInputWidth_cobham
theorem generalBimatrixDictionaryWidth_mem_FPn : FPn generalBimatrixDictionaryWidth :=
  cobham_iff_FPn.mp generalBimatrixDictionaryWidth_cobham
theorem generalBimatrixDictionaryMatrix_mem_FPn : FPn generalBimatrixDictionaryMatrix :=
  cobham_iff_FPn.mp generalBimatrixDictionaryMatrix_cobham
theorem generalBimatrixDictionaryDeterminant_mem_FPn : FPn generalBimatrixDictionaryDeterminant :=
  cobham_iff_FPn.mp generalBimatrixDictionaryDeterminant_cobham
theorem generalBimatrixDictionaryCoefficients_mem_FPn : FPn generalBimatrixDictionaryCoefficients :=
  cobham_iff_FPn.mp generalBimatrixDictionaryCoefficients_cobham
theorem generalBimatrixDictionaryColumn_mem_FPn : FPn generalBimatrixDictionaryColumn :=
  cobham_iff_FPn.mp generalBimatrixDictionaryColumn_cobham
theorem generalBimatrixDictionaryDirection_mem_FPn : FPn generalBimatrixDictionaryDirection :=
  cobham_iff_FPn.mp generalBimatrixDictionaryDirection_cobham
theorem generalBimatrixDictionarySelectedRow_mem_FPn : FPn generalBimatrixDictionarySelectedRow :=
  cobham_iff_FPn.mp generalBimatrixDictionarySelectedRow_cobham
end GameTheory.Complexity.Backend


namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionaryWidth_length (v : Fin 3 → List Bool) :
    (generalBimatrixDictionaryWidth v).length = GameTheory.Math.BirdIterationBounds.workWidth
      (generalRowCount (v 0) + generalColCount (v 0)) (generalCoefficientBits (v 0) + 2) := by
  simp [generalBimatrixDictionaryWidth, binaryBirdWorkWidth_length,
    generalBimatrixDictionaryDimension, generalBimatrixDictionaryInputWidth, generalCoefficientBits]

private theorem shifted_bound (input : List Bool) (player : Bool) (i j : ℕ) :
    (decodeGeneralPayoff player input i j + ((2 : ℤ) ^ generalCoefficientBits input + 1)).natAbs ≤
      2 ^ (generalCoefficientBits input + 2) := by
  have h := generalShiftedPayoffWord_bound player
    ![List.replicate i true, List.replicate j true, input]
  change (binarySignedValue (generalShiftedPayoffWord player ![List.replicate i true, List.replicate j true, input])).natAbs < 2 ^ (generalCoefficientBits input + 2) at h
  have hv := generalShiftedPayoffWord_value player ![List.replicate i true, List.replicate j true, input]
  change binarySignedValue (generalShiftedPayoffWord player ![List.replicate i true, List.replicate j true, input]) = decodeGeneralPayoff player input (List.replicate i true).length (List.replicate j true).length + ((2 : ℤ) ^ generalCoefficientBits input + 1) at hv
  simp only [List.length_replicate] at hv
  rw [hv] at h
  exact h.le

private theorem dictionaryCandidate_bound (input : List Bool) (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input)
    (i j : Fin (generalRowCount input + generalColCount input)) :
    (generalBimatrixCandidateMatrix input s hs i j).natAbs ≤ 2 ^ (generalCoefficientBits input + 2) :=
  bimatrixIntegerColumns_bound _ _ (generalCoefficientBits input + 2)
    (fun r c => shifted_bound input false r.val c.val)
    (fun r c => shifted_bound input true r.val c.val) i (s.orderEmbOfFin hs j)

theorem generalBimatrixDictionaryCandidateMatrix_integer (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (entering : List Bool)
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membershipWord s, entering])
      (generalBimatrixDictionaryMatrix ![input, membershipWord s, entering])
      (i.val * (generalRowCount input + generalColCount input) + j.val) = generalBimatrixCandidateMatrix input s hs i j := by
  let W := generalBimatrixDictionaryWidth ![input, membershipWord s, entering]
  have hw := generalBimatrixDictionaryWidth_length ![input, membershipWord s, entering]
  change W.length = GameTheory.Math.BirdIterationBounds.workWidth
    (generalRowCount input + generalColCount input) (generalCoefficientBits input + 2) at hw
  have hr : 0 < W.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  have hb : ∀ r c, (generalBimatrixCandidateMatrix input s hs r c).natAbs < 2 ^ (W.length - 1) := by
    intro r c
    apply (dictionaryCandidate_bound input s hs r c).trans_lt
    apply Nat.pow_lt_pow_right (by decide)
    rw [hw]
    unfold GameTheory.Math.BirdIterationBounds.workWidth
    omega
  exact generalBimatrixCandidateMatrixWord_integer input s hs W hr hb i j
end GameTheory.Complexity.Backend



namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionaryCandidateMatrix_hypotheses (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (entering : List Bool) :
    let d := generalBimatrixDimensionWord input
    let W := generalBimatrixDictionaryWidth ![input, membershipWord s, entering]
    let M := generalBimatrixDictionaryMatrix ![input, membershipWord s, entering]
    W.length = GameTheory.Math.BirdIterationBounds.workWidth d.length (generalCoefficientBits input + 2) ∧
    M.length = d.length * d.length * W.length ∧
    ∀ i j, (binaryBirdMatrix d W M i j).natAbs ≤ 2 ^ (generalCoefficientBits input + 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [generalBimatrixDimensionWord_length]
    exact generalBimatrixDictionaryWidth_length _
  · have hl := generalBimatrixBasisMatrixWord_length ![generalBimatrixDictionaryWidth ![input, membershipWord s, entering], membershipWord s, input]
    change (generalBimatrixDictionaryMatrix ![input, membershipWord s, entering]).length = (generalRowCount input + generalColCount input) ^ 2 * (generalBimatrixDictionaryWidth ![input, membershipWord s, entering]).length at hl
    simpa only [generalBimatrixDimensionWord_length, pow_two] using hl
  · intro i j
    have hi : i.val < generalRowCount input + generalColCount input := by
      simpa only [generalBimatrixDimensionWord_length] using i.isLt
    have hj : j.val < generalRowCount input + generalColCount input := by
      simpa only [generalBimatrixDimensionWord_length] using j.isLt
    change (binarySignedRowValue _ _ (i.val * (generalBimatrixDimensionWord input).length + j.val)).natAbs ≤ _
    have ho := congrArg (fun a : ℕ => i.val * a + j.val) (generalBimatrixDimensionWord_length input)
    rw [ho, generalBimatrixDictionaryCandidateMatrix_integer input s hs entering ⟨i.val, hi⟩ ⟨j.val, hj⟩]
    exact dictionaryCandidate_bound input s hs _ _

theorem generalBimatrixDictionaryCandidateDeterminant_value (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (entering : List Bool) :
    binarySignedValue (generalBimatrixDictionaryDeterminant ![input, membershipWord s, entering]) =
      (generalBimatrixCandidateMatrix input s hs).det := by
  obtain ⟨hw, hl, hb⟩ := generalBimatrixDictionaryCandidateMatrix_hypotheses input s hs entering
  have hd := binaryBirdDeterminant_value (generalBimatrixDimensionWord input)
    (generalBimatrixDictionaryWidth ![input, membershipWord s, entering])
    (generalBimatrixDictionaryMatrix ![input, membershipWord s, entering])
    (generalCoefficientBits input + 2) hw hl hb
  have hm : (fun i j : Fin (generalRowCount input + generalColCount input) =>
      binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membershipWord s, entering])
        (generalBimatrixDictionaryMatrix ![input, membershipWord s, entering])
        (i.val * (generalRowCount input + generalColCount input) + j.val)) = generalBimatrixCandidateMatrix input s hs := by
    funext i j
    exact generalBimatrixDictionaryCandidateMatrix_integer input s hs entering i j
  have he : (binaryBirdMatrix (generalBimatrixDimensionWord input)
      (generalBimatrixDictionaryWidth ![input, membershipWord s, entering])
      (generalBimatrixDictionaryMatrix ![input, membershipWord s, entering])).det = (generalBimatrixCandidateMatrix input s hs).det := by
    unfold binaryBirdMatrix
    generalize hdim : (generalBimatrixDimensionWord input).length = size
    have hsize : size = generalRowCount input + generalColCount input := hdim.symm.trans (generalBimatrixDimensionWord_length input)
    clear hdim
    subst size
    exact congrArg Matrix.det hm
  exact hd.trans he
end GameTheory.Complexity.Backend


namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionaryCandidateCoefficients_value (input : List Bool)
    (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (entering : List Bool)
    (i : Fin (generalRowCount input + generalColCount input))
    (k : Fin (generalRowCount input + generalColCount input + 1)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membershipWord s, entering])
      (generalBimatrixDictionaryCoefficients ![input, membershipWord s, entering])
      (i.val * (generalRowCount input + generalColCount input + 1) + k.val) =
      GameTheory.Math.IntegerDictionaryComputation.coefficients (generalBimatrixCandidateMatrix input s hs)
        (fun _ => 1) i k := by
  let d := generalBimatrixDimensionWord input
  let W := generalBimatrixDictionaryWidth ![input, membershipWord s, entering]
  let P := generalBimatrixDictionaryMatrix ![input, membershipWord s, entering]
  let C := generalBimatrixDictionaryCoefficients ![input, membershipWord s, entering]
  obtain ⟨hw, hl, hb⟩ := generalBimatrixDictionaryCandidateMatrix_hypotheses input s hs entering
  have hg : ∀ (r : Fin d.length) (a : Fin (d.length + 1)),
      binarySignedRowValue W C (r.val * (d.length + 1) + a.val) =
      GameTheory.Math.IntegerDictionaryComputation.coefficients (binaryBirdMatrix d W P) (fun _ => 1) r a := by
    intro r a
    exact binaryDictionaryCoefficients_value d W P (generalCoefficientBits input + 2) hw hl hb r a
  have hm : (fun r c : Fin (generalRowCount input + generalColCount input) =>
      binarySignedRowValue W P (r.val * (generalRowCount input + generalColCount input) + c.val)) =
      generalBimatrixCandidateMatrix input s hs := by
    funext r c
    exact generalBimatrixDictionaryCandidateMatrix_integer input s hs entering r c
  unfold binaryBirdMatrix at hg
  generalize hdim : d.length = size at hg
  have hsize : size = generalRowCount input + generalColCount input :=
    hdim.symm.trans (generalBimatrixDimensionWord_length input)
  clear hdim
  subst size
  rw [hm] at hg
  exact hg i k

theorem generalBimatrixDictionaryDeterminant_value (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool) :
    binarySignedValue (generalBimatrixDictionaryDeterminant ![input, membershipWord basis.basic, entering]) =
      basis.integerMatrix.det :=
  generalBimatrixDictionaryCandidateDeterminant_value input basis.basic basis.cardinality entering

theorem generalBimatrixDictionaryCoefficients_value (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (i : Fin (generalRowCount input + generalColCount input))
    (k : Fin (generalRowCount input + generalColCount input + 1)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membershipWord basis.basic, entering])
      (generalBimatrixDictionaryCoefficients ![input, membershipWord basis.basic, entering])
      (i.val * (generalRowCount input + generalColCount input + 1) + k.val) =
      GameTheory.Math.IntegerDictionaryComputation.coefficients basis.integerMatrix (fun _ => 1) i k :=
  generalBimatrixDictionaryCandidateCoefficients_value input basis.basic basis.cardinality entering i k
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

private theorem dictionaryColumn_bound (v : Fin 4 → List Bool) :
    (binarySignedValue (generalBimatrixColumnWord v)).natAbs ≤ 2 ^ (generalCoefficientBits (v 3) + 2) := by
  rw [generalBimatrixColumnWord_value]
  split
  · split
    · split
      · exact Nat.zero_le _
      · exact shifted_bound _ true _ _
    · split
      · exact shifted_bound _ false _ _
      · exact Nat.zero_le _
  · split
    · exact Nat.one_le_pow _ 2 (by decide)
    · exact Nat.zero_le _

theorem generalBimatrixDictionaryColumn_value (v : Fin 3 → List Bool) (i : ℕ)
    (hi : i < generalRowCount (v 0) + generalColCount (v 0)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth v) (generalBimatrixDictionaryColumn v) i =
      binarySignedValue (generalBimatrixColumnWord
        ![List.replicate i true, binaryHalfRuler (v 2), binaryLengthParity (v 2), v 0]) := by
  let W := generalBimatrixDictionaryWidth v
  let f := fun k => binarySignedValue (generalBimatrixColumnWord
    ![List.replicate k true, binaryHalfRuler (v 2), binaryLengthParity (v 2), v 0])
  have hw := generalBimatrixDictionaryWidth_length v
  have hr : 0 < W.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  have hc : 2 ^ (generalCoefficientBits (v 0) + 2) < 2 ^ (W.length - 1) := by
    apply Nat.pow_lt_pow_right (by decide)
    rw [hw]
    unfold GameTheory.Math.BirdIterationBounds.workWidth
    omega
  have ht : ∀ r : List Bool, binarySignedValue (dictionaryColumnTerm (Fin.cons r v)) = f r.length := by
    intro r
    change binarySignedValue (generalBimatrixColumnWord ![r, binaryHalfRuler (v 2), binaryLengthParity (v 2), v 0]) = _
    dsimp only [f]
    simp only [generalBimatrixColumnWord_value, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, List.length_replicate]
    rfl
  have hb : ∀ k < (generalBimatrixDictionaryDimension v).length, (f k).natAbs < 2 ^ (W.length - 1) := by
    intro k hk
    exact (dictionaryColumn_bound ![List.replicate k true, binaryHalfRuler (v 2), binaryLengthParity (v 2), v 0]).trans_lt hc
  exact binarySignedTable_value dictionaryColumnTerm W v f ht hr
    (generalBimatrixDictionaryDimension v) hb i (by simpa [generalBimatrixDictionaryDimension] using hi)
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionaryColumn_integer (input membership entering : List Bool)
    (v : BimatrixVariable (generalRowCount input) (generalColCount input))
    (he : entering.length = (index v).val)
    (i : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membership, entering])
      (generalBimatrixDictionaryColumn ![input, membership, entering]) i.val =
      bimatrixIntegerColumns
        (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) i v := by
  have hh : binaryHalfRuler entering = List.replicate (ofLex v).1.val true := by
    rw [binaryHalfRuler_value, he]
    congr 1
    cases hb : (ofLex v).2 <;> simp [index, hb, Nat.add_div]
  have hp : binaryLengthParity entering = [(ofLex v).2] := by
    rw [binaryLengthParity_value, he]
    cases hb : (ofLex v).2 <;> simp [index, hb, Nat.add_mod]
  have hd := generalBimatrixDictionaryColumn_value ![input, membership, entering] i.val i.isLt
  change binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membership, entering])
      (generalBimatrixDictionaryColumn ![input, membership, entering]) i.val =
      binarySignedValue (generalBimatrixColumnWord
        ![List.replicate i.val true, binaryHalfRuler entering, binaryLengthParity entering, input]) at hd
  rw [hh, hp, generalBimatrixColumnWord_integer] at hd
  simpa only [Prod.mk.eta, toLex_ofLex] using hd
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionaryDirection_value (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (v : BimatrixVariable (generalRowCount input) (generalColCount input))
    (he : entering.length = (index v).val) (i : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue (generalBimatrixDictionaryWidth ![input, membershipWord basis.basic, entering])
      (generalBimatrixDictionaryDirection ![input, membershipWord basis.basic, entering]) i.val =
      GameTheory.Math.IntegerDictionaryComputation.direction basis.integerMatrix
        (fun j => bimatrixIntegerColumns
          (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
          (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v) i := by
  let d := generalBimatrixDimensionWord input
  let W := generalBimatrixDictionaryWidth ![input, membershipWord basis.basic, entering]
  let P := generalBimatrixDictionaryMatrix ![input, membershipWord basis.basic, entering]
  let c := generalBimatrixDictionaryColumn ![input, membershipWord basis.basic, entering]
  let D := generalBimatrixDictionaryDirection ![input, membershipWord basis.basic, entering]
  obtain ⟨hw, hl, hb⟩ := generalBimatrixDictionaryCandidateMatrix_hypotheses input basis.basic basis.cardinality entering
  have hc : ∀ j : Fin d.length, (binarySignedRowValue W c j.val).natAbs ≤ 2 ^ (generalCoefficientBits input + 2) := by
    intro j
    have hj : j.val < generalRowCount input + generalColCount input := by
      have ht := j.isLt
      change j.val < (generalBimatrixDimensionWord input).length at ht
      simpa only [generalBimatrixDimensionWord_length] using ht
    have hd := generalBimatrixDictionaryColumn_value ![input, membershipWord basis.basic, entering] j.val hj
    change binarySignedRowValue W c j.val = binarySignedValue (generalBimatrixColumnWord
      ![List.replicate j.val true, binaryHalfRuler entering, binaryLengthParity entering, input]) at hd
    rw [hd]
    exact dictionaryColumn_bound _
  have hg : ∀ j : Fin d.length, binarySignedRowValue W D j.val =
      GameTheory.Math.IntegerDictionaryComputation.direction (binaryBirdMatrix d W P)
        (fun a => binarySignedRowValue W c a.val) j := by
    intro j
    exact binaryDictionaryDirection_value d W P c (generalCoefficientBits input + 2) hw hl hb hc j
  have hm : (fun r a : Fin (generalRowCount input + generalColCount input) =>
      binarySignedRowValue W P (r.val * (generalRowCount input + generalColCount input) + a.val)) =
      basis.integerMatrix := by
    funext r a
    exact generalBimatrixDictionaryCandidateMatrix_integer input basis.basic basis.cardinality entering r a
  have hv : (fun j : Fin (generalRowCount input + generalColCount input) => binarySignedRowValue W c j.val) =
      (fun j => bimatrixIntegerColumns
        (fun r a => decodeGeneralPayoff false input r.val a.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun r a => decodeGeneralPayoff true input r.val a.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v) := by
    funext j
    exact generalBimatrixDictionaryColumn_integer input (membershipWord basis.basic) entering v he j
  unfold binaryBirdMatrix at hg
  generalize hdim : d.length = size at hg
  have hsize : size = generalRowCount input + generalColCount input := hdim.symm.trans (generalBimatrixDimensionWord_length input)
  clear hdim
  subst size
  rw [hm, hv] at hg
  exact hg i
end GameTheory.Complexity.Backend


namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixDictionarySelectedRow_integer_spec (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (v : BimatrixVariable (generalRowCount input) (generalColCount input))
    (he : entering.length = (index v).val) (l : Fin (generalRowCount input + generalColCount input))
    (hs : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow
      ![input, membershipWord basis.basic, entering]) = some l.val) :
    GameTheory.Math.IsLeavingRow
      (fun i k => (GameTheory.Math.IntegerDictionaryComputation.coefficients basis.integerMatrix (fun _ => 1) i k : ℚ))
      (fun i => (GameTheory.Math.IntegerDictionaryComputation.direction basis.integerMatrix
        (fun j => bimatrixIntegerColumns
          (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
          (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v) i : ℚ)) l := by
  let d := generalBimatrixDimensionWord input
  let W := generalBimatrixDictionaryWidth ![input, membershipWord basis.basic, entering]
  let C := generalBimatrixDictionaryCoefficients ![input, membershipWord basis.basic, entering]
  let D := generalBimatrixDictionaryDirection ![input, membershipWord basis.basic, entering]
  have hl : l.val < d.length := by rw [generalBimatrixDimensionWord_length]; exact l.isLt
  have hh := binarySignedRowSelect_some_spec ![d, true :: d, W, C, D] ⟨l.val, hl⟩ hs
  change GameTheory.Math.IsLeavingRow
    (fun i : Fin d.length => fun k : Fin (d.length + 1) => (binarySignedMatrixValue (true :: d) W C i.val k.val : ℚ))
    (fun i => (binarySignedRowValue W D i.val : ℚ)) ⟨l.val, hl⟩ at hh
  have hcount : (true :: d).length = generalRowCount input + generalColCount input + 1 := by
    rw [List.length_cons, generalBimatrixDimensionWord_length]
  have hC : (fun i : Fin (generalRowCount input + generalColCount input) =>
      fun k : Fin (generalRowCount input + generalColCount input + 1) =>
        (binarySignedMatrixValue (true :: d) W C i.val k.val : ℚ)) =
      (fun i k => (GameTheory.Math.IntegerDictionaryComputation.coefficients basis.integerMatrix (fun _ => 1) i k : ℚ)) := by
    funext i k
    rw [binarySignedMatrixValue_eq_flat (true :: d) W C i.val k.val (by rw [hcount]; exact k.isLt), hcount]
    exact congrArg (fun z : ℤ => (z : ℚ)) (generalBimatrixDictionaryCoefficients_value input basis entering i k)
  have hD : (fun i : Fin (generalRowCount input + generalColCount input) => (binarySignedRowValue W D i.val : ℚ)) =
      (fun i => (GameTheory.Math.IntegerDictionaryComputation.direction basis.integerMatrix
        (fun j => bimatrixIntegerColumns
          (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
          (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v) i : ℚ)) := by
    funext i
    exact congrArg (fun z : ℤ => (z : ℚ)) (generalBimatrixDictionaryDirection_value input basis entering v he i)
  generalize hdim : d.length = size at hl hh
  have hsize : size = generalRowCount input + generalColCount input := hdim.symm.trans (generalBimatrixDimensionWord_length input)
  clear hdim
  subst size
  rw [hC, hD] at hh
  exact hh
end GameTheory.Complexity.Backend


namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open GameTheory.Math

set_option backward.isDefEq.respectTransparency false in
theorem generalBimatrixDictionarySelectedRow_spec (input : List Bool)
    (basis : GeneralBimatrixShiftedBasis input) (entering : List Bool)
    (v : BimatrixVariable (generalRowCount input) (generalColCount input))
    (he : entering.length = (index v).val) (l : Fin (generalRowCount input + generalColCount input))
    (hs : binarySignedRowSelectedIndex (generalBimatrixDictionarySelectedRow
      ![input, membershipWord basis.basic, entering]) = some l.val) :
    IsLeavingRow
      (PerturbedDictionary.dictionaryCoefficients (basis.integerMatrix.map (fun z : ℤ => (z : ℚ))) (fun _ => 1))
      ((basis.integerMatrix.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
        (fun j => (bimatrixIntegerColumns
          (fun r c => decodeGeneralPayoff false input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
          (fun r c => decodeGeneralPayoff true input r.val c.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v : ℚ))) l := by
  let M := basis.integerMatrix
  let c := fun j => bimatrixIntegerColumns
    (fun r a => decodeGeneralPayoff false input r.val a.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (fun r a => decodeGeneralPayoff true input r.val a.val + ((2 : ℤ) ^ generalCoefficientBits input + 1)) j v
  have hh := generalBimatrixDictionarySelectedRow_integer_spec input basis entering v he l hs
  change IsLeavingRow (fun i k => (IntegerDictionaryComputation.coefficients M (fun _ => 1) i k : ℚ))
    (fun i => (IntegerDictionaryComputation.direction M c i : ℚ)) l at hh
  have hdet : M.det ≠ 0 := basis.integerMatrix_det_ne_zero
  have hd : (0 : ℚ) < (IntegerCramerComputation.denominator M : ℚ) := by
    rw [IntegerCramerComputation.denominator_eq]
    exact_mod_cast IntegerCramerEncoding.denominator_pos M hdet
  refine ⟨?_, ?_⟩
  · rw [← IntegerDictionaryComputation.direction_decode M c hdet l]
    exact div_pos hh.1 hd
  · intro i hi
    rw [← IntegerDictionaryComputation.direction_decode M c hdet i] at hi
    have hp : (0 : ℚ) < (IntegerDictionaryComputation.direction M c i : ℚ) := (div_pos_iff_of_pos_right hd).mp hi
    have hratio := hh.2 i hp
    have hc (j : Fin (generalRowCount input + generalColCount input)) (k : Fin (generalRowCount input + generalColCount input + 1)) :
        PerturbedDictionary.dictionaryCoefficients (M.map (fun z : ℤ => (z : ℚ))) (fun _ => 1) j k /
          (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun a => (c a : ℚ)) j =
        (IntegerDictionaryComputation.coefficients M (fun _ => 1) j k : ℚ) /
          (IntegerDictionaryComputation.direction M c j : ℚ) := by
      have hcoeff := IntegerDictionaryComputation.coefficients_decode M (fun _ => 1) hdet j k
      simp only [Int.cast_one] at hcoeff
      rw [← hcoeff, ← IntegerDictionaryComputation.direction_decode M c hdet j]
      exact div_div_div_cancel_right₀ hd.ne' _ _
    change (toLex fun k => PerturbedDictionary.dictionaryCoefficients (M.map (fun z : ℤ => (z : ℚ))) (fun _ => 1) l k / (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun a => (c a : ℚ)) l) ≤ (toLex fun k => PerturbedDictionary.dictionaryCoefficients (M.map (fun z : ℤ => (z : ℚ))) (fun _ => 1) i k / (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun a => (c a : ℚ)) i)
    simpa only [hc] using hratio
end GameTheory.Complexity.Backend
