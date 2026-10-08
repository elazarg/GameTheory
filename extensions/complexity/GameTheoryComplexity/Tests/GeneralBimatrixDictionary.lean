import GameTheoryComplexity.Backend.GeneralBimatrixDictionary

/-! Serialized dictionary controls with signed input and unchecked candidate bases. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixDictionary
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool := encodeGeneralInstance 1 1 2 (fun _ _ => -1) (fun _ _ => 2)
private def selected : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)) :=
  Finset.univ.filter fun v => (ofLex v).2
private theorem selected_card : selected.card = generalRowCount input + generalColCount input := by decide +kernel
private def words : Fin 3 → List Bool := ![input, membershipWord selected, []]

private theorem matrix_eq : generalBimatrixCandidateMatrix input selected selected_card =
    (!![0, 4; 7, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  have he := generalBimatrixDictionaryCandidateMatrix_integer input selected selected_card [] i j
  refine he.symm.trans ?_
  fin_cases i <;> fin_cases j <;> decide +kernel
-- Working width is derived from the serialized coefficient ruler, not chosen by the caller.
example : (generalBimatrixDictionaryWidth words).length = 64 := by decide +kernel

example : binarySignedValue (generalBimatrixDictionaryDeterminant words) = -28 := by
  have he := generalBimatrixDictionaryCandidateDeterminant_value input selected selected_card []
  refine he.trans ?_
  exact (congrArg Matrix.det matrix_eq).trans (Matrix.det_fin_two_of 0 4 7 0)

example (i : Fin 2) (k : Fin 3) :
    binarySignedRowValue (generalBimatrixDictionaryWidth words)
      (generalBimatrixDictionaryCoefficients words) (i.val * 3 + k.val) =
      (!![4, 0, 4; 7, 7, 0] : Matrix (Fin 2) (Fin 3) ℤ) i k := by
  have he := generalBimatrixDictionaryCandidateCoefficients_value input selected selected_card [] i k
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => GameTheory.Math.IntegerDictionaryComputation.coefficients M (fun _ => 1) i k) matrix_eq
  refine (he.trans hc).trans ?_
  fin_cases i <;> fin_cases k <;> decide +kernel

-- Empty membership assembles a zero matrix and remains a total computation.
example : binarySignedRowValue (generalBimatrixDictionaryWidth ![input, [], []])
    (generalBimatrixDictionaryMatrix ![input, [], []]) 0 = 0 := by decide +kernel

example : FPn generalBimatrixDictionarySelectedRow := generalBimatrixDictionarySelectedRow_mem_FPn

end GameTheory.Complexity.Tests.GeneralBimatrixDictionary
