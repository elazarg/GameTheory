import GameTheoryComplexity.Backend.GeneralBimatrixMatrixWord

/-! Packed canonical basis matrices use exact shifted entries and total lookups. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixMatrixWord
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool :=
  encodeGeneralInstance 1 1 2 (fun _ _ => -1) (fun _ _ => 2)
private def fieldWidth : List Bool := [true, true, true, true]
private def payoffColumns : List Bool := [false, true, false, true]
private def slackColumns : List Bool := [true, false, true, false]

-- The shift is five, so independently signed original entries become four and seven.
example : binarySignedValue (generalBimatrixBasisEntryWord
    ![[], [true], payoffColumns, input]) = 4 := by decide +kernel

example : binarySignedValue (generalBimatrixBasisEntryWord
    ![[true], [], payoffColumns, input]) = 7 := by decide +kernel

example : binarySignedRowValue fieldWidth
    (generalBimatrixBasisMatrixWord ![fieldWidth, payoffColumns, input]) 1 = 4 := by
  decide +kernel

example : binarySignedRowValue fieldWidth
    (generalBimatrixBasisMatrixWord ![fieldWidth, payoffColumns, input]) 2 = 7 := by
  decide +kernel

example : binarySignedRowValue fieldWidth
    (generalBimatrixBasisMatrixWord ![fieldWidth, slackColumns, input]) 0 = 1 := by
  decide +kernel

-- Missing ordinals have zero entries, and the full table keeps its promised length.
example : generalBimatrixBasisMatrixWord ![fieldWidth, [], input] = List.replicate 16 false := by
  decide +kernel

example : (generalBimatrixBasisMatrixWord ![fieldWidth, payoffColumns, input]).length = 16 := by
  decide +kernel

example : FPn generalBimatrixBasisMatrixWord := generalBimatrixBasisMatrixWord_mem_FPn

-- Every certified basis has these exact row-major fields, conditional only on
-- supplying sufficient fixed-width magnitude capacity.
example (basis : GeneralBimatrixShiftedBasis input) (w : List Bool)
    (hw : 0 < w.length)
    (hb : ∀ r c, (basis.integerMatrix r c).natAbs < 2 ^ (w.length - 1))
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue w (generalBimatrixBasisMatrixWord ![w, membershipWord basis.basic, input])
      (i.val * (generalRowCount input + generalColCount input) + j.val) = basis.integerMatrix i j :=
  generalBimatrixBasisMatrixWord_integer input basis w hw hb i j

-- A singular selection is still assembled exactly; validation may reject it later.
example : binarySignedRowValue fieldWidth
    (generalBimatrixBasisMatrixWord ![fieldWidth, [true, false, false, true], input]) 1 = 4 := by
  decide +kernel

example : binarySignedRowValue fieldWidth
    (generalBimatrixBasisMatrixWord ![fieldWidth, [true, false, false, true], input]) 3 = 0 := by
  decide +kernel

example (s : Finset (BimatrixVariable (generalRowCount input) (generalColCount input)))
    (hs : s.card = generalRowCount input + generalColCount input) (w : List Bool)
    (hw : 0 < w.length)
    (hb : ∀ r c, (generalBimatrixCandidateMatrix input s hs r c).natAbs < 2 ^ (w.length - 1))
    (i j : Fin (generalRowCount input + generalColCount input)) :
    binarySignedRowValue w (generalBimatrixBasisMatrixWord ![w, membershipWord s, input])
      (i.val * (generalRowCount input + generalColCount input) + j.val) =
      generalBimatrixCandidateMatrix input s hs i j :=
  generalBimatrixCandidateMatrixWord_integer input s hs w hw hb i j

end GameTheory.Complexity.Tests.GeneralBimatrixMatrixWord
