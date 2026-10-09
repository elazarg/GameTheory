import GameTheoryComplexity.Backend.GeneralBimatrixNodeValidation
namespace GameTheory.Complexity.Tests.GeneralBimatrixNodeValidation
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open _root_.Complexity _root_.Complexity.Cobham
private def input : List Bool := encodeGeneralInstance 1 1 2 (fun _ _ => -1) (fun _ _ => 2)
example : GeneralInstanceValid input := by decide +kernel
example : FPn generalBimatrixNodeValidFlag := generalBimatrixNodeValidFlag_mem_FPn
-- The all-zero source mask is valid for signed original payoffs after the positive shift.
example : generalBimatrixNodeValidFlag ![input, List.replicate 8 false] = [true] := by
  decide +kernel
-- The same valid serialized instance rejects an incorrectly sized node.
example : generalBimatrixNodeValidFlag ![input, [true, false]] = [false] := by decide +kernel
-- Properly sized masks that omit the entering port are rejected.
example : generalBimatrixNodeValidFlag ![input, List.replicate 8 true] = [false] := by decide +kernel
-- Empty instance input is rejected even on a node with the vacuous width.
example : generalBimatrixNodeValidFlag ![[], []] = [false] := by decide +kernel
-- The certified semantic port and executable acceptance agree without auxiliary feasibility premises.
example (instanceWord : List Bool) (hi : GeneralInstanceValid instanceWord)
    (d : Fin (generalRowCount instanceWord + generalColCount instanceWord)) (hd : d.val = 0)
    (port : GeneralBimatrixShiftedPort instanceWord d) :
    generalBimatrixNodeValidFlag ![instanceWord, encode port] = [true] :=
  generalBimatrixNodeValidFlag_encode instanceWord hi hd port
end GameTheory.Complexity.Tests.GeneralBimatrixNodeValidation
