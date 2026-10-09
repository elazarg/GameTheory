import GameTheoryComplexity.Backend.BimatrixProgramMachine

/-! Entry controls distinguish affine and comparator feedback, including signed zero. -/
namespace GameTheory.Complexity.Tests.BimatrixProgramPayoffs
open Backend

private def program (comparator : Bool) (q : List Bool) : List Bool :=
  BimatrixProgramCodec.encode [false] [false, false, false]
    [false, false, true, false, true] [comparator] ([false, false, false] ++ q)

example : binarySignedValue (BimatrixProgramPayoffs.rowEntry
    ![[], [false], program true [false, true, false]]) = 12 := by decide +kernel

example : binarySignedValue (BimatrixProgramPayoffs.columnEntry
    ![[false], [], program true [false, true, false]]) = -7 := by decide +kernel

example : binarySignedValue (BimatrixProgramPayoffs.columnEntry
    ![[false], [false], program true [false, true, false]]) = -8 := by decide +kernel

example : binarySignedValue (BimatrixProgramPayoffs.columnEntry
    ![[false], [], program false [false, true, false]]) = -9 := by decide +kernel

example : binarySignedValue (BimatrixProgramPayoffs.columnEntry
    ![[false], [], program true [true, false, false]]) = -8 := by decide +kernel

example : binarySignedValue (BimatrixProgramPayoffs.rowEntry ![[], [], []]) = 0 ∧
    binarySignedValue (BimatrixProgramPayoffs.columnEntry ![[], [], []]) = 0 := by
  decide +kernel

example : GeneralInstanceValid
    (BimatrixProgramMachine.instanceWord (program true [false, true, false])) := by
  apply BimatrixProgramMachine.instanceWord_valid
  decide +kernel

example : decodeGeneralPayoff false
    (BimatrixProgramMachine.instanceWord (program true [false, true, false])) 0 1 = 12 := by
  decide +kernel

example : decodeGeneralPayoff true
    (BimatrixProgramMachine.instanceWord (program true [false, true, false])) 1 0 = -7 := by
  decide +kernel

example : ¬GeneralInstanceValid (BimatrixProgramMachine.instanceWord []) := by
  decide +kernel

end GameTheory.Complexity.Tests.BimatrixProgramPayoffs
