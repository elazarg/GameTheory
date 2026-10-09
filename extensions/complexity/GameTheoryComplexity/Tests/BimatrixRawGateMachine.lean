import GameTheoryComplexity.Backend.BimatrixRawGateMachine

/-! Executable coefficient controls retain repeated references and inline negations. -/
namespace GameTheory.Complexity.Tests.BimatrixRawGateMachine
open Backend _root_.Complexity.CircuitCode

private def aliased (op : _root_.Complexity.AndOrOp) (neg : Bool) : RawGate :=
  ⟨op, 0, 0, false, neg⟩

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![[false, false], (aliased .and false).encode, [false]]) = 5 := by
  decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![[false, false], (aliased .and false).encode, []]) = -3 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![[false, false], (aliased .and true).encode, [false]]) = -1 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![[false, false], (aliased .or true).encode, [false]]) = 1 := by decide +kernel

-- Truncated gates have explicit defaults, rather than a rejection or zero-output convention.
example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    ![[false, false], [], [false]]) = 7 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.selectedCoefficientWord
    ![[false, false], [], [false], []]) = -1 := by decide +kernel

end GameTheory.Complexity.Tests.BimatrixRawGateMachine
