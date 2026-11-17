module

public import GameTheoryComplexity.Backend.BimatrixRawGateMachine

@[expose] public section

/-! Executable coefficient controls retain repeated references and inline negations. -/
namespace GameTheory.Complexity.Tests.BimatrixRawGateMachine
open Backend

private def aliased (op neg : Bool) : List Bool :=
  CircuitFormat.encodeGate (op, false, neg) 0 0

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    [false, false] (aliased true false) [false]) = 5 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    [false, false] (aliased true false) []) = -3 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    [false, false] (aliased true true) [false]) = -1 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    [false, false] (aliased false true) [false]) = 1 := by decide +kernel

-- Truncated gates retain the documented defaults.
example : binarySignedValue (BimatrixRawGateMachine.coefficientWord
    [false, false] [] [false]) = 7 := by decide +kernel

example : binarySignedValue (BimatrixRawGateMachine.selectedCoefficientWord
    [false, false] [] [false] []) = -1 := by decide +kernel

-- Relocated aliases retain their copied-coordinate offset.
example : binarySignedValue (BimatrixRawGateMachine.shiftedCoefficientWord
    [false, false] (aliased true false) [false] [false, false, false]) = 5 := by decide +kernel
example : binarySignedValue (BimatrixRawGateMachine.shiftedCoefficientWord
    [false, false] (aliased true false) [false] [false]) = -3 := by decide +kernel

end GameTheory.Complexity.Tests.BimatrixRawGateMachine
