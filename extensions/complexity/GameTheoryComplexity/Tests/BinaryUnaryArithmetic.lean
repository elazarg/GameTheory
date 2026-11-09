module

public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic

@[expose] public section

namespace GameTheory.Complexity.Tests.BinaryUnaryArithmetic
open GameTheory.Complexity.Backend Turing.MultiTapeTM

example : binaryHalfRuler [] = [] := by decide +kernel
example : binaryHalfRuler [false] = [] := by decide +kernel
example : binaryHalfRuler [false, false] = [true] := by decide +kernel
example : binaryHalfRuler [true, false, true] = [true] := by decide +kernel
example : binaryHalfRuler [false, true, false, true, true] = [true, true] := by decide +kernel
example : binaryHalfRuler [true, true, true, true, true, true] = [true, true, true] := by decide +kernel

example : binaryLengthParity [] = [false] := by decide +kernel
example : binaryLengthParity [false] = [true] := by decide +kernel
example : binaryLengthParity [false, false] = [false] := by decide +kernel
example : binaryLengthParity [false, false, false] = [true] := by decide +kernel
example : binaryLengthParity [true, true, true, true] = [false] := by decide +kernel

example : ComputableInPolyTime binaryHalfRuler encBits encBits :=
  binaryHalfRuler_polyTime
example : ComputableInPolyTime binaryLengthParity encBits encBits :=
  binaryLengthParity_polyTime

end GameTheory.Complexity.Tests.BinaryUnaryArithmetic
