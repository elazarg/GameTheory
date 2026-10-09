import GameTheoryComplexity.Backend.BinaryUnaryArithmetic

namespace GameTheory.Complexity.Tests.BinaryUnaryArithmetic
open GameTheory.Complexity.Backend

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

example : _root_.Complexity.Cobham (fun v : Fin 1 → List Bool => binaryHalfRuler (v 0)) :=
  binaryHalfRuler_cobham
example : _root_.Complexity.Cobham.FPn (fun v : Fin 1 → List Bool => binaryLengthParity (v 0)) :=
  binaryLengthParity_mem_FPn

end GameTheory.Complexity.Tests.BinaryUnaryArithmetic
