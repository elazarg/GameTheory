import GameTheoryComplexity.Backend.GeneralBimatrixEndpointMachine

namespace GameTheory.Complexity.Tests.GeneralBimatrixEndpointMachine
open Backend _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool :=
  encodeGeneralInstance 1 1 2 (fun _ _ => -1) (fun _ _ => 2)
private def width : List Bool := List.replicate 8 false
private def members : List Bool := [false, true, false, true]
private def signed (z : ℤ) : List Bool :=
  [decide (z < 0)] ++ Nat.toBitsLE 7 z.natAbs
private def coefficients : List Bool :=
  signed 4 ++ signed 0 ++ signed 4 ++ signed 7 ++ signed 7 ++ signed 0
private def fields : Fin 5 → List Bool := ![input, members, signed (-28), coefficients, width]

example : binarySignedValue (generalBimatrixEndpointWeightWord
    ![[], input, members, signed (-28), coefficients, width]) = 4 := by decide +kernel

example : binarySignedValue (generalBimatrixEndpointWeightWord
    ![[false], input, members, signed (-28), coefficients, width]) = 7 := by decide +kernel

example : binarySignedValue (generalBimatrixEndpointMassWord false fields) = 4 := by decide +kernel
example : binarySignedValue (generalBimatrixEndpointMassWord true fields) = 7 := by decide +kernel
example : binarySignedValue (generalBimatrixEndpointUtilityWord false fields) = -7 := by decide +kernel
example : binarySignedValue (generalBimatrixEndpointUtilityWord true fields) = 8 := by decide +kernel

-- A negative constant numerator is clamped to zero, even for a selected variable.
example : binarySignedValue (generalBimatrixEndpointWeightWord
    ![[], input, members, signed 1, signed (-3), width]) = 0 := by decide +kernel

example : binarySignedValue (generalBimatrixEndpointWeightWord
    ![[], input, [], signed 1, coefficients, width]) = 0 := by decide +kernel

example : FPn generalBimatrixEndpointMachineWord := generalBimatrixEndpointMachineWord_mem_FPn

example (v : Fin 5 → List Bool) :
    (generalBimatrixEndpointMachineWord v).length =
      (6 + generalRowCount (v 0) + generalColCount (v 0)) *
        generalCertificateWidth (v 0).length := generalBimatrixEndpointMachineWord_length v

end GameTheory.Complexity.Tests.GeneralBimatrixEndpointMachine
