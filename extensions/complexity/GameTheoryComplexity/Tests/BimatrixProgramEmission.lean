import GameTheoryComplexity.Backend.BimatrixProgramEmission

/-! Packed signed fields preserve aliases, signs and empty dimensions. -/
namespace GameTheory.Complexity.Tests.BimatrixProgramEmission

open GameTheory.Complexity.Backend.BimatrixProgramEmission

example : coefficients (fun _ => [true, true])
    ![[false, true], [true, true, true, true], []] =
      (List.replicate 8 [true, true, false, false]).flatten := by decide +kernel

example : coefficients (fun _ => [true, false])
    ![[true], [false, false, false], []] =
      [true, false, false, true, false, false] := by decide +kernel

example : coefficients (fun _ => [true, true]) ![[], [true], []] = [] := by decide +kernel

example : coefficients (fun _ => [true, true]) ![[true, true], [], []] = [] := by decide +kernel
end GameTheory.Complexity.Tests.BimatrixProgramEmission
