import GameTheoryComplexity.Backend.CircuitPrefixCompiler

/-! Shared-gate and malformed-input controls for serialized prefix compilation. -/

namespace GameTheory.Complexity.Tests.CircuitPrefixCompiler

open Backend _root_.Complexity _root_.Complexity.CircuitCode

/-- A shared gate feeds both branches of a diamond-shaped circuit. -/
def sharedDiamond : RawCircuit :=
  [⟨.and, 0, 1, false, false⟩, ⟨.or, 3, 2, false, false⟩, ⟨.and, 3, 4, true, false⟩]

/-- The fixture has three inputs and shares its first gate's output. -/
theorem sharedDiamond_wellFormed : sharedDiamond.WellFormed 3 := by decide

/-- Hardwiring the first input leaves the function `!a && b`. -/
theorem sharedDiamond_truthTable :
    (List.map (fun input => evalCode 2
      (restrictCircuitCode [false, true] [true] sharedDiamond.encode) input)
      [[false, false], [false, true], [true, false], [true, true]]) =
        [some false, some true, some false, some false] := by decide

/-- Forward references are preserved as failures rather than repaired. -/
theorem forward_reference_rejected :
    evalCode 2 (restrictCircuitCode [true, true] [true]
      (RawCircuit.encode [RawGate.copy 3])) [false, true] = none := by decide

/-- Prefix gates cannot become the output of an originally empty circuit. -/
theorem empty_circuit_rejected :
    restrictCircuitCode [true, true] [true] (RawCircuit.encode []) = [] := by decide

/-- A zero-width target cannot anchor the constant gates. -/
theorem zero_width_rejected :
    restrictCircuitCode [] [true] sharedDiamond.encode = [] := by decide

/-- Trailing garbage, truncated gates and unterminated unary fields are rejected. -/
theorem malformed_codes_rejected :
    (List.map (restrictCircuitCode [true, true] [false])
      [sharedDiamond.encode ++ [false], sharedDiamond.encode.take 7,
        [true, true], [true, false, true, false, false], []]) =
      [[], [], [], [], []] := by decide

/-- Syntax validation accepts an empty circuit; the compiler's output guard is separate. -/
theorem empty_syntax_accepted : circuitCodeSyntaxFlag (RawCircuit.encode []) = [true] := by
  decide

/-- Incorrect target input width remains an evaluation failure. -/
theorem input_width_rejected :
    evalCode 2 (restrictCircuitCode [true, true] [true] sharedDiamond.encode) [false] =
      none := by decide

end GameTheory.Complexity.Tests.CircuitPrefixCompiler
