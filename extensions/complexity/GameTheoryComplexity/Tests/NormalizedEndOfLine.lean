module

public import GameTheoryComplexity.PPAD
public import GameTheoryComplexity.Backend.EndOfLineScalarQueries
public import GameTheoryComplexity.Tests.RawEndOfLine

@[expose] public section

/-! Controls for coordinate order, scalar queries, normalized isolated vertices,
and the certified reduction's public classification. -/

namespace GameTheory.Complexity.Tests.NormalizedEndOfLine

open Turing.MultiTapeTM
open Cslib.Complexity
open GameTheory.Complexity GameTheory.Complexity.Backend
open GameTheory.Complexity.Tests.EndOfLine

example : circuitVectorCodeAt
    (emitCircuitVector (fun _ i => List.replicate i true) [false] 3) 0 = [] := by decide

example : circuitVectorCodeAt
    (emitCircuitVector (fun _ i => List.replicate i true) [false] 3) 2 = [true, true] := by decide

example : emitCircuitVector (fun _ i => List.replicate i true) [false] 0 = [] := rfl

example : pointerBitQuery endOfLineNormalizedSuccessor
    (CircuitWords.encodePair (CircuitWords.encodePair oneBitPath []) [false]) = true := by
  change pointerBitQuery _ (CircuitWords.encodePair (CircuitWords.encodePair oneBitPath (List.replicate 0 true)) [false]) = true
  rw [pointerBitQuery_pair]
  decide

example : pointerBitQuery endOfLineNormalizedSuccessor
    (CircuitWords.encodePair (CircuitWords.encodePair oneBitPath [true]) [false]) = false := by
  change pointerBitQuery _ (CircuitWords.encodePair (CircuitWords.encodePair oneBitPath (List.replicate 1 true)) [false]) = false
  rw [pointerBitQuery_pair]
  decide

example : endOfLineNormalizedPredecessor twoBitPath [false, true] = [false, true] ∧
    endOfLineNormalizedSuccessor twoBitPath [false, true] = [false, true] := by decide

example : ¬GameTheory.Math.EndOfLine.RawWitness
    (endOfLineNormalizedPredecessor twoBitPath) (endOfLineNormalizedSuccessor twoBitPath)
    (endOfLineOrigin twoBitPath) [false, true] := by
  unfold GameTheory.Math.EndOfLine.RawWitness
  decide

example : SearchComplete @Cslib.Complexity.PPAD encBits endOfLineRelation := endOfLineRelation_PPADComplete

/-- Native completeness supplies an efficient reduction preserving every raw answer. -/
example : SearchReducible encBits encBits endOfLineRelation rawEndOfLineRelation :=
  rawEndOfLineRelation_PPADHard encBits endOfLineRelation endOfLineRelation_mem_PPAD

end GameTheory.Complexity.Tests.NormalizedEndOfLine
