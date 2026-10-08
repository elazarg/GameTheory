import GameTheoryComplexity.PPAD
import GameTheoryComplexity.Tests.RawEndOfLine

/-! Controls for coordinate order, scalar queries, normalized isolated vertices,
and the certified reduction's public classification. -/

namespace GameTheory.Complexity.Tests.NormalizedEndOfLine

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Complexity GameTheory.Complexity.Backend
open GameTheory.Complexity.Tests.EndOfLine

example : circuitVectorCodeAt
    (emitCircuitVector pairSnd [false] 3) 0 = [] := by decide

example : circuitVectorCodeAt
    (emitCircuitVector pairSnd [false] 3) 2 = [true, true] := by decide

example : emitCircuitVector pairSnd [false] 0 = [] := rfl

example : pointerBitQuery endOfLineNormalizedSuccessor
    (pair (pair oneBitPath []) [false]) = true := by
  change pointerBitQuery _ (pair (pair oneBitPath (List.replicate 0 true)) [false]) = true
  rw [pointerBitQuery_pair]
  decide

example : pointerBitQuery endOfLineNormalizedSuccessor
    (pair (pair oneBitPath [true]) [false]) = false := by
  change pointerBitQuery _ (pair (pair oneBitPath (List.replicate 1 true)) [false]) = false
  rw [pointerBitQuery_pair]
  decide

example : endOfLineNormalizedPredecessor twoBitPath [false, true] = [false, true] ∧
    endOfLineNormalizedSuccessor twoBitPath [false, true] = [false, true] := by decide

example : ¬GameTheory.Math.EndOfLine.RawWitness
    (endOfLineNormalizedPredecessor twoBitPath) (endOfLineNormalizedSuccessor twoBitPath)
    (endOfLineOrigin twoBitPath) [false, true] := by
  unfold GameTheory.Math.EndOfLine.RawWitness
  decide

example : PPADComplete endOfLineRelation := endOfLineRelation_PPADComplete

/-- The compiled reduction preserves every raw answer, including fallback cases. -/
example : ∃ a : SearchReduction endOfLineRelation rawEndOfLineRelation,
    ∀ input witness, rawEndOfLineRelation (a.instanceMap input) witness →
      endOfLineRelation input (a.decode ![input, witness]) := by
  obtain ⟨a⟩ := endOfLineRelation_mem_PPAD.2
  exact ⟨a, a.sound⟩

end GameTheory.Complexity.Tests.NormalizedEndOfLine
