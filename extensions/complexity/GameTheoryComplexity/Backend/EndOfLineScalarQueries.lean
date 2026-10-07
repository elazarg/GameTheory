import GameTheoryComplexity.Backend.EndOfLinePointerNormalization
import Complexitylib.Classes.P.Cobham.Internal.Extract

/-! Scalar queries for normalized End-of-Line pointers. The instance and unary
output index occupy the fixed prefix; the vertex remains the circuit input. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Query one output bit of a word-valued pointer. -/
def pointerBitQuery (pointer : List Bool → List Bool → List Bool)
    (word : List Bool) : Bool :=
  bitOf (pointer (pairFst (pairFst word)) (pairSnd word))
    (pairSnd (pairFst word)).length

/-- A polynomial-time pointer evaluator gives polynomial-time scalar queries. -/
theorem pointerBitQuery_mem_FP
    {pointer : List Bool → List Bool → List Bool}
    (hp : ∀ {input vertex : List Bool → List Bool}, input ∈ FP → vertex ∈ FP →
      (fun z => pointer (input z) (vertex z)) ∈ FP) :
    (fun z => [pointerBitQuery pointer z]) ∈ FP := by
  have hi := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := Cobham.comp₂ Cobham.bitAtFn (FP_subset_CobhamFP hr)
    (FP_subset_CobhamFP (hp hi pairSnd_mem_FP))
  exact CobhamFP_subset_FP (h.of_eq fun z => by
    simp [bitAt_eq, pointerBitQuery])

/-- Scalar queries to the consistent incoming pointer are polynomial-time. -/
theorem normalizedPredecessorBit_mem_FP :
    (fun z => [pointerBitQuery endOfLineNormalizedPredecessor z]) ∈ FP :=
  pointerBitQuery_mem_FP normalizedPredecessorFn_mem_FP

/-- Scalar queries to the consistent outgoing pointer are polynomial-time. -/
theorem normalizedSuccessorBit_mem_FP :
    (fun z => [pointerBitQuery endOfLineNormalizedSuccessor z]) ∈ FP :=
  pointerBitQuery_mem_FP normalizedSuccessorFn_mem_FP

/-- Canonical framing recovers the requested pointer output coordinate. -/
@[simp] theorem pointerBitQuery_pair (pointer : List Bool → List Bool → List Bool)
    (input vertex : List Bool) (i : ℕ) :
    pointerBitQuery pointer (pair (pair input (List.replicate i true)) vertex) =
      bitOf (pointer input vertex) i := by
  simp [pointerBitQuery]

end GameTheory.Complexity.Backend
