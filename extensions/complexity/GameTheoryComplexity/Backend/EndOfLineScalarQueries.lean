module

public import GameTheoryComplexity.Backend.EndOfLinePointerNormalization

@[expose] public section

/-! Scalar queries to word pointers use a framed instance and unary output
index followed by the vertex. Out-of-range coordinates return false.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Read a coordinate of a total word pointer through the concrete query codec. -/
def pointerBitQuery (pointer : List Bool → List Bool → List Bool)
    (word : List Bool) : Bool :=
  (pointer (CircuitWords.first (CircuitWords.first word)) (CircuitWords.rest word)).getD
    (CircuitWords.rest (CircuitWords.first word)).length false

/-- Scalar lookup charges decoding, pointer evaluation, and unary indexing. -/
@[fun_prop] theorem pointerBitQuery_polyTime
    {pointer : List Bool → List Bool → List Bool}
    (hp : ComputableInPolyTime (fun p : List Bool × List Bool => pointer p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (pointerBitQuery pointer) encBits encBool := by
  have hi := CircuitWords.first_polyTime.comp CircuitWords.first_polyTime
  have hv := CircuitWords.rest_polyTime
  have hr := ComputableInPolyTime.length_bits.comp
    (CircuitWords.rest_polyTime.comp CircuitWords.first_polyTime)
  exact (hp.comp (hi.prod hv)).bitsGetDWithInput hr false

/-- Scalar queries to the consistent incoming pointer are efficient. -/
@[fun_prop] theorem normalizedPredecessorBit_polyTime :
    ComputableInPolyTime (pointerBitQuery endOfLineNormalizedPredecessor) encBits encBool :=
  pointerBitQuery_polyTime
    (normalizedPredecessor_polyTime (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits))

/-- Scalar queries to the consistent outgoing pointer are efficient. -/
@[fun_prop] theorem normalizedSuccessorBit_polyTime :
    ComputableInPolyTime (pointerBitQuery endOfLineNormalizedSuccessor) encBits encBool :=
  pointerBitQuery_polyTime
    (normalizedSuccessor_polyTime (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits))

/-- The concrete framing recovers the requested output coordinate. -/
@[simp] theorem pointerBitQuery_pair (pointer : List Bool → List Bool → List Bool)
    (input vertex : List Bool) (i : ℕ) :
    pointerBitQuery pointer
      (CircuitWords.encodePair (CircuitWords.encodePair input (List.replicate i true)) vertex) =
      (pointer input vertex).getD i false := by
  simp only [pointerBitQuery, CircuitWords.first_encodePair,
    CircuitWords.rest_encodePair, List.length_replicate]

end GameTheory.Complexity.Backend
