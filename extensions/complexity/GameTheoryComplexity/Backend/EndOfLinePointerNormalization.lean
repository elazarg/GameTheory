import GameTheory.Math.EndOfLineNormalization
import GameTheoryComplexity.Backend.EndOfLineMachineOps

/-! Polynomial-time evaluation of consistent End-of-Line pointers. Each evaluator
checks the original pointer and its reverse link, retaining the pointer only when
it encodes an incident edge. These are word evaluators, rather than serializers
of new circuit instances. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open EndOfLineMachineOps

/-- Keep an incoming pointer exactly when its reverse link agrees. -/
def endOfLineNormalizedPredecessor (input vertex : List Bool) : List Bool :=
  caseBit₀ (predecessorFlag input vertex) (endOfLinePredecessor input vertex) vertex

/-- Keep an outgoing pointer exactly when its reverse link agrees. -/
def endOfLineNormalizedSuccessor (input vertex : List Bool) : List Bool :=
  caseBit₀ (successorFlag input vertex) (endOfLineSuccessor input vertex) vertex

theorem endOfLineNormalizedPredecessor_eq (input vertex : List Bool) :
    endOfLineNormalizedPredecessor input vertex =
      GameTheory.Math.EndOfLine.normalizePredecessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  have hf : predecessorFlag input vertex = [true] ∨
      predecessorFlag input vertex = [false] := andBit_flag _ _
  rcases hf with h | h
  · have hp := (predecessorFlag_accept input vertex).mp h
    simp only [endOfLineNormalizedPredecessor, h, caseBit₀_cons, Bool.cond_true,
      GameTheory.Math.EndOfLine.normalizePredecessor, ite_eq_left hp]
  · have hp : ¬GameTheory.Math.EndOfLine.HasPredecessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
      intro hp
      have ht := (predecessorFlag_accept input vertex).mpr hp
      rw [h] at ht
      cases ht
    simp only [endOfLineNormalizedPredecessor, h, caseBit₀_cons, Bool.cond_false,
      GameTheory.Math.EndOfLine.normalizePredecessor, ite_eq_right hp]

theorem endOfLineNormalizedSuccessor_eq (input vertex : List Bool) :
    endOfLineNormalizedSuccessor input vertex =
      GameTheory.Math.EndOfLine.normalizeSuccessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  have hf : successorFlag input vertex = [true] ∨
      successorFlag input vertex = [false] := andBit_flag _ _
  rcases hf with h | h
  · have hs := (successorFlag_accept input vertex).mp h
    simp only [endOfLineNormalizedSuccessor, h, caseBit₀_cons, Bool.cond_true,
      GameTheory.Math.EndOfLine.normalizeSuccessor, ite_eq_left hs]
  · have hs : ¬GameTheory.Math.EndOfLine.HasSuccessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
      intro hs
      have ht := (successorFlag_accept input vertex).mpr hs
      rw [h] at ht
      cases ht
    simp only [endOfLineNormalizedSuccessor, h, caseBit₀_cons, Bool.cond_false,
      GameTheory.Math.EndOfLine.normalizeSuccessor, ite_eq_right hs]

@[simp] theorem endOfLineNormalizedPredecessor_length (input vertex : List Bool) :
    (endOfLineNormalizedPredecessor input vertex).length = vertex.length := by
  rw [endOfLineNormalizedPredecessor_eq,
    GameTheory.Math.EndOfLine.normalizePredecessor]
  split_ifs
  · exact evaluateCircuitVector_length _ vertex
  · rfl

@[simp] theorem endOfLineNormalizedSuccessor_length (input vertex : List Bool) :
    (endOfLineNormalizedSuccessor input vertex).length = vertex.length := by
  rw [endOfLineNormalizedSuccessor_eq, GameTheory.Math.EndOfLine.normalizeSuccessor]
  split_ifs
  · exact evaluateCircuitVector_length _ vertex
  · rfl

/-- Normalization composes with any polynomial-time instance and vertex producers. -/
theorem normalizedPredecessorFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => endOfLineNormalizedPredecessor (input z) (vertex z)) ∈ FP :=
  selectFn_mem_FP (predecessorFlagFn_mem_FP hi hv) (predecessorFn_mem_FP hi hv) hv

theorem normalizedSuccessorFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => endOfLineNormalizedSuccessor (input z) (vertex z)) ∈ FP :=
  selectFn_mem_FP (successorFlagFn_mem_FP hi hv) (successorFn_mem_FP hi hv) hv

theorem endOfLineNormalizedPredecessor_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => endOfLineNormalizedPredecessor (v 0) (v 1)) := by
  have hp := normalizedPredecessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP
  have hc := Cobham.comp (FP_subset_CobhamFP hp)
    (fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing
      (Cobham.proj (0 : Fin 2)) (Cobham.proj 1))
  exact cobham_iff_FPn.mp (hc.of_eq fun v => by simp)

theorem endOfLineNormalizedSuccessor_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => endOfLineNormalizedSuccessor (v 0) (v 1)) := by
  have hs := normalizedSuccessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP
  have hc := Cobham.comp (FP_subset_CobhamFP hs)
    (fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing
      (Cobham.proj (0 : Fin 2)) (Cobham.proj 1))
  exact cobham_iff_FPn.mp (hc.of_eq fun v => by simp)

/-- Machine normalization preserves precisely the original graph endpoints. -/
theorem endOfLineNormalized_endpoint_iff (input vertex : List Bool) :
    GameTheory.Math.EndOfLine.IsEndpoint (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input) vertex ↔
      GameTheory.Math.EndOfLine.IsEndpoint (endOfLinePredecessor input)
        (endOfLineSuccessor input) vertex := by
  have hp := funext (endOfLineNormalizedPredecessor_eq input)
  have hs := funext (endOfLineNormalizedSuccessor_eq input)
  rw [hp, hs]
  exact GameTheory.Math.EndOfLine.isEndpoint_normalize_iff _ _ vertex

/-- Under the genuine-source promise, normalized raw answers are exactly endpoints. -/
theorem endOfLineNormalized_rawWitness_iff {input vertex : List Bool}
    (hsource : endOfLineSourceValid input) :
    GameTheory.Math.EndOfLine.RawWitness (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input) (endOfLineOrigin input) vertex ↔
      vertex ≠ endOfLineOrigin input ∧ GameTheory.Math.EndOfLine.IsEndpoint
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  have hp := funext (endOfLineNormalizedPredecessor_eq input)
  have hs := funext (endOfLineNormalizedSuccessor_eq input)
  rw [hp, hs]
  exact GameTheory.Math.EndOfLine.normalized_rawWitness_iff _ _
    hsource.1 hsource.2.1 hsource.2.2

end GameTheory.Complexity.Backend
