import GameTheoryComplexity.Backend.UniformCircuitSpecialization
import GameTheoryComplexity.Backend.EndOfLineScalarQueries
import GameTheoryComplexity.Backend.CircuitVectorEmission
import GameTheoryComplexity.Backend.EndOfLineVerifier

/-! Uniform circuit generation serializes consistent-edge normalization of
End-of-Line pointers. Scalar bit queries are specialized to each instance and
coordinate, then emitted as vectors. Invalid source promises map to the empty instance. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode
open EndOfLineMachineOps

private def scalarPointerCode (gen : List Bool → List Bool) (q : List Bool) : List Bool :=
  gen (pair (List.replicate (endOfLineWidth (pairFst q)) true) (pair q []))

private theorem scalarPointerCode_mem_FP {gen : List Bool → List Bool} (hg : gen ∈ FP) :
    scalarPointerCode gen ∈ FP := by
  have hi : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hw := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) unaryLength_mem_FP
  exact mem_FP_comp (pairFn_mem_FP hw (pairFn_mem_FP hi (constFn_mem_FP []))) hg

private theorem scalarPointerCode_eval (pointer : List Bool → List Bool → List Bool)
    (gen : List Bool → List Bool)
    (hgen : ∀ ruler seed vertex, 0 < ruler.length → vertex.length = ruler.length →
      evalFamilyCode (gen (pair ruler seed)) vertex =
        some (pointerBitQuery pointer (seed ++ vertex)))
    (input vertex : List Bool) (i : ℕ) (hn : 0 < endOfLineWidth input)
    (hi : vertex.length = endOfLineWidth input) :
    evalFamilyCode (scalarPointerCode gen (pair input (List.replicate i true))) vertex =
      some (bitOf (pointer input vertex) i) := by
  have h := hgen (List.replicate (endOfLineWidth input) true)
    (pair (pair input (List.replicate i true)) []) vertex (by simpa using hn)
    (by simpa using hi)
  have happ : pair (pair input (List.replicate i true)) [] ++ vertex =
      pair (pair input (List.replicate i true)) vertex := by simp [pair]
  rw [happ] at h
  simpa only [scalarPointerCode, pairFst_pair, pointerBitQuery_pair] using h

private theorem vectorPointer_eval (pointer : List Bool → List Bool → List Bool)
    (hlen : ∀ input vertex, (pointer input vertex).length = vertex.length)
    (gen : List Bool → List Bool)
    (hgen : ∀ ruler seed vertex, 0 < ruler.length → vertex.length = ruler.length →
      evalFamilyCode (gen (pair ruler seed)) vertex =
        some (pointerBitQuery pointer (seed ++ vertex)))
    (input vertex : List Bool) (hn : 0 < endOfLineWidth input)
    (hi : vertex.length = endOfLineWidth input) :
    evaluateCircuitVector
      (emitCircuitVector (scalarPointerCode gen) input (endOfLineWidth input)) vertex =
        pointer input vertex := by
  rw [← hi, evaluateCircuitVector_emit]
  simp only [scalarPointerCode_eval pointer gen hgen input vertex _ hn hi,
    Option.getD_some]
  apply List.ext_getElem
  · simp [hlen]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact bitOf_eq_getElem h₂

private def generatedInstance (p s : List Bool → List Bool) (input : List Bool) : List Bool :=
  pair (pairFst input)
    (pair (emitCircuitVector (scalarPointerCode p) input (endOfLineWidth input))
      (emitCircuitVector (scalarPointerCode s) input (endOfLineWidth input)))

private theorem generatedInstance_mem_FP {p s : List Bool → List Bool}
    (hp : p ∈ FP) (hs : s ∈ FP) : generatedInstance p s ∈ FP := by
  have hi : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  exact pairFn_mem_FP pairFst_mem_FP (pairFn_mem_FP
    (emitCircuitVectorFn_mem_FP _ _ _ (scalarPointerCode_mem_FP hp) hi pairFst_mem_FP)
    (emitCircuitVectorFn_mem_FP _ _ _ (scalarPointerCode_mem_FP hs) hi pairFst_mem_FP))

private theorem source_width_pos {input : List Bool} (h : endOfLineSourceValid input) :
    0 < endOfLineWidth input := by
  by_contra hn
  have hz : endOfLineWidth input = 0 := by omega
  have ho : endOfLineOrigin input = [] := by simp [endOfLineOrigin, hz]
  have hs : endOfLineSuccessor input (endOfLineOrigin input) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [endOfLineSuccessor, evaluateCircuitVector_length, ho]
    rfl
  exact h.2.1 (hs.trans ho.symm)

/-- An actual polynomial-time mapper serializes normalized pointers at the same
width for valid sources and returns the empty instance for invalid sources. -/
theorem exists_normalizedEndOfLineInstance :
    ∃ f : List Bool → List Bool, f ∈ FP ∧
      (∀ input, endOfLineSourceValid input →
        endOfLineWidth (f input) = endOfLineWidth input ∧
          ∀ vertex, vertex.length = endOfLineWidth input →
            endOfLinePredecessor (f input) vertex =
                endOfLineNormalizedPredecessor input vertex ∧
            endOfLineSuccessor (f input) vertex = endOfLineNormalizedSuccessor input vertex) ∧
      (∀ input, ¬endOfLineSourceValid input → f input = []) := by
  obtain ⟨p, hp, hpeval⟩ := exists_prefixCircuitGenerator
    (pointerBitQuery endOfLineNormalizedPredecessor) normalizedPredecessorBit_mem_FP
  obtain ⟨s, hs, hseval⟩ := exists_prefixCircuitGenerator
    (pointerBitQuery endOfLineNormalizedSuccessor) normalizedSuccessorBit_mem_FP
  let f := fun input => caseBit₀ (endOfLineSourceFlag input) (generatedInstance p s input) []
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  refine ⟨f, selectFn_mem_FP (endOfLineSourceFlagFn_mem_FP hid)
    (generatedInstance_mem_FP hp hs) (constFn_mem_FP []), ?_, ?_⟩
  · intro input hsource
    have hflag := (endOfLineSourceFlag_accept input).mpr hsource
    have hf : f input = generatedInstance p s input := by simp [f, hflag, caseBit₀]
    rw [hf]
    constructor
    · simp [generatedInstance, endOfLineWidth]
    · intro vertex hi
      have hn := source_width_pos hsource
      constructor
      · simpa only [generatedInstance, endOfLinePredecessor, pairFst_pair, pairSnd_pair]
          using vectorPointer_eval _ endOfLineNormalizedPredecessor_length p hpeval
            input vertex hn hi
      · simpa only [generatedInstance, endOfLineSuccessor, pairFst_pair, pairSnd_pair]
          using vectorPointer_eval _ endOfLineNormalizedSuccessor_length s hseval
            input vertex hn hi
  · intro input hinvalid
    have hflag := (endOfLineSourceFlag_flag input).resolve_left
      (fun h => hinvalid ((endOfLineSourceFlag_accept input).mp h))
    simp [f, hflag, caseBit₀]

end GameTheory.Complexity.Backend
