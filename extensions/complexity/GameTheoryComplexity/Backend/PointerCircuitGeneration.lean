import GameTheoryComplexity.Backend.UniformCircuitSpecialization
import GameTheoryComplexity.Backend.EndOfLineScalarQueries
import GameTheoryComplexity.Backend.CircuitVectorEmission
import GameTheoryComplexity.Backend.EndOfLineProblem

/-! Uniform circuit generation serializes polynomial-time word pointers.
A polynomial-time width ruler supplies the vertex length. Scalar bit computations
are specialized to each instance and coordinate, then emitted as circuit vectors. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

private def scalarPointerCode (ruler gen : List Bool → List Bool) (q : List Bool) : List Bool :=
  gen (pair (List.replicate (ruler (pairFst q)).length true) (pair q []))

private theorem scalarPointerCode_mem_FP {ruler gen : List Bool → List Bool}
    (hr : ruler ∈ FP) (hg : gen ∈ FP) : scalarPointerCode ruler gen ∈ FP := by
  have hi : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hw := mem_FP_comp (mem_FP_comp pairFst_mem_FP hr) unaryLength_mem_FP
  exact mem_FP_comp (pairFn_mem_FP hw (pairFn_mem_FP hi (constFn_mem_FP []))) hg

private theorem scalarPointerCode_eval (ruler : List Bool → List Bool)
    (pointer : List Bool → List Bool → List Bool)
    (gen : List Bool → List Bool)
    (hgen : ∀ ruler seed vertex, 0 < ruler.length → vertex.length = ruler.length →
      evalFamilyCode (gen (pair ruler seed)) vertex =
        some (pointerBitQuery pointer (seed ++ vertex)))
    (input vertex : List Bool) (i : ℕ) (hn : 0 < (ruler input).length)
    (hi : vertex.length = (ruler input).length) :
    evalFamilyCode (scalarPointerCode ruler gen (pair input (List.replicate i true))) vertex =
      some (bitOf (pointer input vertex) i) := by
  have h := hgen (List.replicate (ruler input).length true)
    (pair (pair input (List.replicate i true)) []) vertex (by simpa using hn)
    (by simpa using hi)
  have happ : pair (pair input (List.replicate i true)) [] ++ vertex =
      pair (pair input (List.replicate i true)) vertex := by simp [pair]
  rw [happ] at h
  simpa only [scalarPointerCode, pairFst_pair, pointerBitQuery_pair] using h

private theorem vectorPointer_eval (ruler : List Bool → List Bool)
    (pointer : List Bool → List Bool → List Bool)
    (hlen : ∀ input vertex, (pointer input vertex).length = vertex.length)
    (gen : List Bool → List Bool)
    (hgen : ∀ ruler seed vertex, 0 < ruler.length → vertex.length = ruler.length →
      evalFamilyCode (gen (pair ruler seed)) vertex =
        some (pointerBitQuery pointer (seed ++ vertex)))
    (input vertex : List Bool) (hn : 0 < (ruler input).length)
    (hi : vertex.length = (ruler input).length) :
    evaluateCircuitVector
      (emitCircuitVector (scalarPointerCode ruler gen) input (ruler input).length) vertex =
        pointer input vertex := by
  rw [← hi, evaluateCircuitVector_emit]
  simp only [scalarPointerCode_eval ruler pointer gen hgen input vertex _ hn hi,
    Option.getD_some]
  apply List.ext_getElem
  · simp [hlen]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact bitOf_eq_getElem h₂

private def generatedInstance (ruler p s : List Bool → List Bool) (input : List Bool) : List Bool :=
  pair (ruler input)
    (pair (emitCircuitVector (scalarPointerCode ruler p) input (ruler input).length)
      (emitCircuitVector (scalarPointerCode ruler s) input (ruler input).length))

private theorem generatedInstance_mem_FP {ruler p s : List Bool → List Bool}
    (hr : ruler ∈ FP) (hp : p ∈ FP) (hs : s ∈ FP) : generatedInstance ruler p s ∈ FP := by
  have hi : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  exact pairFn_mem_FP hr (pairFn_mem_FP
    (emitCircuitVectorFn_mem_FP _ _ _ (scalarPointerCode_mem_FP hr hp) hi hr)
    (emitCircuitVectorFn_mem_FP _ _ _ (scalarPointerCode_mem_FP hr hs) hi hr))

private theorem pointerFn_mem_FP
    {pointer : List Bool → List Bool → List Bool}
    (hp : (fun z => pointer (pairFst z) (pairSnd z)) ∈ FP)
    {input vertex : List Bool → List Bool} (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => pointer (input z) (vertex z)) ∈ FP := by
  have h := mem_FP_comp (pairFn_mem_FP hi hv) hp
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using h

/-- Any two length-preserving FP pointers admit an actual FP serialized circuit
instance generator, with exact pointer agreement at the positive ruler width. -/
theorem exists_pointerCircuitInstance (ruler : List Bool → List Bool)
    (p s : List Bool → List Bool → List Bool) (hr : ruler ∈ FP)
    (hp : (fun z => p (pairFst z) (pairSnd z)) ∈ FP)
    (hs : (fun z => s (pairFst z) (pairSnd z)) ∈ FP)
    (hplen : ∀ input vertex, (p input vertex).length = vertex.length)
    (hslen : ∀ input vertex, (s input vertex).length = vertex.length) :
    ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ input, 0 < (ruler input).length →
      endOfLineWidth (f input) = (ruler input).length ∧
        ∀ vertex, vertex.length = (ruler input).length →
          endOfLinePredecessor (f input) vertex = p input vertex ∧
          endOfLineSuccessor (f input) vertex = s input vertex := by
  obtain ⟨pg, hpg, hpeval⟩ := exists_prefixCircuitGenerator
    (pointerBitQuery p) (pointerBitQuery_mem_FP (pointerFn_mem_FP hp))
  obtain ⟨sg, hsg, hseval⟩ := exists_prefixCircuitGenerator
    (pointerBitQuery s) (pointerBitQuery_mem_FP (pointerFn_mem_FP hs))
  refine ⟨generatedInstance ruler pg sg, generatedInstance_mem_FP hr hpg hsg, ?_⟩
  intro input hn
  constructor
  · simp [generatedInstance, endOfLineWidth]
  · intro vertex hi
    constructor
    · simpa only [generatedInstance, endOfLinePredecessor, pairFst_pair, pairSnd_pair]
        using vectorPointer_eval ruler p hplen pg hpeval input vertex hn hi
    · simpa only [generatedInstance, endOfLineSuccessor, pairFst_pair, pairSnd_pair]
        using vectorPointer_eval ruler s hslen sg hseval input vertex hn hi

end GameTheory.Complexity.Backend
