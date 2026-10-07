import GameTheoryComplexity.Backend.RawEndOfLine
import GameTheoryComplexity.Backend.EndOfLineVerifier
import GameTheoryComplexity.Backend.SearchReduction

/-! Standard raw witnesses reduce to consistent-edge endpoint search. A failed
first inverse link is recovered from the endpoint relation's empty fallback by
returning the original instance's origin. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open EndOfLineMachineOps

/-- Keep genuine endpoints, and recover a broken first link at the origin. -/
def rawToEndpointDecode (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (endOfLineSourceFlag (v 0)) (v 1)
    (caseBit₀ (rawEndOfLineSourceFlag (v 0)) (endOfLineOrigin (v 0)) (v 1))

/-- Decoding inspects only polynomial-time source flags and the unary origin. -/
theorem rawToEndpointDecode_mem_FPn : FPn rawToEndpointDecode := by
  let g := fun z => rawToEndpointDecode ![pairSnd z, pairSnd (pairFst z)]
  have hv : (fun z => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hg : g ∈ FP :=
    selectFn_mem_FP (endOfLineSourceFlagFn_mem_FP pairSnd_mem_FP) hv
      (selectFn_mem_FP (rawEndOfLineSourceFlagFn_mem_FP pairSnd_mem_FP)
        (originFn_mem_FP pairSnd_mem_FP) hv)
  refine ⟨g, hg, fun v => ?_⟩
  simp [g, rawToEndpointDecode, encodeVec, Fin.tail]

/-- Every endpoint solution decodes to a standard raw witness, including both
invalid-promise cases. The instance map is the identity. -/
def rawToEndpointReduction : SearchReduction rawEndOfLineRelation endOfLineRelation where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := rawToEndpointDecode
  decode_mem_FPn := rawToEndpointDecode_mem_FPn
  sound := by
    intro input witness h
    rcases h with ⟨hsource, hlen, hne, hend⟩ | ⟨hsource, rfl⟩
    · have hf := (endOfLineSourceFlag_accept input).mpr hsource
      have hd : rawToEndpointDecode ![input, witness] = witness := by
        simp only [rawToEndpointDecode, Matrix.cons_val_zero, Matrix.cons_val_one, hf,
          caseBit₀_cons, Bool.cond_true]
      rw [hd]
      exact Or.inl ⟨⟨hsource.1, hsource.2.1⟩, hlen,
        GameTheory.Math.EndOfLine.endpoint_rawWitness _ _ hne hend⟩
    · have hf : endOfLineSourceFlag input = [false] :=
        (endOfLineSourceFlag_flag input).resolve_left
          (fun he => hsource ((endOfLineSourceFlag_accept input).mp he))
      by_cases hweak : rawEndOfLineSourceValid input
      · have hw := (rawEndOfLineSourceFlag_accept input).mpr hweak
        have hd : rawToEndpointDecode ![input, []] = endOfLineOrigin input := by
          simp only [rawToEndpointDecode, Matrix.cons_val_zero, Matrix.cons_val_one,
            hf, hw, caseBit₀_cons, Bool.cond_true, Bool.cond_false]
        rw [hd]
        refine Or.inl ⟨hweak, List.length_replicate, Or.inl ?_⟩
        intro hlink
        exact hsource ⟨hweak.1, hweak.2, hlink⟩
      · have hw : rawEndOfLineSourceFlag input = [false] :=
          (rawEndOfLineSourceFlag_flag input).resolve_left
            (fun he => hweak ((rawEndOfLineSourceFlag_accept input).mp he))
        have hd : rawToEndpointDecode ![input, []] = [] := by
          simp only [rawToEndpointDecode, Matrix.cons_val_zero, Matrix.cons_val_one,
            hf, hw, caseBit₀_cons, Bool.cond_false]
        exact Or.inr ⟨hweak, hd⟩

end GameTheory.Complexity.Backend
