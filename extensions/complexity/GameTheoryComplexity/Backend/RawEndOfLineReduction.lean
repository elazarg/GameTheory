module

public import GameTheoryComplexity.Backend.RawEndOfLine
public import GameTheoryComplexity.Backend.EndOfLineVerifier

@[expose] public section

/-! Every consistent-edge endpoint answer decodes to an asymmetric raw witness.
A broken first inverse link is recovered from the endpoint relation's empty
fallback by returning the original instance's origin. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime
open EndOfLineMachineOps

/-- Keep genuine endpoints, and recover a broken first link at the origin. -/
def rawToEndpointDecode (p : List Bool × List Bool) : List Bool :=
  if endOfLineSourceFlag p.1 then p.2
  else if rawEndOfLineSourceFlag p.1 then endOfLineOrigin p.1 else p.2

/-- Decoding inspects only polynomial-time source checks and the unary origin. -/
@[fun_prop] theorem rawToEndpointDecode_polyTime :
    ComputableInPolyTime rawToEndpointDecode (encPair encBits encBits) encBits := by
  have hi := fst encBits encBits
  have hw := snd encBits encBits
  exact (endOfLineSourceFlag_polyTime hi).ite hw
    ((rawEndOfLineSourceFlag_polyTime hi).ite (origin_polyTime hi) hw)

/-- Every endpoint answer decodes to a raw witness, including both fallback cases. -/
theorem rawToEndpointDecode_sound (input witness : List Bool)
    (h : endOfLineRelation input witness) :
    rawEndOfLineRelation input (rawToEndpointDecode (input, witness)) := by
  rcases h with ⟨hsource, hlen, hne, hend⟩ | ⟨hsource, rfl⟩
  · have hf := (endOfLineSourceFlag_accept input).mpr hsource
    have hd : rawToEndpointDecode (input, witness) = witness := by
      simp [rawToEndpointDecode, hf]
    rw [hd]
    exact Or.inl ⟨⟨hsource.1, hsource.2.1⟩, hlen,
      GameTheory.Math.EndOfLine.endpoint_rawWitness _ _ hne hend⟩
  · have hf : endOfLineSourceFlag input = false :=
      Bool.eq_false_of_not_eq_true
        (fun he => hsource ((endOfLineSourceFlag_accept input).mp he))
    by_cases hweak : rawEndOfLineSourceValid input
    · have hw := (rawEndOfLineSourceFlag_accept input).mpr hweak
      have hd : rawToEndpointDecode (input, []) = endOfLineOrigin input := by
        simp [rawToEndpointDecode, hf, hw]
      rw [hd]
      refine Or.inl ⟨hweak, List.length_replicate, Or.inl ?_⟩
      intro hlink
      exact hsource ⟨hweak.1, hweak.2, hlink⟩
    · have hw : rawEndOfLineSourceFlag input = false :=
        Bool.eq_false_of_not_eq_true
          (fun he => hweak ((rawEndOfLineSourceFlag_accept input).mp he))
      have hd : rawToEndpointDecode (input, []) = [] := by
        simp [rawToEndpointDecode, hf, hw]
      exact Or.inr ⟨hweak, hd⟩

/-- The identity instance map and total decoder form a native search reduction. -/
theorem rawToEndpointReduction :
    Cslib.Complexity.SearchReducible encBits encBits rawEndOfLineRelation endOfLineRelation :=
  Cslib.Complexity.SearchReducible.of_isTotalSearch
    (f := id) (g := rawToEndpointDecode) endOfLineRelation_total id'
    rawToEndpointDecode_polyTime rawToEndpointDecode_sound

end GameTheory.Complexity.Backend
