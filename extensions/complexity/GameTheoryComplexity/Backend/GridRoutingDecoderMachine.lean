module

public import GameTheoryComplexity.Backend.GridRoutingCandidateMachine

@[expose] public section

/-! Six fixed local candidates suffice to invert the routed grid image.
Two virtual-center candidates are validated even when no crossing is present;
liveness and exact image matching make such extra candidates harmless. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

/-- Produce two center occurrences followed by the four ordinary local candidates. -/
def routingCandidateNodes (ruler : List Bool) (P : List Bool → List Bool)
    (x y : List Bool) : List (List Bool) :=
  let cx := routingCenterBits x
  let cy := routingCenterBits y
  let row := routingDivSixBits y
  [routingInteriorNodeBits (routingHorizontalOwnerBits ruler P cy) cx cy,
    routingInteriorNodeBits (routingVerticalOwnerBits ruler cx) cx cy,
    routingVertexNodeBits row,
    routingInteriorNodeBits (routingHorizontalOwnerBits ruler P y) x y,
    routingInteriorNodeBits (routingVerticalOwnerBits ruler x) x y,
    routingInteriorNodeBits (routingQueryBits ruler P row) x y]

/-- Decode through six validated candidates and an explicit found flag. -/
def routingDecoderBits (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  routingChooseNodeBits ruler P S x y (routingCandidateNodes ruler P x y)

/-- Candidate production has constant cardinality independent of graph size. -/
@[simp] theorem routingCandidateNodes_length (ruler : List Bool) (P : List Bool → List Bool)
    (x y : List Bool) : (routingCandidateNodes ruler P x y).length = 6 := rfl

private theorem candidateNodes_decode (ruler : List Bool) (P : List Bool → List Bool)
    (x y : List Bool) :
    (routingCandidateNodes ruler P x y).map routingDecodeNodeBits =
      let point := (lsbValue x, lsbValue y)
      let center := crossingCenter point
      let pred := routingOriginalPointer ruler P
      [.inr (horizontalOwner pred center, center),
        .inr (verticalOwner (2 ^ ruler.length) center, center)] ++
          ordinaryCandidates (2 ^ ruler.length) pred point := by
  simp only [routingCandidateNodes, List.map_cons, List.map_nil,
    routingDecodeNodeBits_interior, routingDecodeNodeBits_vertex,
    routingHorizontalOwnerBits_value, routingVerticalOwnerBits_value,
    routingQueryBits_value, routingDivSixBits_value, routingCenterBits_value,
    crossingCenter, horizontalOwner, verticalOwner, ordinaryCandidates]
  rfl

/-- The fixed candidate list includes every candidate of the mathematical decoder. -/
theorem routingCandidateNodes_cover (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) (node : WireNode)
    (hm : node ∈ wireCandidates (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (lsbValue x, lsbValue y)) :
    node ∈ (routingCandidateNodes ruler P x y).map routingDecodeNodeBits := by
  rw [candidateNodes_decode]
  dsimp only [wireCandidates] at hm
  cases hc : crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (crossingCenter (lsbValue x, lsbValue y)) with
  | none =>
      rw [hc] at hm
      exact List.mem_append_right _ hm
  | some owners =>
      rw [hc] at hm
      have ho : owners =
          (horizontalOwner (routingOriginalPointer ruler P)
            (crossingCenter (lsbValue x, lsbValue y)),
          verticalOwner (2 ^ ruler.length)
            (crossingCenter (lsbValue x, lsbValue y))) := by
        unfold crossingOwners at hc
        dsimp only at hc
        split_ifs at hc
        exact (Option.some.inj hc).symm
      rw [ho] at hm
      exact hm

/-- The binary decoder agrees with the mathematical grid decoder on every coordinate word. -/
theorem routingDecoderBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingDecodeResultBits (routingDecoderBits ruler P S x y) =
      decodeWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) := by
  unfold routingDecoderBits
  rw [routingChooseNodeBits_decode]
  cases hd : decodeWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) with
  | none =>
      cases hs : chooseWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (lsbValue x, lsbValue y)
          ((routingCandidateNodes ruler P x y).map routingDecodeNodeBits) with
      | none => rfl
      | some node =>
          have h := decodeWireNode_eq_some_iff.mpr (chooseWireNode_sound hs)
          rw [hd] at h
          cases h
  | some node =>
      obtain ⟨hl, he⟩ := decodeWireNode_eq_some_iff.mp hd
      apply chooseWireNode_complete hl he
      apply routingCandidateNodes_cover
      rw [← he]
      exact wireCandidates_complete hl

/-- Decoding always produces a canonical found flag, including for background points. -/
theorem routingDecoderBits_found_flag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : CircuitWords.first (routingDecoderBits ruler P S x y) = [true] ∨
      CircuitWords.first (routingDecoderBits ruler P S x y) = [false] :=
  routingChooseNodeBits_found_flag ruler P S x y (routingCandidateNodes ruler P x y)

/-- Six local candidate producers compose into one uniform polynomial-time decoder. -/
@[fun_prop] theorem routingDecoderBitsUniform_polyTime (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hs : ComputableInPolyTime seed enc encBits) (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingDecoderBits (ruler z) (P (seed z)) (S (seed z)) (x z) (y z)) enc encBits := by
  have hcx := routingCenterBits_polyTime hx
  have hcy := routingCenterBits_polyTime hy
  have hrow := routingDivSixBits_polyTime hy
  have hhcenter := routingHorizontalOwnerBitsUniform_polyTime P hr hs hcy hP
  have hvcenter := routingVerticalOwnerBits_polyTime hr hcx
  have hh := routingHorizontalOwnerBitsUniform_polyTime P hr hs hy hP
  have hv := routingVerticalOwnerBits_polyTime hr hx
  have hp := routingQueryBitsUniform_polyTime P hr hs hrow hP
  let a : α → List Bool := fun z => routingInteriorNodeBits
    (routingHorizontalOwnerBits (ruler z) (P (seed z)) (routingCenterBits (y z)))
    (routingCenterBits (x z)) (routingCenterBits (y z))
  let b : α → List Bool := fun z => routingInteriorNodeBits
    (routingVerticalOwnerBits (ruler z) (routingCenterBits (x z)))
    (routingCenterBits (x z)) (routingCenterBits (y z))
  let c : α → List Bool := fun z => routingVertexNodeBits (routingDivSixBits (y z))
  let d : α → List Bool := fun z => routingInteriorNodeBits
    (routingHorizontalOwnerBits (ruler z) (P (seed z)) (y z)) (x z) (y z)
  let e : α → List Bool := fun z => routingInteriorNodeBits
    (routingVerticalOwnerBits (ruler z) (x z)) (x z) (y z)
  let f : α → List Bool := fun z => routingInteriorNodeBits
    (routingQueryBits (ruler z) (P (seed z)) (routingDivSixBits (y z))) (x z) (y z)
  have ha : ComputableInPolyTime a enc encBits := routingInteriorNodeBits_polyTime hhcenter hcx hcy
  have hb : ComputableInPolyTime b enc encBits := routingInteriorNodeBits_polyTime hvcenter hcx hcy
  have hc : ComputableInPolyTime c enc encBits := routingVertexNodeBits_polyTime hrow
  have hd : ComputableInPolyTime d enc encBits := routingInteriorNodeBits_polyTime hh hx hy
  have he : ComputableInPolyTime e enc encBits := routingInteriorNodeBits_polyTime hv hx hy
  have hf : ComputableInPolyTime f enc encBits := routingInteriorNodeBits_polyTime hp hx hy
  have hall : ∀ node ∈ [a, b, c, d, e, f], ComputableInPolyTime node enc encBits := by
    intro node hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  have h := routingChooseNodeBitsUniform_polyTime P S hr hs hx hy hP hS
    [a, b, c, d, e, f] hall
  simpa only [routingDecoderBits, routingCandidateNodes, List.map_cons, List.map_nil,
    a, b, c, d, e, f] using h

end GameTheory.Complexity.Backend
