import GameTheoryComplexity.Backend.GridRoutingNodeCodec
import GameTheoryComplexity.Backend.GridRoutingLiveMachine
import GameTheoryComplexity.Backend.GridRoutingImageMachine

/-! Internal node operations dispatch on the vertex/interior tag while retaining
raw framed fields. Their semantics agree with the total natural routing nodes. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

/-- Validate a vertex or interior label according to its internal tag. -/
def routingLiveNodeFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node)
    (routingLiveInteriorFlag ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node))
    (routingLiveVertexFlag ruler (routingNodeOwnerBits node))

/-- Internal liveness agrees exactly with the natural node decoded from every word. -/
theorem routingLiveNodeFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : routingLiveNodeFlag ruler P S node =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node))] := by
  cases node with
  | nil =>
    simpa [routingLiveNodeFlag, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀] using
      routingLiveVertexFlag_value ruler (routingNodeOwnerBits [])
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
  | cons tag node =>
    cases tag
    · simpa [routingLiveNodeFlag, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀] using
        routingLiveVertexFlag_value ruler (routingNodeOwnerBits (false :: node))
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
    · simpa [routingLiveNodeFlag, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀] using
        routingLiveInteriorFlag_value ruler P S (routingNodeOwnerBits (true :: node))
          (routingNodeXBits (true :: node)) (routingNodeYBits (true :: node))

/-- Internal liveness always emits exactly one Boolean flag. -/
@[simp] theorem routingLiveNodeFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : (routingLiveNodeFlag ruler P S node).length = 1 := by
  rw [routingLiveNodeFlag_value]
  rfl

private theorem nodeTagFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => bitAt [] (node z)) ∈ FP :=
  CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hn))

/-- Liveness composes seeded pointer queries with any polynomial-time node producer. -/
theorem routingLiveNodeFlagUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed node : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingLiveNodeFlag (ruler z) (P (seed z)) (S (seed z)) (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (routingLiveInteriorFlagUniformFn_mem_FP P S hr hs (routingNodeOwnerBitsFn_mem_FP hn)
      (routingNodeXBitsFn_mem_FP hn) (routingNodeYBitsFn_mem_FP hn) hP hS)
    (routingLiveVertexFlagFn_mem_FP hr (routingNodeOwnerBitsFn_mem_FP hn))

/-- Image the horizontal field of an interior node; original vertices stay on column zero. -/
def routingNodeImageXBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node)
    (routingImageXBits ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node)) []

/-- Image the vertical field of an interior node; original vertices retain their row. -/
def routingNodeImageYBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node)
    (routingImageYBits ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node))
    (routingSixBits (routingNodeOwnerBits node))

/-- Horizontal node imaging agrees with the natural geometric realization on every word. -/
theorem routingNodeImageXBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : Nat.fromBitsLE (routingNodeImageXBits ruler P S node) =
      (routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node)).1 := by
  cases node with
  | nil => rfl
  | cons tag node =>
    cases tag with
    | false => rfl
    | true =>
      simp [routingNodeImageXBits, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀,
        routingImageXBits_value, routedCoordinate]

/-- Vertical node imaging agrees with the natural geometric realization on every word. -/
theorem routingNodeImageYBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : Nat.fromBitsLE (routingNodeImageYBits ruler P S node) =
      (routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node)).2 := by
  cases node with
  | nil => rfl
  | cons tag node => cases tag <;>
      simp [routingNodeImageYBits, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀,
        routingImageYBits_value, routingSixBits_value, routedCoordinate, vertexPoint]

/-- Both image fields form precisely the natural coordinate of the decoded internal node. -/
theorem routingNodeImage_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) :
    (Nat.fromBitsLE (routingNodeImageXBits ruler P S node),
      Nat.fromBitsLE (routingNodeImageYBits ruler P S node)) =
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) :=
  Prod.ext (routingNodeImageXBits_value ruler P S node) (routingNodeImageYBits_value ruler P S node)

/-- Switch an interior owner without changing its raw coordinates; vertices retain their word. -/
def routingNodeSwitchBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node)
    (routingInteriorNodeBits
      (routingSwitchOwnerBits ruler P S (routingNodeOwnerBits node)
        (routingNodeXBits node) (routingNodeYBits node))
      (routingNodeXBits node) (routingNodeYBits node)) node

/-- Node switching decodes to the exact natural crossing involution on every word. -/
theorem routingNodeSwitchBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : routingDecodeNodeBits (routingNodeSwitchBits ruler P S node) =
      routedSwitch (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) := by
  cases node with
  | nil => rfl
  | cons tag node =>
    cases tag
    · simp [routingNodeSwitchBits, routingDecodeNodeBits, bitAt_eq, bitOf, caseBit₀, routedSwitch]
    · have hd : routingDecodeNodeBits (true :: node) =
          .inr (Nat.fromBitsLE (routingNodeOwnerBits (true :: node)),
            (Nat.fromBitsLE (routingNodeXBits (true :: node)),
              Nat.fromBitsLE (routingNodeYBits (true :: node)))) := by
        simp [routingDecodeNodeBits]
      rw [hd]
      simpa [routingNodeSwitchBits, bitAt_eq, bitOf, caseBit₀] using
        (routingSwitchOwnerBits_value ruler P S (routingNodeOwnerBits (true :: node))
          (routingNodeXBits (true :: node)) (routingNodeYBits (true :: node))).symm

/-- Horizontal node images compose seeded polynomial-time pointer queries uniformly. -/
theorem routingNodeImageXBitsUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed node : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingNodeImageXBits (ruler z) (P (seed z)) (S (seed z)) (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (routingImageXBitsUniformFn_mem_FP P S hr hs (routingNodeOwnerBitsFn_mem_FP hn)
      (routingNodeXBitsFn_mem_FP hn) (routingNodeYBitsFn_mem_FP hn) hP hS) (constFn_mem_FP [])

/-- Vertical node images compose seeded polynomial-time pointer queries uniformly. -/
theorem routingNodeImageYBitsUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed node : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingNodeImageYBits (ruler z) (P (seed z)) (S (seed z)) (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (routingImageYBitsUniformFn_mem_FP P S hr hs (routingNodeOwnerBitsFn_mem_FP hn)
      (routingNodeXBitsFn_mem_FP hn) (routingNodeYBitsFn_mem_FP hn) hP hS)
    (routingSixBitsFn_mem_FP (routingNodeOwnerBitsFn_mem_FP hn))

/-- Node switching has a uniform polynomial-time certificate on every internal word. -/
theorem routingNodeSwitchBitsUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed node : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingNodeSwitchBits (ruler z) (P (seed z)) (S (seed z)) (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (routingInteriorNodeBitsFn_mem_FP
      (routingSwitchOwnerBitsUniformFn_mem_FP P S hr hs (routingNodeOwnerBitsFn_mem_FP hn)
        (routingNodeXBitsFn_mem_FP hn) (routingNodeYBitsFn_mem_FP hn) hP hS)
      (routingNodeXBitsFn_mem_FP hn) (routingNodeYBitsFn_mem_FP hn)) hn

end GameTheory.Complexity.Backend
