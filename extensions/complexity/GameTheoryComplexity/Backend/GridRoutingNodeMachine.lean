module

public import GameTheoryComplexity.Backend.GridRoutingNodeCodec
public import GameTheoryComplexity.Backend.GridRoutingLiveMachine
public import GameTheoryComplexity.Backend.GridRoutingImageMachine

@[expose] public section

/-! Internal node operations dispatch on the vertex/interior tag while retaining
raw framed fields. Their semantics agree with the total natural routing nodes. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- Validate a vertex or interior label according to its internal tag. -/
def routingLiveNodeFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  if node.headD false then
    (routingLiveInteriorFlag ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node))
    else routingLiveVertexFlag ruler (routingNodeOwnerBits node)

/-- Internal liveness agrees exactly with the natural node decoded from every word. -/
theorem routingLiveNodeFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : routingLiveNodeFlag ruler P S node =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node))] := by
  cases node with
  | nil =>
    simpa [routingLiveNodeFlag, routingDecodeNodeBits] using
      routingLiveVertexFlag_value ruler (routingNodeOwnerBits [])
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
  | cons tag node =>
    cases tag
    · simpa [routingLiveNodeFlag, routingDecodeNodeBits] using
        routingLiveVertexFlag_value ruler (routingNodeOwnerBits (false :: node))
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
    · simpa [routingLiveNodeFlag, routingDecodeNodeBits] using
        routingLiveInteriorFlag_value ruler P S (routingNodeOwnerBits (true :: node))
          (routingNodeXBits (true :: node)) (routingNodeYBits (true :: node))

/-- Internal liveness always emits exactly one Boolean flag. -/
@[simp] theorem routingLiveNodeFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : (routingLiveNodeFlag ruler P S node).length = 1 := by
  rw [routingLiveNodeFlag_value]
  rfl

/-- Liveness charges native seeded queries and the complete tagged node word. -/
@[fun_prop] theorem routingLiveNodeFlagUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingLiveNodeFlag (ruler z) (P (seed z)) (S (seed z)) (node z)) enc encBits := by
  unfold routingLiveNodeFlag
  fun_prop

/-- Image the horizontal field of an interior node; original vertices stay on column zero. -/
def routingNodeImageXBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  if node.headD false then
    (routingImageXBits ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node)) else []

/-- Image the vertical field of an interior node; original vertices retain their row. -/
def routingNodeImageYBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  if node.headD false then
    (routingImageYBits ruler P S (routingNodeOwnerBits node)
      (routingNodeXBits node) (routingNodeYBits node))
    else routingSixBits (routingNodeOwnerBits node)

/-- Horizontal node imaging agrees with the natural geometric realization on every word. -/
theorem routingNodeImageXBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : lsbValue (routingNodeImageXBits ruler P S node) =
      (routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node)).1 := by
  cases node with
  | nil => rfl
  | cons tag node =>
    cases tag with
    | false => rfl
    | true =>
      simp [routingNodeImageXBits, routingDecodeNodeBits,
        routingImageXBits_value, routedCoordinate]

/-- Vertical node imaging agrees with the natural geometric realization on every word. -/
theorem routingNodeImageYBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : lsbValue (routingNodeImageYBits ruler P S node) =
      (routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node)).2 := by
  cases node with
  | nil => rfl
  | cons tag node => cases tag <;>
      simp [routingNodeImageYBits, routingDecodeNodeBits,
        routingImageYBits_value, routingSixBits_value, routedCoordinate, vertexPoint]

/-- Both image fields form precisely the natural coordinate of the decoded internal node. -/
theorem routingNodeImage_value (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) :
    (lsbValue (routingNodeImageXBits ruler P S node),
      lsbValue (routingNodeImageYBits ruler P S node)) =
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) :=
  Prod.ext (routingNodeImageXBits_value ruler P S node) (routingNodeImageYBits_value ruler P S node)

/-- Switch an interior owner without changing its raw coordinates; vertices retain their word. -/
def routingNodeSwitchBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  if node.headD false then
    (routingInteriorNodeBits
      (routingSwitchOwnerBits ruler P S (routingNodeOwnerBits node)
        (routingNodeXBits node) (routingNodeYBits node))
      (routingNodeXBits node) (routingNodeYBits node)) else node

/-- Node switching decodes to the exact natural crossing involution on every word. -/
theorem routingNodeSwitchBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : routingDecodeNodeBits (routingNodeSwitchBits ruler P S node) =
      routedSwitch (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) := by
  cases node with
  | nil => rfl
  | cons tag node =>
    cases tag
    · simp [routingNodeSwitchBits, routingDecodeNodeBits, routedSwitch]
    · have hd : routingDecodeNodeBits (true :: node) =
          .inr (lsbValue (routingNodeOwnerBits (true :: node)),
            (lsbValue (routingNodeXBits (true :: node)),
              lsbValue (routingNodeYBits (true :: node)))) := by
        simp [routingDecodeNodeBits]
      rw [hd]
      simpa [routingNodeSwitchBits] using
        (routingSwitchOwnerBits_value ruler P S (routingNodeOwnerBits (true :: node))
          (routingNodeXBits (true :: node)) (routingNodeYBits (true :: node))).symm

/-- Horizontal node imaging charges native seeded queries and raw field decoding. -/
@[fun_prop] theorem routingNodeImageXBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingNodeImageXBits (ruler z) (P (seed z)) (S (seed z)) (node z)) enc encBits := by
  unfold routingNodeImageXBits
  fun_prop

/-- Vertical node imaging charges native seeded queries and exact row arithmetic. -/
@[fun_prop] theorem routingNodeImageYBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingNodeImageYBits (ruler z) (P (seed z)) (S (seed z)) (node z)) enc encBits := by
  unfold routingNodeImageYBits
  fun_prop

/-- Node switching has native costs on every internal word. -/
@[fun_prop] theorem routingNodeSwitchBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingNodeSwitchBits (ruler z) (P (seed z)) (S (seed z)) (node z)) enc encBits := by
  unfold routingNodeSwitchBits
  fun_prop

end GameTheory.Complexity.Backend
