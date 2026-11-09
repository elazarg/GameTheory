module

public import GameTheoryComplexity.Backend.CircuitWords
public import GameTheoryComplexity.Backend.GridRoutingQueries
public import GameTheoryComplexity.Backend.GridRoutingGeometryMachine

@[expose] public section

/-! Internal routing nodes carry a vertex/interior tag and framed binary fields.
Owners and coordinates retain their complete words until a liveness check;
only the external point codec imposes a fixed coordinate width. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- An original vertex carries its raw label behind the vertex tag. -/
def routingVertexNodeBits (owner : List Bool) : List Bool := false :: owner

/-- An interior occurrence carries its owner and both raw coordinates. -/
def routingInteriorNodeBits (owner x y : List Bool) : List Bool :=
  true :: CircuitWords.encodePair owner (CircuitWords.encodePair x y)

/-- Extract the complete owner field, allowing either internal node tag. -/
def routingNodeOwnerBits (node : List Bool) : List Bool :=
  if node.headD false then CircuitWords.first node.tail else node.tail

/-- Extract the horizontal coordinate; original vertices lie on column zero. -/
def routingNodeXBits (node : List Bool) : List Bool :=
  if node.headD false then CircuitWords.first (CircuitWords.rest node.tail) else []

/-- Extract the vertical coordinate, computing original vertex rows exactly. -/
def routingNodeYBits (node : List Bool) : List Bool :=
  if node.headD false then CircuitWords.rest (CircuitWords.rest node.tail)
  else routingSixBits (routingNodeOwnerBits node)

/-- Interpret an internal node word without narrowing its numeric fields. -/
def routingDecodeNodeBits (node : List Bool) : WireNode :=
  if node.headD false then
    .inr (lsbValue (routingNodeOwnerBits node),
      (lsbValue (routingNodeXBits node), lsbValue (routingNodeYBits node)))
  else .inl (lsbValue (routingNodeOwnerBits node))

/-- Vertex construction has exact natural-node semantics on every label word. -/
@[simp] theorem routingDecodeNodeBits_vertex (owner : List Bool) :
    routingDecodeNodeBits (routingVertexNodeBits owner) = .inl (lsbValue owner) := by
  simp [routingDecodeNodeBits, routingVertexNodeBits, routingNodeOwnerBits]

/-- Interior construction retains exact owners and coordinates at arbitrary widths. -/
@[simp] theorem routingDecodeNodeBits_interior (owner x y : List Bool) :
    routingDecodeNodeBits (routingInteriorNodeBits owner x y) =
      .inr (lsbValue owner, (lsbValue x, lsbValue y)) := by
  simp [routingDecodeNodeBits, routingInteriorNodeBits, routingNodeOwnerBits,
    routingNodeXBits, routingNodeYBits]

/-- Extracted coordinates agree with the canonical semantic node point. -/
theorem routingNodePoint_value (node : List Bool) :
    (lsbValue (routingNodeXBits node), lsbValue (routingNodeYBits node)) =
      wireNodePoint (routingDecodeNodeBits node) := by
  cases node with
  | nil => rfl
  | cons tag node =>
      cases tag
      · simp [routingDecodeNodeBits, routingNodeOwnerBits, routingNodeXBits,
          routingNodeYBits, wireNodePoint, vertexPoint,
          routingSixBits_value]
        rfl
      · simp [routingDecodeNodeBits, routingNodeOwnerBits, routingNodeXBits,
          routingNodeYBits, wireNodePoint]

/-- Vertex construction charges the complete owner word. -/
@[fun_prop] theorem routingVertexNodeBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {owner : α → List Bool}
    (ho : ComputableInPolyTime owner enc encBits) :
    ComputableInPolyTime (fun z => routingVertexNodeBits (owner z)) enc encBits :=
  bitsCons (const false) ho

/-- Interior construction charges the complete public framing of all three fields. -/
@[fun_prop] theorem routingInteriorNodeBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {owner x y : α → List Bool}
    (ho : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingInteriorNodeBits (owner z) (x z) (y z))
      enc encBits :=
  bitsCons (const true) (CircuitWords.encodePair_polyTime.comp
    (ho.prod (CircuitWords.encodePair_polyTime.comp (hx.prod hy))))

/-- Owner extraction has native machine costs on every internal word. -/
@[fun_prop] theorem routingNodeOwnerBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {node : α → List Bool}
    (hn : ComputableInPolyTime node enc encBits) :
    ComputableInPolyTime (fun z => routingNodeOwnerBits (node z)) enc encBits := by
  unfold routingNodeOwnerBits
  fun_prop

/-- Horizontal extraction charges total public frame decoding. -/
@[fun_prop] theorem routingNodeXBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {node : α → List Bool}
    (hn : ComputableInPolyTime node enc encBits) :
    ComputableInPolyTime (fun z => routingNodeXBits (node z)) enc encBits := by
  unfold routingNodeXBits
  fun_prop

/-- Vertical extraction charges frame decoding and exact original-vertex row computation. -/
@[fun_prop] theorem routingNodeYBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {node : α → List Bool}
    (hn : ComputableInPolyTime node enc encBits) :
    ComputableInPolyTime (fun z => routingNodeYBits (node z)) enc encBits := by
  unfold routingNodeYBits
  fun_prop

end GameTheory.Complexity.Backend
