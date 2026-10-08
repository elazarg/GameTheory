import GameTheoryComplexity.Backend.GridRoutingQueries
import GameTheoryComplexity.Backend.GridRoutingGeometryMachine

/-! Internal routing nodes carry a vertex/interior tag and framed binary fields.
Owners and coordinates retain their complete words until a liveness check;
only the external point codec imposes a fixed coordinate width. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

/-- An original vertex carries its raw label behind the vertex tag. -/
def routingVertexNodeBits (owner : List Bool) : List Bool := false :: owner

/-- An interior occurrence carries its owner and both raw coordinates. -/
def routingInteriorNodeBits (owner x y : List Bool) : List Bool :=
  true :: pair owner (pair x y)

/-- Extract the complete owner field, allowing either internal node tag. -/
def routingNodeOwnerBits (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node) (pairFst node.tail) node.tail

/-- Extract the horizontal coordinate; original vertices lie on column zero. -/
def routingNodeXBits (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node) (pairFst (pairSnd node.tail)) []

/-- Extract the vertical coordinate, computing original vertex rows exactly. -/
def routingNodeYBits (node : List Bool) : List Bool :=
  caseBit₀ (bitAt [] node) (pairSnd (pairSnd node.tail))
    (routingSixBits (routingNodeOwnerBits node))

/-- Interpret an internal node word without narrowing its numeric fields. -/
def routingDecodeNodeBits (node : List Bool) : WireNode :=
  if (node.head?).getD false then
    .inr (Nat.fromBitsLE (routingNodeOwnerBits node),
      (Nat.fromBitsLE (routingNodeXBits node), Nat.fromBitsLE (routingNodeYBits node)))
  else .inl (Nat.fromBitsLE (routingNodeOwnerBits node))

/-- Vertex construction has exact natural-node semantics on every label word. -/
@[simp] theorem routingDecodeNodeBits_vertex (owner : List Bool) :
    routingDecodeNodeBits (routingVertexNodeBits owner) = .inl (Nat.fromBitsLE owner) := by
  simp [routingDecodeNodeBits, routingVertexNodeBits, routingNodeOwnerBits, bitAt_eq, bitOf,
    caseBit₀]

/-- Interior construction retains exact owners and coordinates at arbitrary widths. -/
@[simp] theorem routingDecodeNodeBits_interior (owner x y : List Bool) :
    routingDecodeNodeBits (routingInteriorNodeBits owner x y) =
      .inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  simp [routingDecodeNodeBits, routingInteriorNodeBits, routingNodeOwnerBits,
    routingNodeXBits, routingNodeYBits, bitAt_eq, bitOf, caseBit₀]

/-- Extracted coordinates agree with the canonical semantic node point. -/
theorem routingNodePoint_value (node : List Bool) :
    (Nat.fromBitsLE (routingNodeXBits node), Nat.fromBitsLE (routingNodeYBits node)) =
      wireNodePoint (routingDecodeNodeBits node) := by
  cases node with
  | nil => rfl
  | cons tag node =>
      cases tag
      · simp [routingDecodeNodeBits, routingNodeOwnerBits, routingNodeXBits,
          routingNodeYBits, bitAt_eq, bitOf, caseBit₀, wireNodePoint, vertexPoint,
          routingSixBits_value]
        rfl
      · simp [routingDecodeNodeBits, routingNodeOwnerBits, routingNodeXBits,
          routingNodeYBits, bitAt_eq, bitOf, caseBit₀, wireNodePoint]

/-- Vertex construction composes any polynomial-time owner producer. -/
theorem routingVertexNodeBitsFn_mem_FP {owner : List Bool → List Bool} (ho : owner ∈ FP) :
    (fun z => routingVertexNodeBits (owner z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.comp (.bit false) (fun _ => FP_subset_CobhamFP ho)

/-- Interior construction composes polynomial-time raw field producers. -/
theorem routingInteriorNodeBitsFn_mem_FP {owner x y : List Bool → List Bool}
    (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingInteriorNodeBits (owner z) (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.comp (.bit true)
    (fun _ => FP_subset_CobhamFP (pairFn_mem_FP ho (pairFn_mem_FP hx hy)))

private theorem nodeTailFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => (node z).tail) ∈ FP :=
  CobhamFP_subset_FP (tailFn (FP_subset_CobhamFP hn))

private theorem nodeTagFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => bitAt [] (node z)) ∈ FP :=
  CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hn))

/-- Owner extraction is polynomial-time on every internal word. -/
theorem routingNodeOwnerBitsFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => routingNodeOwnerBits (node z)) ∈ FP := by
  have ht := nodeTailFn_mem_FP hn
  exact selectFn_mem_FP (nodeTagFn_mem_FP hn) (mem_FP_comp ht pairFst_mem_FP) ht

/-- Horizontal-coordinate extraction is polynomial-time on every internal word. -/
theorem routingNodeXBitsFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => routingNodeXBits (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (mem_FP_comp (mem_FP_comp (nodeTailFn_mem_FP hn) pairSnd_mem_FP) pairFst_mem_FP)
    (constFn_mem_FP [])

/-- Vertical-coordinate extraction composes framing with exact vertex-row construction. -/
theorem routingNodeYBitsFn_mem_FP {node : List Bool → List Bool} (hn : node ∈ FP) :
    (fun z => routingNodeYBits (node z)) ∈ FP :=
  selectFn_mem_FP (nodeTagFn_mem_FP hn)
    (mem_FP_comp (mem_FP_comp (nodeTailFn_mem_FP hn) pairSnd_mem_FP) pairSnd_mem_FP)
    (routingSixBitsFn_mem_FP (routingNodeOwnerBitsFn_mem_FP hn))

end GameTheory.Complexity.Backend
