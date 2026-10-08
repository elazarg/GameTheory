import GameTheoryComplexity.Backend.GridRoutingNodeMachine
import GameTheoryComplexity.Backend.GridRoutingWireMachine
import GameTheoryComplexity.Backend.GridRoutingWords

/-! Guarded internal node steps follow active source-indexed wires and rejoin
their original vertices. Idle labels retain their complete raw word. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

private def vertexCoordinateFlag (owner x y : List Bool) : List Bool :=
  andBit (routingEQFlag x []) (routingEQFlag y (routingSixBits owner))

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    caseBit₀ [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, caseBit₀]

private theorem vertexCoordinateFlag_value (owner x y : List Bool) :
    vertexCoordinateFlag owner x y = [decide
      ((Nat.fromBitsLE x, Nat.fromBitsLE y) = vertexPoint (Nat.fromBitsLE owner))] := by
  simp only [vertexCoordinateFlag, routingEQFlag_value, routingSixBits_value, flagAnd_decide]
  congr 2
  apply propext
  simp only [vertexPoint, Prod.mk.injEq, show Nat.fromBitsLE [] = 0 from rfl]

private def embedNodeBits (owner target x y : List Bool) : List Bool :=
  caseBit₀ (vertexCoordinateFlag owner x y) (routingVertexNodeBits owner)
    (caseBit₀ (vertexCoordinateFlag target x y) (routingVertexNodeBits target)
      (routingInteriorNodeBits owner x y))

private theorem embedNodeBits_decode (owner target x y : List Bool) (S : ℕ → ℕ)
    (ht : Nat.fromBitsLE target = S (Nat.fromBitsLE owner)) :
    routingDecodeNodeBits (embedNodeBits owner target x y) =
      embedWire S (Nat.fromBitsLE owner) (Nat.fromBitsLE x, Nat.fromBitsLE y) := by
  simp only [embedNodeBits, vertexCoordinateFlag_value, select_decide, embedWire, ← ht]
  split_ifs <;> simp_all only [routingDecodeNodeBits_vertex, routingDecodeNodeBits_interior]

private def wireStepNodeBits (ruler owner target x y : List Bool) (incoming : Bool) : List Bool :=
  let point := routingWireStepBits ruler owner target x y incoming
  embedNodeBits owner target (routingPointXBits ruler point) (routingPointYBits ruler point)

private theorem wireStep_onWire {n i j : ℕ} {p : ℕ × ℕ} (incoming : Bool)
    (hi : i < n) (hne : i ≠ j) (hp : onWire n i j p) :
    onWire n i j (if incoming then wirePredecessor n i j p else wireSuccessor n i j p) := by
  cases incoming
  · change onWire n i j (wireSuccessor n i j p)
    by_cases hs : wireSuccessor n i j p = p
    · simpa only [Bool.false_eq_true, ite_false, hs] using hp
    · have hb := wire_successor_consistent hi hne p hs
      exact ((wirePredecessor_ne_iff hi hne _).mp
        (by rw [hb]; exact Ne.symm hs)).1
  · change onWire n i j (wirePredecessor n i j p)
    by_cases hs : wirePredecessor n i j p = p
    · simpa only [ite_true, hs] using hp
    · have hb := wire_predecessor_consistent hi hne p hs
      exact ((wireSuccessor_ne_iff hi hne _).mp
        (by rw [hb]; exact Ne.symm hs)).1

private theorem wireStepNodeBits_decode (ruler owner target x y : List Bool)
    (incoming : Bool) (P S : ℕ → ℕ)
    (ha : activeEdge (2 ^ ruler.length) P S (Nat.fromBitsLE owner))
    (ht : Nat.fromBitsLE target = S (Nat.fromBitsLE owner))
    (hp : onWire (2 ^ ruler.length) (Nat.fromBitsLE owner) (Nat.fromBitsLE target)
      (Nat.fromBitsLE x, Nat.fromBitsLE y)) :
    routingDecodeNodeBits (wireStepNodeBits ruler owner target x y incoming) =
      embedWire S (Nat.fromBitsLE owner)
        (if incoming then wirePredecessor (2 ^ ruler.length) (Nat.fromBitsLE owner)
          (Nat.fromBitsLE target) (Nat.fromBitsLE x, Nat.fromBitsLE y)
        else wireSuccessor (2 ^ ruler.length) (Nat.fromBitsLE owner)
          (Nat.fromBitsLE target) (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  let q := if incoming then wirePredecessor (2 ^ ruler.length) (Nat.fromBitsLE owner)
      (Nat.fromBitsLE target) (Nat.fromBitsLE x, Nat.fromBitsLE y)
    else wireSuccessor (2 ^ ruler.length) (Nat.fromBitsLE owner)
      (Nat.fromBitsLE target) (Nat.fromBitsLE x, Nat.fromBitsLE y)
  have hne : Nat.fromBitsLE owner ≠ Nat.fromBitsLE target := by rw [ht]; exact ha.2.2.1.symm
  have hq := wireStep_onWire incoming ha.1 hne hp
  have hb := onWire_bounds ha.1 (by rw [ht]; exact ha.2.1) hq
  have hx : q.1 < 2 ^ routingCoordinateWidth ruler.length :=
    hb.1.trans_le (routingCoordinateCapacity ruler.length).1
  have hy : q.2 < 2 ^ routingCoordinateWidth ruler.length :=
    hb.2.trans_le (routingCoordinateCapacity ruler.length).2
  simp only [wireStepNodeBits, routingWireStepBits_eq_encode]
  change routingDecodeNodeBits (embedNodeBits owner target
    (routingPointXBits ruler (encodeRoutingPoint ruler.length q))
    (routingPointYBits ruler (encodeRoutingPoint ruler.length q))) = _
  rw [embedNodeBits_decode owner target _ _ S ht, routingPointXBits_encode,
    routingPointYBits_encode, Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hy]

private def incomingVertexFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (owner : List Bool) : List Bool :=
  let prev := routingQueryBits ruler P owner
  andBit (routingActiveEdgeFlag ruler P S prev)
    (routingEQFlag (routingQueryBits ruler S prev) owner)

private theorem incomingVertexFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner : List Bool) : incomingVertexFlag ruler P S owner = [decide
      (activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S)
          (routingOriginalPointer ruler P (Nat.fromBitsLE owner)) ∧
        routingOriginalPointer ruler S (routingOriginalPointer ruler P (Nat.fromBitsLE owner)) =
          Nat.fromBitsLE owner)] := by
  simp only [incomingVertexFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingQueryBits_value, flagAnd_decide]

/-- Follow the original routed predecessor or successor of an internal node word. -/
def routingNodeStepBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) (incoming : Bool) : List Bool :=
  let owner := routingNodeOwnerBits node
  let next := routingQueryBits ruler S owner
  let interior := caseBit₀ (routingLiveInteriorFlag ruler P S owner
      (routingNodeXBits node) (routingNodeYBits node))
    (wireStepNodeBits ruler owner next (routingNodeXBits node) (routingNodeYBits node) incoming)
    node
  let vertex := if incoming then
      caseBit₀ (incomingVertexFlag ruler P S owner)
        (wireStepNodeBits ruler (routingQueryBits ruler P owner) owner []
          (routingSixBits owner) true) node
    else caseBit₀ (routingActiveEdgeFlag ruler P S owner)
      (wireStepNodeBits ruler owner next [] (routingSixBits owner) false) node
  caseBit₀ (bitAt [] node) interior vertex

private theorem interiorStep_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node owner x y : List Bool) (incoming : Bool)
    (hd : routingDecodeNodeBits node =
      .inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y))) :
    routingDecodeNodeBits (caseBit₀ (routingLiveInteriorFlag ruler P S owner x y)
      (wireStepNodeBits ruler owner (routingQueryBits ruler S owner) x y incoming) node) =
      (if incoming then routedPredecessor else routedSuccessor) (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (.inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y))) := by
  simp only [routingLiveInteriorFlag_value, select_decide]
  by_cases hl : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S)
      (.inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y)))
  · rw [ite_eq_left hl]
    have hp : onWire (2 ^ ruler.length) (Nat.fromBitsLE owner)
        (Nat.fromBitsLE (routingQueryBits ruler S owner)) (Nat.fromBitsLE x, Nat.fromBitsLE y) := by
      rw [routingQueryBits_value]
      exact hl.2.1
    have hs := wireStepNodeBits_decode ruler owner (routingQueryBits ruler S owner) x y
      incoming (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
      hl.1 (routingQueryBits_value ruler S owner) hp
    cases incoming <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
      routedPredecessor, routedSuccessor, ite_eq_left hl, routingQueryBits_value] using hs
  · cases incoming <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      routedPredecessor, routedSuccessor, ite_eq_right hl, hd]

private theorem outgoingVertexStep_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node owner : List Bool) (hd : routingDecodeNodeBits node = .inl (Nat.fromBitsLE owner)) :
    routingDecodeNodeBits (caseBit₀ (routingActiveEdgeFlag ruler P S owner)
      (wireStepNodeBits ruler owner (routingQueryBits ruler S owner) []
        (routingSixBits owner) false) node) =
      routedSuccessor (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (.inl (Nat.fromBitsLE owner)) := by
  simp only [routingActiveEdgeFlag_value, select_decide, routedSuccessor]
  by_cases ha : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (Nat.fromBitsLE owner)
  · rw [ite_eq_left ha]
    have hp : onWire (2 ^ ruler.length) (Nat.fromBitsLE owner)
        (Nat.fromBitsLE (routingQueryBits ruler S owner))
        (Nat.fromBitsLE [], Nat.fromBitsLE (routingSixBits owner)) := by
      rw [routingSixBits_value]
      exact Or.inl ⟨rfl, Nat.zero_le _⟩
    simpa only [Bool.false_eq_true, ite_false, ite_eq_left ha,
      routingQueryBits_value, routingSixBits_value,
      show Nat.fromBitsLE [] = 0 from rfl, vertexPoint] using
      wireStepNodeBits_decode ruler owner (routingQueryBits ruler S owner) []
        (routingSixBits owner) false (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) ha (routingQueryBits_value ruler S owner) hp
  · simp only [ite_eq_right ha, hd]

private theorem incomingVertexStep_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node owner : List Bool) (hd : routingDecodeNodeBits node = .inl (Nat.fromBitsLE owner)) :
    routingDecodeNodeBits (caseBit₀ (incomingVertexFlag ruler P S owner)
      (wireStepNodeBits ruler (routingQueryBits ruler P owner) owner []
        (routingSixBits owner) true) node) =
      routedPredecessor (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (.inl (Nat.fromBitsLE owner)) := by
  simp only [incomingVertexFlag_value, select_decide, routedPredecessor]
  by_cases ha : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingOriginalPointer ruler P (Nat.fromBitsLE owner)) ∧
      routingOriginalPointer ruler S (routingOriginalPointer ruler P (Nat.fromBitsLE owner)) =
        Nat.fromBitsLE owner
  · rw [ite_eq_left ha]
    have hactive : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (Nat.fromBitsLE (routingQueryBits ruler P owner)) := by
      rw [routingQueryBits_value]
      exact ha.1
    have ht : Nat.fromBitsLE owner = routingOriginalPointer ruler S
        (Nat.fromBitsLE (routingQueryBits ruler P owner)) := by
      rw [routingQueryBits_value]
      exact ha.2.symm
    have hp : onWire (2 ^ ruler.length) (Nat.fromBitsLE (routingQueryBits ruler P owner))
        (Nat.fromBitsLE owner) (Nat.fromBitsLE [], Nat.fromBitsLE (routingSixBits owner)) := by
      rw [routingSixBits_value]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl, by omega⟩))
    simpa only [ite_true, ite_eq_left ha, routingQueryBits_value, routingSixBits_value,
      show Nat.fromBitsLE [] = 0 from rfl, vertexPoint] using
      wireStepNodeBits_decode ruler (routingQueryBits ruler P owner) owner []
        (routingSixBits owner) true (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) hactive ht hp
  · simp only [ite_eq_right ha, hd]

/-- Every binary node step decodes to the exact total original routed pointer. -/
theorem routingNodeStepBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) (incoming : Bool) :
    routingDecodeNodeBits (routingNodeStepBits ruler P S node incoming) =
      (if incoming then routedPredecessor else routedSuccessor) (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (routingDecodeNodeBits node) := by
  cases node with
  | nil =>
    cases incoming
    · exact outgoingVertexStep_decode ruler P S [] (routingNodeOwnerBits []) rfl
    · exact incomingVertexStep_decode ruler P S [] (routingNodeOwnerBits []) rfl
  | cons tag node =>
    cases tag
    · cases incoming
      · exact outgoingVertexStep_decode ruler P S (false :: node)
          (routingNodeOwnerBits (false :: node)) rfl
      · exact incomingVertexStep_decode ruler P S (false :: node)
          (routingNodeOwnerBits (false :: node)) rfl
    · exact interiorStep_decode ruler P S (true :: node)
        (routingNodeOwnerBits (true :: node)) (routingNodeXBits (true :: node))
        (routingNodeYBits (true :: node)) incoming rfl

private theorem vertexCoordinateFlagFn_mem_FP {owner x y : List Bool → List Bool}
    (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => vertexCoordinateFlag (owner z) (x z) (y z)) ∈ FP :=
  andBitFn_mem_FP (routingEQFlagFn_mem_FP hx (constFn_mem_FP []))
    (routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP ho))

private theorem embedNodeBitsFn_mem_FP {owner target x y : List Bool → List Bool}
    (ho : owner ∈ FP) (ht : target ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => embedNodeBits (owner z) (target z) (x z) (y z)) ∈ FP :=
  selectFn_mem_FP (vertexCoordinateFlagFn_mem_FP ho hx hy) (routingVertexNodeBitsFn_mem_FP ho)
    (selectFn_mem_FP (vertexCoordinateFlagFn_mem_FP ht hx hy) (routingVertexNodeBitsFn_mem_FP ht)
      (routingInteriorNodeBitsFn_mem_FP ho hx hy))

private theorem wireStepNodeBitsFn_mem_FP (incoming : Bool)
    {ruler owner target x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (ho : owner ∈ FP) (ht : target ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => wireStepNodeBits (ruler z) (owner z) (target z) (x z) (y z) incoming) ∈ FP := by
  have hpoint := routingWireStepBitsFn_mem_FP incoming hr ho ht hx hy
  exact embedNodeBitsFn_mem_FP ho ht (routingPointXBitsFn_mem_FP hr hpoint)
    (routingPointYBitsFn_mem_FP hr hpoint)

private theorem incomingVertexFlagUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool) {ruler seed owner : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => incomingVertexFlag (ruler z) (P (seed z)) (S (seed z)) (owner z)) ∈ FP := by
  have hprev := routingQueryBitsUniformFn_mem_FP P hr hs ho hP
  have hnext := routingQueryBitsUniformFn_mem_FP S hr hs hprev hS
  exact andBitFn_mem_FP (routingActiveEdgeFlagUniformFn_mem_FP P S hr hs hprev hP hS)
    (routingEQFlagFn_mem_FP hnext ho)

private theorem taggedSelectFn_mem_FP {tag yes no : List Bool → List Bool}
    (ht : tag ∈ FP) (hy : yes ∈ FP) (hn : no ∈ FP) :
    (fun z => caseBit₀ (bitAt [] (tag z)) (yes z) (no z)) ∈ FP :=
  selectFn_mem_FP (CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP ht))) hy hn

/-- Original routed node steps compose seeded polynomial-time queries and raw node producers. -/
theorem routingNodeStepBitsUniformFn_mem_FP (incoming : Bool)
    (P S : List Bool → List Bool → List Bool) {ruler seed node : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingNodeStepBits (ruler z) (P (seed z))
      (S (seed z)) (node z) incoming) ∈ FP := by
  let owner := fun z => routingNodeOwnerBits (node z)
  let x := fun z => routingNodeXBits (node z)
  let y := fun z => routingNodeYBits (node z)
  let next := fun z => routingQueryBits (ruler z) (S (seed z)) (owner z)
  have ho : owner ∈ FP := routingNodeOwnerBitsFn_mem_FP hn
  have hx : x ∈ FP := routingNodeXBitsFn_mem_FP hn
  have hy : y ∈ FP := routingNodeYBitsFn_mem_FP hn
  have hnext : next ∈ FP := routingQueryBitsUniformFn_mem_FP S hr hs ho hS
  let interiorFlag := fun z =>
    routingLiveInteriorFlag (ruler z) (P (seed z)) (S (seed z)) (owner z) (x z) (y z)
  let interiorStep := fun z => wireStepNodeBits (ruler z) (owner z) (next z) (x z) (y z) incoming
  let interior := fun z => caseBit₀ (interiorFlag z) (interiorStep z) (node z)
  have hflag : interiorFlag ∈ FP := routingLiveInteriorFlagUniformFn_mem_FP P S hr hs ho hx hy hP hS
  have hstep : interiorStep ∈ FP := wireStepNodeBitsFn_mem_FP incoming hr ho hnext hx hy
  have hinterior : interior ∈ FP :=
    selectFn_mem_FP (flag := interiorFlag) (yes := interiorStep) (no := node) hflag hstep hn
  have hzero := constFn_mem_FP ([] : List Bool)
  have hrow := routingSixBitsFn_mem_FP ho
  cases incoming
  · let vertexFlag := fun z => routingActiveEdgeFlag (ruler z) (P (seed z)) (S (seed z)) (owner z)
    let vertexStep := fun z =>
      wireStepNodeBits (ruler z) (owner z) (next z) [] (routingSixBits (owner z)) false
    let vertex := fun z => caseBit₀ (vertexFlag z) (vertexStep z) (node z)
    have hvflag : vertexFlag ∈ FP := routingActiveEdgeFlagUniformFn_mem_FP P S hr hs ho hP hS
    have hvstep : vertexStep ∈ FP := wireStepNodeBitsFn_mem_FP false hr ho hnext hzero hrow
    have hvertex : vertex ∈ FP :=
      selectFn_mem_FP (flag := vertexFlag) (yes := vertexStep) (no := node) hvflag hvstep hn
    have he : (fun z => routingNodeStepBits (ruler z) (P (seed z)) (S (seed z)) (node z) false) =
        (fun z => caseBit₀ (bitAt [] (node z)) (interior z) (vertex z)) := rfl
    rw [he]
    exact taggedSelectFn_mem_FP hn hinterior hvertex
  · let prev := fun z => routingQueryBits (ruler z) (P (seed z)) (owner z)
    let vertexFlag := fun z => incomingVertexFlag (ruler z) (P (seed z)) (S (seed z)) (owner z)
    let vertexStep := fun z =>
      wireStepNodeBits (ruler z) (prev z) (owner z) [] (routingSixBits (owner z)) true
    let vertex := fun z => caseBit₀ (vertexFlag z) (vertexStep z) (node z)
    have hprev : prev ∈ FP := routingQueryBitsUniformFn_mem_FP P hr hs ho hP
    have hvflag : vertexFlag ∈ FP := incomingVertexFlagUniformFn_mem_FP P S hr hs ho hP hS
    have hvstep : vertexStep ∈ FP := wireStepNodeBitsFn_mem_FP true hr hprev ho hzero hrow
    have hvertex : vertex ∈ FP :=
      selectFn_mem_FP (flag := vertexFlag) (yes := vertexStep) (no := node) hvflag hvstep hn
    have he : (fun z => routingNodeStepBits (ruler z) (P (seed z)) (S (seed z)) (node z) true) =
        (fun z => caseBit₀ (bitAt [] (node z)) (interior z) (vertex z)) := rfl
    rw [he]
    exact taggedSelectFn_mem_FP hn hinterior hvertex

end GameTheory.Complexity.Backend
