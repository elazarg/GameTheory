module

public import GameTheoryComplexity.Backend.GridRoutingNodeMachine
public import GameTheoryComplexity.Backend.GridRoutingWireMachine
public import GameTheoryComplexity.Backend.GridRoutingWords

@[expose] public section

/-! Guarded internal node steps follow active source-indexed wires and rejoin
their original vertices. Idle labels retain their complete raw word. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- Check whether raw coordinates name the original owner vertex. -/
def routingVertexCoordinateFlag (owner x y : List Bool) : List Bool :=
  andFlag (routingEQFlag x []) (routingEQFlag y (routingSixBits owner))

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    select [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, select]

private theorem vertexCoordinateFlag_value (owner x y : List Bool) :
    routingVertexCoordinateFlag owner x y = [decide
      ((lsbValue x, lsbValue y) = vertexPoint (lsbValue owner))] := by
  simp only [routingVertexCoordinateFlag, routingEQFlag_value, routingSixBits_value, flagAnd_decide]
  congr 2
  apply propext
  simp only [vertexPoint, Prod.mk.injEq, show lsbValue [] = 0 from rfl]

/-- Join the two original endpoint representations to their wire interior. -/
def routingEmbedNodeBits (owner target x y : List Bool) : List Bool :=
  select (routingVertexCoordinateFlag owner x y) (routingVertexNodeBits owner)
    (select (routingVertexCoordinateFlag target x y) (routingVertexNodeBits target)
      (routingInteriorNodeBits owner x y))

private theorem embedNodeBits_decode (owner target x y : List Bool) (S : ℕ → ℕ)
    (ht : lsbValue target = S (lsbValue owner)) :
    routingDecodeNodeBits (routingEmbedNodeBits owner target x y) =
      embedWire S (lsbValue owner) (lsbValue x, lsbValue y) := by
  simp only [routingEmbedNodeBits, vertexCoordinateFlag_value, select_decide, embedWire, ← ht]
  split_ifs <;> simp_all only [routingDecodeNodeBits_vertex, routingDecodeNodeBits_interior]

/-- Follow a single wire and retain the exact tagged node representation. -/
def routingWireStepNodeBits (ruler owner target x y : List Bool) (incoming : Bool) : List Bool :=
  let point := routingWireStepBits ruler owner target x y incoming
  routingEmbedNodeBits owner target (routingPointXBits ruler point) (routingPointYBits ruler point)

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
    (ha : activeEdge (2 ^ ruler.length) P S (lsbValue owner))
    (ht : lsbValue target = S (lsbValue owner))
    (hp : onWire (2 ^ ruler.length) (lsbValue owner) (lsbValue target)
      (lsbValue x, lsbValue y)) :
    routingDecodeNodeBits (routingWireStepNodeBits ruler owner target x y incoming) =
      embedWire S (lsbValue owner)
        (if incoming then wirePredecessor (2 ^ ruler.length) (lsbValue owner)
          (lsbValue target) (lsbValue x, lsbValue y)
        else wireSuccessor (2 ^ ruler.length) (lsbValue owner)
          (lsbValue target) (lsbValue x, lsbValue y)) := by
  let q := if incoming then wirePredecessor (2 ^ ruler.length) (lsbValue owner)
      (lsbValue target) (lsbValue x, lsbValue y)
    else wireSuccessor (2 ^ ruler.length) (lsbValue owner)
      (lsbValue target) (lsbValue x, lsbValue y)
  have hne : lsbValue owner ≠ lsbValue target := by rw [ht]; exact ha.2.2.1.symm
  have hq := wireStep_onWire incoming ha.1 hne hp
  have hb := onWire_bounds ha.1 (by rw [ht]; exact ha.2.1) hq
  have hx : q.1 < 2 ^ routingCoordinateWidth ruler.length :=
    hb.1.trans_le (routingCoordinateCapacity ruler.length).1
  have hy : q.2 < 2 ^ routingCoordinateWidth ruler.length :=
    hb.2.trans_le (routingCoordinateCapacity ruler.length).2
  simp only [routingWireStepNodeBits, routingWireStepBits_eq_encode]
  change routingDecodeNodeBits (routingEmbedNodeBits owner target
    (routingPointXBits ruler (encodeRoutingPoint ruler.length q))
    (routingPointYBits ruler (encodeRoutingPoint ruler.length q))) = _
  rw [embedNodeBits_decode owner target _ _ S ht, routingPointXBits_encode,
    routingPointYBits_encode, lsbValue_lowBits hx, lsbValue_lowBits hy]

/-- Check that the predecessor query identifies a consistent incoming edge. -/
def routingIncomingVertexFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (owner : List Bool) : List Bool :=
  let prev := routingQueryBits ruler P owner
  andFlag (routingActiveEdgeFlag ruler P S prev)
    (routingEQFlag (routingQueryBits ruler S prev) owner)

private theorem incomingVertexFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner : List Bool) : routingIncomingVertexFlag ruler P S owner = [decide
      (activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S)
          (routingOriginalPointer ruler P (lsbValue owner)) ∧
        routingOriginalPointer ruler S (routingOriginalPointer ruler P (lsbValue owner)) =
          lsbValue owner)] := by
  simp only [routingIncomingVertexFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingQueryBits_value, flagAnd_decide]

/-- Follow the original routed predecessor or successor of an internal node word. -/
def routingNodeStepBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) (incoming : Bool) : List Bool :=
  let owner := routingNodeOwnerBits node
  let next := routingQueryBits ruler S owner
  let interior := select (routingLiveInteriorFlag ruler P S owner
      (routingNodeXBits node) (routingNodeYBits node))
    (routingWireStepNodeBits ruler owner next (routingNodeXBits node) (routingNodeYBits node) incoming)
    node
  let vertex := if incoming then
      select (routingIncomingVertexFlag ruler P S owner)
        (routingWireStepNodeBits ruler (routingQueryBits ruler P owner) owner []
          (routingSixBits owner) true) node
    else select (routingActiveEdgeFlag ruler P S owner)
      (routingWireStepNodeBits ruler owner next [] (routingSixBits owner) false) node
  select [node.headD false] interior vertex

private theorem interiorStep_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node owner x y : List Bool) (incoming : Bool)
    (hd : routingDecodeNodeBits node =
      .inr (lsbValue owner, (lsbValue x, lsbValue y))) :
    routingDecodeNodeBits (select (routingLiveInteriorFlag ruler P S owner x y)
      (routingWireStepNodeBits ruler owner (routingQueryBits ruler S owner) x y incoming) node) =
      (if incoming then routedPredecessor else routedSuccessor) (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (.inr (lsbValue owner, (lsbValue x, lsbValue y))) := by
  simp only [routingLiveInteriorFlag_value, select_decide]
  by_cases hl : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S)
      (.inr (lsbValue owner, (lsbValue x, lsbValue y)))
  · rw [ite_eq_left hl]
    have hp : onWire (2 ^ ruler.length) (lsbValue owner)
        (lsbValue (routingQueryBits ruler S owner)) (lsbValue x, lsbValue y) := by
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
    (node owner : List Bool) (hd : routingDecodeNodeBits node = .inl (lsbValue owner)) :
    routingDecodeNodeBits (select (routingActiveEdgeFlag ruler P S owner)
      (routingWireStepNodeBits ruler owner (routingQueryBits ruler S owner) []
        (routingSixBits owner) false) node) =
      routedSuccessor (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (.inl (lsbValue owner)) := by
  simp only [routingActiveEdgeFlag_value, select_decide, routedSuccessor]
  by_cases ha : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (lsbValue owner)
  · rw [ite_eq_left ha]
    have hp : onWire (2 ^ ruler.length) (lsbValue owner)
        (lsbValue (routingQueryBits ruler S owner))
        (lsbValue [], lsbValue (routingSixBits owner)) := by
      rw [routingSixBits_value]
      exact Or.inl ⟨rfl, Nat.zero_le _⟩
    simpa only [Bool.false_eq_true, ite_false, ite_eq_left ha,
      routingQueryBits_value, routingSixBits_value,
      show lsbValue [] = 0 from rfl, vertexPoint] using
      wireStepNodeBits_decode ruler owner (routingQueryBits ruler S owner) []
        (routingSixBits owner) false (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) ha (routingQueryBits_value ruler S owner) hp
  · simp only [ite_eq_right ha, hd]

private theorem incomingVertexStep_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (node owner : List Bool) (hd : routingDecodeNodeBits node = .inl (lsbValue owner)) :
    routingDecodeNodeBits (select (routingIncomingVertexFlag ruler P S owner)
      (routingWireStepNodeBits ruler (routingQueryBits ruler P owner) owner []
        (routingSixBits owner) true) node) =
      routedPredecessor (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (.inl (lsbValue owner)) := by
  simp only [incomingVertexFlag_value, select_decide, routedPredecessor]
  by_cases ha : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingOriginalPointer ruler P (lsbValue owner)) ∧
      routingOriginalPointer ruler S (routingOriginalPointer ruler P (lsbValue owner)) =
        lsbValue owner
  · rw [ite_eq_left ha]
    have hactive : activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue (routingQueryBits ruler P owner)) := by
      rw [routingQueryBits_value]
      exact ha.1
    have ht : lsbValue owner = routingOriginalPointer ruler S
        (lsbValue (routingQueryBits ruler P owner)) := by
      rw [routingQueryBits_value]
      exact ha.2.symm
    have hp : onWire (2 ^ ruler.length) (lsbValue (routingQueryBits ruler P owner))
        (lsbValue owner) (lsbValue [], lsbValue (routingSixBits owner)) := by
      rw [routingSixBits_value]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl, by omega⟩))
    simpa only [ite_true, ite_eq_left ha, routingQueryBits_value, routingSixBits_value,
      show lsbValue [] = 0 from rfl, vertexPoint] using
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

@[fun_prop] theorem routingVertexCoordinateFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {owner x y : α → List Bool}
    (howner : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingVertexCoordinateFlag (owner z) (x z) (y z)) enc encBits := by
  exact andFlag_polyTime.comp ((routingEQFlag_polyTime hx (const [])).prod
    (routingEQFlag_polyTime hy (routingSixBits_polyTime howner)))

@[fun_prop] theorem routingEmbedNodeBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {owner target x y : α → List Bool}
    (howner : ComputableInPolyTime owner enc encBits)
    (htarget : ComputableInPolyTime target enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingEmbedNodeBits (owner z) (target z) (x z) (y z)) enc encBits := by
  exact select_polyTime.comp ((routingVertexCoordinateFlag_polyTime howner hx hy).prod
    ((routingVertexNodeBits_polyTime howner).prod
      (select_polyTime.comp ((routingVertexCoordinateFlag_polyTime htarget hx hy).prod
        ((routingVertexNodeBits_polyTime htarget).prod
          (routingInteriorNodeBits_polyTime howner hx hy))))))

@[fun_prop] theorem routingWireStepNodeBits_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler owner target x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (htarget : ComputableInPolyTime target enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingWireStepNodeBits (ruler z) (owner z) (target z) (x z) (y z) incoming) enc encBits := by
  have hpoint := routingWireStepBits_polyTime incoming hruler howner htarget hx hy
  exact routingEmbedNodeBits_polyTime howner htarget (routingPointXBits_polyTime hruler hpoint)
    (routingPointYBits_polyTime hruler hpoint)

/-- Incoming vertex validation charges both mutually consistent native queries. -/
@[fun_prop] theorem routingIncomingVertexFlagUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingIncomingVertexFlag (ruler z) (P (seed z)) (S (seed z)) (owner z)) enc encBits := by
  have hprev := routingQueryBitsUniform_polyTime P hruler hseed howner hP
  have hnext := routingQueryBitsUniform_polyTime S hruler hseed hprev hS
  exact andFlag_polyTime.comp
    ((routingActiveEdgeFlagUniform_polyTime P S hruler hseed hprev hP hS).prod
      (routingEQFlag_polyTime hnext howner))

/-- Guarded node steps charge the native seeded queries and every raw field. -/
@[fun_prop] theorem routingNodeStepBitsUniform_polyTime (incoming : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingNodeStepBits (ruler z) (P (seed z)) (S (seed z)) (node z) incoming) enc encBits := by
  have ho := routingNodeOwnerBits_polyTime hnode
  have hx := routingNodeXBits_polyTime hnode
  have hy := routingNodeYBits_polyTime hnode
  have hnext := routingQueryBitsUniform_polyTime S hruler hseed ho hS
  have hflag := routingLiveInteriorFlagUniform_polyTime P S hruler hseed ho hx hy hP hS
  have hstep := routingWireStepNodeBits_polyTime incoming hruler ho hnext hx hy
  have hinterior := select_polyTime.comp (hflag.prod (hstep.prod hnode))
  have hhead : ComputableInPolyTime (fun bits : List Bool => bits.headD false)
      encBits encBool := .headD false
  have htag := bitsCons (hhead.comp hnode) (const [])
  cases incoming
  · have hvflag := routingActiveEdgeFlagUniform_polyTime P S hruler hseed ho hP hS
    have hvstep := routingWireStepNodeBits_polyTime false hruler ho hnext (const [])
      (routingSixBits_polyTime ho)
    have hcert := select_polyTime.comp (htag.prod (hinterior.prod
      (select_polyTime.comp (hvflag.prod (hvstep.prod hnode)))))
    apply ComputableInPolyTime.of_tidy
    apply hcert.tidy.of_enc_eq
    intro z
    rfl
  · have hprev := routingQueryBitsUniform_polyTime P hruler hseed ho hP
    have hvflag := routingIncomingVertexFlagUniform_polyTime P S hruler hseed ho hP hS
    have hvstep := routingWireStepNodeBits_polyTime true hruler hprev ho (const [])
      (routingSixBits_polyTime ho)
    have hcert := select_polyTime.comp (htag.prod (hinterior.prod
      (select_polyTime.comp (hvflag.prod (hvstep.prod hnode)))))
    apply ComputableInPolyTime.of_tidy
    apply hcert.tidy.of_enc_eq
    intro z
    rfl

end GameTheory.Complexity.Backend
