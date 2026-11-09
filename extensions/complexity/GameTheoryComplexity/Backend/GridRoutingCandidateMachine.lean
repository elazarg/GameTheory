module

public import GameTheoryComplexity.Backend.GridRoutingNodeMachine

@[expose] public section

/-! A candidate is accepted exactly when it is live and realizes the requested
point. Selection carries an explicit found flag; an empty internal node word
is a vertex-zero representation and cannot stand for search failure. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- Check a candidate's liveness and exact realized coordinates. -/
def routingCandidateFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y node : List Bool) : List Bool :=
  andFlag (routingLiveNodeFlag ruler P S node)
    (andFlag (routingEQFlag (routingNodeImageXBits ruler P S node) x)
      (routingEQFlag (routingNodeImageYBits ruler P S node) y))

/-- Interpret the explicit found flag independently of its selected node word. -/
def routingDecodeResultBits (result : List Bool) : Option WireNode :=
  if CircuitWords.first result = [true] then some (routingDecodeNodeBits (CircuitWords.rest result)) else none

/-- Success specifies the explicit found flag and the exact semantic node. -/
theorem routingDecodeResultBits_eq_some_iff (result : List Bool) (node : WireNode) :
    routingDecodeResultBits result = some node ↔
      CircuitWords.first result = [true] ∧ routingDecodeNodeBits (CircuitWords.rest result) = node := by
  unfold routingDecodeResultBits
  split_ifs <;> simp_all

/-- Select the first accepted candidate, keeping failure separate from vertex zero. -/
def routingChooseNodeBits (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List (List Bool) → List Bool
  | [] => CircuitWords.encodePair [false] []
  | node :: nodes => select (routingCandidateFlag ruler P S x y node)
      (CircuitWords.encodePair [true] node) (routingChooseNodeBits ruler P S x y nodes)

/-- A result fails exactly when its explicit found flag is not the success flag. -/
theorem routingDecodeResultBits_eq_none_iff (result : List Bool) :
    routingDecodeResultBits result = none ↔ CircuitWords.first result ≠ [true] := by
  unfold routingDecodeResultBits
  split_ifs <;> simp_all

private theorem andFlag_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

/-- Candidate validation is exactly live geometric membership at the requested point. -/
theorem routingCandidateFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y node : List Bool) : routingCandidateFlag ruler P S x y node =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
      routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
          (lsbValue x, lsbValue y))] := by
  simp only [routingCandidateFlag, routingLiveNodeFlag_value, routingEQFlag_value,
    routingNodeImageXBits_value, routingNodeImageYBits_value, andFlag_decide, Prod.ext_iff]

/-- Every candidate test returns one Boolean flag. -/
@[simp] theorem routingCandidateFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (x y node : List Bool) : (routingCandidateFlag ruler P S x y node).length = 1 := by
  rw [routingCandidateFlag_value]
  rfl

/-- Framed selection agrees with the existing mathematical first-live-node selector. -/
theorem routingChooseNodeBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) (nodes : List (List Bool)) :
    routingDecodeResultBits (routingChooseNodeBits ruler P S x y nodes) =
      chooseWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue x, lsbValue y)
          (nodes.map routingDecodeNodeBits) := by
  induction nodes with
  | nil => simp [routingChooseNodeBits, CircuitWords.first, CircuitWords.splitPair, routingDecodeResultBits, chooseWireNode]
  | cons node nodes ih =>
      by_cases h : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
            (lsbValue x, lsbValue y)
      · simp [routingChooseNodeBits, CircuitWords.first, CircuitWords.rest, CircuitWords.splitPair, routingCandidateFlag_value, h, select,
          routingDecodeResultBits, chooseWireNode]
      · simp [routingChooseNodeBits, routingCandidateFlag_value, h, select,
          chooseWireNode, ih]

/-- Selection always emits a canonical found flag, independently of the chosen node. -/
theorem routingChooseNodeBits_found_flag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) (nodes : List (List Bool)) :
    CircuitWords.first (routingChooseNodeBits ruler P S x y nodes) = [true] ∨
      CircuitWords.first (routingChooseNodeBits ruler P S x y nodes) = [false] := by
  induction nodes with
  | nil => simp [routingChooseNodeBits, CircuitWords.first, CircuitWords.splitPair]
  | cons node nodes ih =>
      by_cases h : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
            (lsbValue x, lsbValue y)
      · simp [routingChooseNodeBits, CircuitWords.first, CircuitWords.splitPair, routingCandidateFlag_value, h, select]
      · simpa only [routingChooseNodeBits, routingCandidateFlag_value, h, decide_false,
          select, List.headD_cons, Bool.false_eq_true, ite_false] using ih

/-- Candidate validation charges seeded pointer computation and exact image comparison. -/
@[fun_prop] theorem routingCandidateFlagUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingCandidateFlag (ruler z) (P (seed z)) (S (seed z)) (x z) (y z) (node z)) enc encBits := by
  unfold routingCandidateFlag
  fun_prop

/-- A fixed finite list of native candidate producers has a native selector. -/
@[fun_prop] theorem routingChooseNodeBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits)
    (nodes : List (α → List Bool))
    (hn : ∀ node ∈ nodes, ComputableInPolyTime node enc encBits) :
    ComputableInPolyTime (fun z => routingChooseNodeBits (ruler z) (P (seed z)) (S (seed z))
      (x z) (y z) (nodes.map (fun node => node z))) enc encBits := by
  induction nodes with
  | nil => exact const _
  | cons node nodes ih =>
      have hnode := hn node (List.mem_cons_self ..)
      have htail := ih (fun n hn' => hn n (List.mem_cons_of_mem _ hn'))
      exact select_polyTime.comp
        ((routingCandidateFlagUniform_polyTime P S hr hs hx hy hnode hP hS).prod
          ((CircuitWords.encodePair_polyTime.comp ((const [true]).prod hnode)).prod htail))

end GameTheory.Complexity.Backend
