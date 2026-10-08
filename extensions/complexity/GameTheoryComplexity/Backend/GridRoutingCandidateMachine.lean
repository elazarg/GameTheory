import GameTheoryComplexity.Backend.GridRoutingNodeMachine

/-! A candidate is accepted exactly when it is live and realizes the requested
point. Selection carries an explicit found flag; an empty internal node word
is a vertex-zero representation and cannot stand for search failure. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

/-- Check a candidate's liveness and exact realized coordinates. -/
def routingCandidateFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y node : List Bool) : List Bool :=
  andBit (routingLiveNodeFlag ruler P S node)
    (andBit (routingEQFlag (routingNodeImageXBits ruler P S node) x)
      (routingEQFlag (routingNodeImageYBits ruler P S node) y))

/-- Interpret the explicit found flag independently of its selected node word. -/
def routingDecodeResultBits (result : List Bool) : Option WireNode :=
  if pairFst result = [true] then some (routingDecodeNodeBits (pairSnd result)) else none

/-- Success specifies the explicit found flag and the exact semantic node. -/
theorem routingDecodeResultBits_eq_some_iff (result : List Bool) (node : WireNode) :
    routingDecodeResultBits result = some node ↔
      pairFst result = [true] ∧ routingDecodeNodeBits (pairSnd result) = node := by
  unfold routingDecodeResultBits
  split_ifs <;> simp_all

/-- Select the first accepted candidate, keeping failure separate from vertex zero. -/
def routingChooseNodeBits (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List (List Bool) → List Bool
  | [] => pair [false] []
  | node :: nodes => caseBit₀ (routingCandidateFlag ruler P S x y node)
      (pair [true] node) (routingChooseNodeBits ruler P S x y nodes)

/-- A result fails exactly when its explicit found flag is not the success flag. -/
theorem routingDecodeResultBits_eq_none_iff (result : List Bool) :
    routingDecodeResultBits result = none ↔ pairFst result ≠ [true] := by
  unfold routingDecodeResultBits
  split_ifs <;> simp_all

private theorem andBit_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

/-- Candidate validation is exactly live geometric membership at the requested point. -/
theorem routingCandidateFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y node : List Bool) : routingCandidateFlag ruler P S x y node =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
      routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
          (Nat.fromBitsLE x, Nat.fromBitsLE y))] := by
  simp only [routingCandidateFlag, routingLiveNodeFlag_value, routingEQFlag_value,
    routingNodeImageXBits_value, routingNodeImageYBits_value, andBit_decide, Prod.ext_iff]

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
        (routingOriginalPointer ruler S) (Nat.fromBitsLE x, Nat.fromBitsLE y)
          (nodes.map routingDecodeNodeBits) := by
  induction nodes with
  | nil => simp [routingChooseNodeBits, routingDecodeResultBits, chooseWireNode]
  | cons node nodes ih =>
      by_cases h : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
            (Nat.fromBitsLE x, Nat.fromBitsLE y)
      · simp [routingChooseNodeBits, routingCandidateFlag_value, h, caseBit₀,
          routingDecodeResultBits, chooseWireNode]
      · simp [routingChooseNodeBits, routingCandidateFlag_value, h, caseBit₀,
          chooseWireNode, ih]

/-- Selection always emits a canonical found flag, independently of the chosen node. -/
theorem routingChooseNodeBits_found_flag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) (nodes : List (List Bool)) :
    pairFst (routingChooseNodeBits ruler P S x y nodes) = [true] ∨
      pairFst (routingChooseNodeBits ruler P S x y nodes) = [false] := by
  induction nodes with
  | nil => simp [routingChooseNodeBits]
  | cons node nodes ih =>
      by_cases h : liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) ∧
        routedCoordinate (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (routingDecodeNodeBits node) =
            (Nat.fromBitsLE x, Nat.fromBitsLE y)
      · simp [routingChooseNodeBits, routingCandidateFlag_value, h, caseBit₀]
      · simpa only [routingChooseNodeBits, routingCandidateFlag_value, h, decide_false,
          caseBit₀, Bool.cond_false] using ih

/-- Candidate validation composes actual seeded pointer and node machines uniformly. -/
theorem routingCandidateFlagUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed x y node : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingCandidateFlag (ruler z) (P (seed z)) (S (seed z))
      (x z) (y z) (node z)) ∈ FP :=
  andBitFn_mem_FP (routingLiveNodeFlagUniformFn_mem_FP P S hr hs hn hP hS)
    (andBitFn_mem_FP
      (routingEQFlagFn_mem_FP (routingNodeImageXBitsUniformFn_mem_FP P S hr hs hn hP hS) hx)
      (routingEQFlagFn_mem_FP (routingNodeImageYBitsUniformFn_mem_FP P S hr hs hn hP hS) hy))

/-- A fixed finite sequence of FP candidate producers has an actual FP selector. -/
theorem routingChooseNodeBitsUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP)
    (nodes : List (List Bool → List Bool)) (hn : ∀ node ∈ nodes, node ∈ FP) :
    (fun z => routingChooseNodeBits (ruler z) (P (seed z)) (S (seed z))
      (x z) (y z) (nodes.map (fun node => node z))) ∈ FP := by
  induction nodes with
  | nil => exact constFn_mem_FP _
  | cons node nodes ih =>
      have hnode := hn node (List.mem_cons_self ..)
      have htail := ih (fun n hn' => hn n (List.mem_cons_of_mem _ hn'))
      exact selectFn_mem_FP (routingCandidateFlagUniformFn_mem_FP P S hr hs hx hy hnode hP hS)
        (pairFn_mem_FP (constFn_mem_FP [true]) hnode) htail

end GameTheory.Complexity.Backend
