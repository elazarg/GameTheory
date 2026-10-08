import GameTheoryComplexity.Backend.GridRoutingDecoderMachine
import GameTheoryComplexity.Backend.GridRoutingNodeStepMachine
import GameTheoryComplexity.Backend.GridRoutingWords

/-! One composed routing pointer decodes a live internal node, follows the
crossing-switched step, and serializes its exact image. Malformed external
words and background points remain unchanged. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

/-- Switch outgoing tails before a successor step and incoming tails after a predecessor. -/
def routingSwitchedNodeStepBits (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (node : List Bool) : List Bool :=
  if incoming then
    routingNodeSwitchBits ruler P S (routingNodeStepBits ruler P S node true)
  else routingNodeStepBits ruler P S (routingNodeSwitchBits ruler P S node) false

/-- Pack the realized node image into the external fixed-width coordinate codec. -/
def routingNodeOutputBits (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : List Bool :=
  routingPadBits (routingCoordinateRuler ruler) (routingNodeImageXBits ruler P S node) ++
    routingPadBits (routingCoordinateRuler ruler) (routingNodeImageYBits ruler P S node)

/-- The complete binary routing pointer preserves malformed words and background points. -/
def routingPointerMachine (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) : List Bool :=
  let result := routingDecoderBits ruler P S (routingPointXBits ruler word)
    (routingPointYBits ruler word)
  let next := routingSwitchedNodeStepBits ruler P S incoming (pairSnd result)
  caseBit₀ (routingPointAcceptFlag ruler word)
    (caseBit₀ (pairFst result) (routingNodeOutputBits ruler P S next) word) word

/-- Internal execution follows precisely the mathematical crossing-switched pointer. -/
theorem routingSwitchedNodeStepBits_decode (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (node : List Bool) :
    routingDecodeNodeBits (routingSwitchedNodeStepBits ruler P S incoming node) =
      (if incoming then switchedRoutedPredecessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
      else switchedRoutedSuccessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
          (routingDecodeNodeBits node) := by
  cases incoming <;>
    simp only [routingSwitchedNodeStepBits, Bool.false_eq_true, ↓reduceIte,
      routingNodeStepBits_decode, routingNodeSwitchBits_decode,
      switchedRoutedPredecessor, switchedRoutedSuccessor, Function.comp_apply]

/-- Output packing is exactly the canonical encoding of the realized semantic node. -/
theorem routingNodeOutputBits_eq_encode (ruler : List Bool) (P S : List Bool → List Bool)
    (node : List Bool) : routingNodeOutputBits ruler P S node =
      encodeRoutingPoint ruler.length (routedCoordinate (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
          (routingDecodeNodeBits node)) := by
  simp only [routingNodeOutputBits, routingPadBits_eq_toBitsLE,
    routingCoordinateRuler_length, routingNodeImageXBits_value, routingNodeImageYBits_value,
    encodeRoutingPoint]

/-- The composed machine agrees exactly with the word graph on every external word. -/
theorem routingPointerMachine_eq_words (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) : routingPointerMachine ruler P S incoming word =
      wordRoutingPointer ruler.length (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) incoming word := by
  by_cases hw : word.length = routingPointWidth ruler.length
  · have ha := (routingPointAcceptFlag_width ruler word).mpr hw
    have hd : decodeRoutingPoint ruler.length word = some
        (Nat.fromBitsLE (routingPointXBits ruler word),
          Nat.fromBitsLE (routingPointYBits ruler word)) := by
      simp only [decodeRoutingPoint, hw, ↓reduceIte, routingPointXBits, routingPointYBits]
    rw [wordRoutingPointer_of_decode hd incoming]
    unfold routingPointerMachine
    rw [ha]
    simp only [caseBit₀, Bool.cond_true]
    cases hg : decodeWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S)
        (Nat.fromBitsLE (routingPointXBits ruler word),
          Nat.fromBitsLE (routingPointYBits ruler word)) with
    | none =>
        have hn := (routingDecodeResultBits_eq_none_iff _).mp
          ((routingDecoderBits_decode ruler P S
            (routingPointXBits ruler word) (routingPointYBits ruler word)).trans hg)
        have hf := (routingDecoderBits_found_flag ruler P S
          (routingPointXBits ruler word) (routingPointYBits ruler word)).resolve_left hn
        rw [hf]
        simp only [Bool.cond_false]
        cases incoming <;>
          simp only [Bool.false_eq_true, ↓reduceIte, gridRoutedPredecessor,
            gridRoutedSuccessor, hg] <;>
          exact (encodeRoutingPoint_decode hd).symm
    | some node =>
        obtain ⟨hf, hn⟩ := (routingDecodeResultBits_eq_some_iff _ _).mp
          ((routingDecoderBits_decode ruler P S
            (routingPointXBits ruler word) (routingPointYBits ruler word)).trans hg)
        rw [hf]
        simp only [Bool.cond_true]
        rw [routingNodeOutputBits_eq_encode, routingSwitchedNodeStepBits_decode, hn]
        cases incoming <;>
          simp only [Bool.false_eq_true, ↓reduceIte, gridRoutedPredecessor,
            gridRoutedSuccessor, hg]
  · have hn : routingPointAcceptFlag ruler word ≠ [true] := by
      intro ha
      exact hw ((routingPointAcceptFlag_width ruler word).mp ha)
    have hf : routingPointAcceptFlag ruler word = [false] :=
      (eqFlag_flag _ _).resolve_left hn
    simp only [routingPointerMachine, hf, caseBit₀, Bool.cond_false,
      wordRoutingPointer, decodeRoutingPoint, hw, ite_false]

/-- The composed pointer preserves external word length, including malformed inputs. -/
@[simp] theorem routingPointerMachine_length (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) :
    (routingPointerMachine ruler P S incoming word).length = word.length := by
  rw [routingPointerMachine_eq_words, wordRoutingPointer_length]

/-- Crossing-switched internal steps compose seeded polynomial-time producers uniformly. -/
theorem routingSwitchedNodeStepBitsUniformFn_mem_FP (incoming : Bool)
    (P S : List Bool → List Bool → List Bool) {ruler seed node : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingSwitchedNodeStepBits (ruler z) (P (seed z)) (S (seed z))
      incoming (node z)) ∈ FP := by
  cases incoming
  · exact routingNodeStepBitsUniformFn_mem_FP false P S hr hs
      (routingNodeSwitchBitsUniformFn_mem_FP P S hr hs hn hP hS) hP hS
  · exact routingNodeSwitchBitsUniformFn_mem_FP P S hr hs
      (routingNodeStepBitsUniformFn_mem_FP true P S hr hs hn hP hS) hP hS

/-- External node-image packing has an actual uniform polynomial-time certificate. -/
theorem routingNodeOutputBitsUniformFn_mem_FP (P S : List Bool → List Bool → List Bool)
    {ruler seed node : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hn : node ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingNodeOutputBits (ruler z) (P (seed z)) (S (seed z)) (node z)) ∈ FP :=
  appendFn_mem_FP
    (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr)
      (routingNodeImageXBitsUniformFn_mem_FP P S hr hs hn hP hS))
    (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr)
      (routingNodeImageYBitsUniformFn_mem_FP P S hr hs hn hP hS))

/-- The complete routing pointer has one actual uniform polynomial-time certificate. -/
theorem routingPointerMachineUniformFn_mem_FP (incoming : Bool)
    (P S : List Bool → List Bool → List Bool) {ruler seed word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : word ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingPointerMachine (ruler z) (P (seed z)) (S (seed z))
      incoming (word z)) ∈ FP := by
  have hd := routingDecoderBitsUniformFn_mem_FP P S hr hs
    (routingPointXBitsFn_mem_FP hr hw) (routingPointYBitsFn_mem_FP hr hw) hP hS
  have hn := mem_FP_comp hd pairSnd_mem_FP
  have hf := mem_FP_comp hd pairFst_mem_FP
  have hstep := routingSwitchedNodeStepBitsUniformFn_mem_FP incoming P S hr hs hn hP hS
  have hout := routingNodeOutputBitsUniformFn_mem_FP P S hr hs hstep hP hS
  exact selectFn_mem_FP (routingPointAcceptFlagFn_mem_FP hr hw)
    (selectFn_mem_FP hf hout hw) hw

end GameTheory.Complexity.Backend
