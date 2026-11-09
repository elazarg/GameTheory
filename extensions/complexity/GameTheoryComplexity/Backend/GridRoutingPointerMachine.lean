module

public import GameTheoryComplexity.Backend.GridRoutingDecoderMachine
public import GameTheoryComplexity.Backend.GridRoutingNodeStepMachine
public import GameTheoryComplexity.Backend.GridRoutingWords

@[expose] public section

/-! One composed routing pointer decodes a live internal node, follows the
crossing-switched step, and serializes its exact image. Malformed external
words and background points remain unchanged. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
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
  let next := routingSwitchedNodeStepBits ruler P S incoming (CircuitWords.rest result)
  select (routingPointAcceptFlag ruler word)
    (select (CircuitWords.first result) (routingNodeOutputBits ruler P S next) word) word

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
  simp only [routingNodeOutputBits, routingPadBits_eq_lowBits,
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
        (lsbValue (routingPointXBits ruler word),
          lsbValue (routingPointYBits ruler word)) := by
      simp only [decodeRoutingPoint, hw, ↓reduceIte, routingPointXBits, routingPointYBits]
    rw [wordRoutingPointer_of_decode hd incoming]
    unfold routingPointerMachine
    rw [ha]
    simp only [select_cons, ↓reduceIte]
    cases hg : decodeWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S)
        (lsbValue (routingPointXBits ruler word),
          lsbValue (routingPointYBits ruler word)) with
    | none =>
        have hn := (routingDecodeResultBits_eq_none_iff _).mp
          ((routingDecoderBits_decode ruler P S
            (routingPointXBits ruler word) (routingPointYBits ruler word)).trans hg)
        have hf := (routingDecoderBits_found_flag ruler P S
          (routingPointXBits ruler word) (routingPointYBits ruler word)).resolve_left hn
        rw [hf]
        cases incoming <;>
          simp only [Bool.false_eq_true, ↓reduceIte, gridRoutedPredecessor,
            gridRoutedSuccessor, hg] <;>
          exact (encodeRoutingPoint_decode hd).symm
    | some node =>
        obtain ⟨hf, hn⟩ := (routingDecodeResultBits_eq_some_iff _ _).mp
          ((routingDecoderBits_decode ruler P S
            (routingPointXBits ruler word) (routingPointYBits ruler word)).trans hg)
        rw [hf]
        simp only [select_cons, ↓reduceIte]
        rw [routingNodeOutputBits_eq_encode, routingSwitchedNodeStepBits_decode, hn]
        cases incoming <;>
          simp only [Bool.false_eq_true, ↓reduceIte, gridRoutedPredecessor,
            gridRoutedSuccessor, hg]
  · have hn : routingPointAcceptFlag ruler word ≠ [true] := by
      intro ha
      exact hw ((routingPointAcceptFlag_width ruler word).mp ha)
    have hf : routingPointAcceptFlag ruler word = [false] :=
      by simp [routingPointAcceptFlag, hw]
    simp only [routingPointerMachine, hf, select_cons, Bool.false_eq_true, ↓reduceIte,
      wordRoutingPointer, decodeRoutingPoint, hw]

/-- The composed pointer preserves external word length, including malformed inputs. -/
@[simp] theorem routingPointerMachine_length (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) :
    (routingPointerMachine ruler P S incoming word).length = word.length := by
  rw [routingPointerMachine_eq_words, wordRoutingPointer_length]

/-- Crossing-switched steps charge native seeded pointer and raw-node producers. -/
@[fun_prop] theorem routingSwitchedNodeStepBitsUniform_polyTime (incoming : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingSwitchedNodeStepBits (ruler z) (P (seed z)) (S (seed z)) incoming (node z)) enc encBits := by
  cases incoming
  · exact routingNodeStepBitsUniform_polyTime false P S hruler hseed
      (routingNodeSwitchBitsUniform_polyTime P S hruler hseed hnode hP hS) hP hS
  · exact routingNodeSwitchBitsUniform_polyTime P S hruler hseed
      (routingNodeStepBitsUniform_polyTime true P S hruler hseed hnode hP hS) hP hS

/-- External node-image packing charges both complete canonical fields. -/
@[fun_prop] theorem routingNodeOutputBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed node : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hnode : ComputableInPolyTime node enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingNodeOutputBits (ruler z) (P (seed z)) (S (seed z)) (node z)) enc encBits := by
  exact bitsAppend
    (routingPadBits_polyTime (routingCoordinateRuler_polyTime hruler)
      (routingNodeImageXBitsUniform_polyTime P S hruler hseed hnode hP hS))
    (routingPadBits_polyTime (routingCoordinateRuler_polyTime hruler)
      (routingNodeImageYBitsUniform_polyTime P S hruler hseed hnode hP hS))

/-- The complete routing pointer has one native uniform polynomial-time machine. -/
@[fun_prop] theorem routingPointerMachineUniform_polyTime (incoming : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hword : ComputableInPolyTime word enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingPointerMachine (ruler z) (P (seed z)) (S (seed z)) incoming (word z)) enc encBits := by
  have hd := routingDecoderBitsUniform_polyTime P S hruler hseed
    (routingPointXBits_polyTime hruler hword) (routingPointYBits_polyTime hruler hword) hP hS
  have hn := CircuitWords.rest_polyTime.comp hd
  have hf := CircuitWords.first_polyTime.comp hd
  have hstep := routingSwitchedNodeStepBitsUniform_polyTime incoming P S hruler hseed hn hP hS
  have hout := routingNodeOutputBitsUniform_polyTime P S hruler hseed hstep hP hS
  exact select_polyTime.comp ((routingPointAcceptFlag_polyTime hruler hword).prod
    ((select_polyTime.comp (hf.prod (hout.prod hword))).prod hword))

end GameTheory.Complexity.Backend
