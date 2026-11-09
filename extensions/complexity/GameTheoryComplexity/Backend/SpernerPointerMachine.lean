module

public import GameTheoryComplexity.Backend.SpernerCornerMachine
public import GameTheoryComplexity.Backend.SpernerCrossMachine
public import GameTheoryComplexity.Backend.SpernerDoorMachine
public import GameTheoryComplexity.Backend.SpernerGridWords

@[expose] public section

/-! A composed polynomial-time Sperner pointer reads three corner colors and
crosses their selected door. Boundary coordinates retain an extra bit; rejected
node words remain isolated. Color queries may depend on a serialized input seed. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime WordOperations Cslib.BitString
open GameTheory.Math.Sperner

/-- Select a local triangle neighbor from three boundary-aware corner colors. -/
def gridTrianglePointer (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) : List Bool :=
  gridChooseDoor incoming (gridCornerColor ruler query word 0)
    (gridCornerColor ruler query word 1) (gridCornerColor ruler query word 2)
    (gridCrossWord ruler incoming 0 word) (gridCrossWord ruler incoming 1 word)
    (gridCrossWord ruler incoming 2 word) word

/-- Compute a graph pointer, with one canonical source and malformed-word isolation. -/
def gridPointerMachine (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) : List Bool :=
  select (gridNodeAcceptFlag ruler word)
    (select ([word.headD false]) (gridTrianglePointer ruler query incoming word)
      (if incoming then gridWidthWord ruler
        else [true, false] ++ (gridWidthWord ruler).tail.tail)) word

/-- Triangle pointers charge three colors and all selected neighbor computations. -/
@[fun_prop] theorem gridTrianglePointer_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits)
    (query : α → List Bool → List Bool)
    (hq : ComputableInPolyTime (fun p : α × List Bool => query p.1 p.2)
      (encPair enc encBits) encBits) :
    ComputableInPolyTime
      (fun a => gridTrianglePointer (ruler a) (query a) incoming (word a)) enc encBits :=
  gridChooseDoor_polyTime incoming
    (gridCornerColor_polyTime hr hw query hq 0)
    (gridCornerColor_polyTime hr hw query hq 1)
    (gridCornerColor_polyTime hr hw query hq 2)
    (gridCrossWord_polyTime incoming 0 hr hw)
    (gridCrossWord_polyTime incoming 1 hr hw)
    (gridCrossWord_polyTime incoming 2 hr hw) hw

/-- Canonical-source dispatch and malformed-word isolation have native certificates. -/
@[fun_prop] theorem gridPointerMachine_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits)
    (query : α → List Bool → List Bool)
    (hq : ComputableInPolyTime (fun p : α × List Bool => query p.1 p.2)
      (encPair enc encBits) encBits) :
    ComputableInPolyTime
      (fun a => gridPointerMachine (ruler a) (query a) incoming (word a)) enc encBits := by
  have hwidth := gridWidthWord_polyTime hr
  have hsource : ComputableInPolyTime (fun a => if incoming then gridWidthWord (ruler a)
      else [true, false] ++ (gridWidthWord (ruler a)).tail.tail) enc encBits := by
    cases incoming with
    | false => exact bitsAppend (const [true, false]) (bitsTail.comp (bitsTail.comp hwidth))
    | true => exact hwidth
  have hhead : ComputableInPolyTime (fun a => [(word a).headD false]) enc encBits :=
    bitsCons ((ComputableInPolyTime.headD (encA := encBool) false).comp hw) (const [])
  exact select_polyTime.comp ((gridNodeAcceptFlag_polyTime hr hw).prod
    ((select_polyTime.comp (hhead.prod
      ((gridTrianglePointer_polyTime incoming hr hw query hq).prod hsource))).prod hw))

private theorem zero_bits (b : ℕ) : lowBits b 0 = List.replicate b false := by
  simpa only [List.length_replicate, lsbValue_replicate_false] using
    lowBits_lsbValue (List.replicate b false)

/-- Local triangle execution agrees with the mathematical selected-edge pointer. -/
theorem gridTrianglePointer_encode (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (t : GridTriangle) (hv : ValidTriangle (2 ^ ruler.length) t) :
    gridTrianglePointer ruler query incoming (encodeGridNode ruler.length (some t)) =
      encodeGridNode ruler.length
        (gridPointer (2 ^ ruler.length) (gridInteriorColor ruler.length query) incoming
          (some t)) := by
  unfold gridTrianglePointer
  rw [gridCornerColor_encode ruler query t 0 hv,
    gridCornerColor_encode ruler query t 1 hv, gridCornerColor_encode ruler query t 2 hv]
  simp only [encodeGridColor]
  rw [gridChooseDoor_colors]
  change (match gridDoor (standardGridColor (2 ^ ruler.length)
      (gridInteriorColor ruler.length query)) t incoming with
    | none => encodeGridNode ruler.length (some t)
    | some p => if p = 0 then _ else if p = 1 then _ else _) = _
  rw [gridPointer, ite_eq_left hv]
  cases hd : gridDoor (standardGridColor (2 ^ ruler.length)
      (gridInteriorColor ruler.length query)) t incoming with
  | none => rfl
  | some p =>
    have hcross : gridCrossWord ruler incoming p (encodeGridNode ruler.length (some t)) =
        encodeGridNode ruler.length (match across (2 ^ ruler.length) t p with
          | some (u, _) => some u
          | none => if incoming then none else some t) := by
      rw [gridCrossWord_encode ruler incoming p t hv]
      cases across (2 ^ ruler.length) t p with
      | none => cases incoming <;> rfl
      | some uq => rfl
    fin_cases p <;> dsimp <;> exact hcross

/-- Every accepted encoded node executes exactly its established graph pointer. -/
theorem gridPointerMachine_encode (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (node : Option GridTriangle)
    (hv : ∀ t, node = some t → ValidTriangle (2 ^ ruler.length) t) :
    gridPointerMachine ruler query incoming (encodeGridNode ruler.length node) =
      encodeGridNode ruler.length
        (gridPointer (2 ^ ruler.length) (gridInteriorColor ruler.length query) incoming node) := by
  have ha := (gridNodeAcceptFlag_accept ruler (encodeGridNode ruler.length node)).mpr
    ⟨node, decodeGridNode_encode _ _ hv⟩
  rw [gridPointerMachine, ha]
  cases node with
  | some t =>
    simpa only [encodeGridNode, List.cons_append, List.nil_append, List.headD_cons,
      select_cons, ite_true] using
      gridTrianglePointer_encode ruler query incoming t (hv t rfl)
  | none =>
    have hz : gridWidthWord ruler =
        false :: false :: List.replicate (2 * ruler.length) false := by
      simp [gridWidthWord, gridNodeWidth, Nat.add_comm (2 * ruler.length) 2,
        List.replicate_add, List.replicate_succ]
    change select [true]
      (select [(gridWidthWord ruler).headD false] _ _) (gridWidthWord ruler) = _
    rw [hz]
    cases incoming <;>
      simp only [List.headD_cons, select_cons,
        gridPointer, encodeGridNode, entranceTriangle, zero_bits, List.tail_cons,
        Bool.false_eq_true, ↓reduceIte]
    · rw [two_mul, List.replicate_add, List.append_assoc]
    · rw [gridNodeWidth, Nat.add_comm (2 * ruler.length) 2, List.replicate_add]
      rfl

/-- Rejected node codes remain isolated under execution. -/
theorem gridPointerMachine_reject (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) (hd : decodeGridNode ruler.length word = none) :
    gridPointerMachine ruler query incoming word = word := by
  have singleton_flag (b : Bool) : [b] = [true] ∨ [b] = [false] := by
    cases b <;> simp
  have hf : gridNodeAcceptFlag ruler word = [true] ∨
      gridNodeAcceptFlag ruler word = [false] := singleton_flag _
  rcases hf with hf | hf
  · obtain ⟨node, hn⟩ := (gridNodeAcceptFlag_accept ruler word).mp hf
    rw [hd] at hn
    cases hn
  · simp [gridPointerMachine, hf]

/-- The FP implementation agrees on every word with the semantic graph transport. -/
theorem gridPointerMachine_eq_wordGridPointer (ruler : List Bool)
    (query : List Bool → List Bool) (incoming : Bool) (word : List Bool) :
    gridPointerMachine ruler query incoming word =
      wordGridPointer ruler.length (gridInteriorColor ruler.length query) incoming word := by
  cases hd : decodeGridNode ruler.length word with
  | none => simpa [wordGridPointer, hd] using
      gridPointerMachine_reject ruler query incoming word hd
  | some node =>
    have hv := decodeGridNode_valid hd
    have he := encodeGridNode_decode hd
    rw [← he, gridPointerMachine_encode ruler query incoming node hv,
      wordGridPointer_encode ruler.length (gridInteriorColor ruler.length query)
        incoming node hv]

/-- Pointer execution preserves word length, including malformed inputs. -/
@[simp] theorem gridPointerMachine_length (ruler : List Bool)
    (query : List Bool → List Bool) (incoming : Bool) (word : List Bool) :
    (gridPointerMachine ruler query incoming word).length = word.length := by
  rw [gridPointerMachine_eq_wordGridPointer, wordGridPointer_length]

/-- A succinct input pairs the coordinate-width ruler with serialized color circuits. -/
def spernerPointer (input : List Bool) (incoming : Bool) (word : List Bool) : List Bool :=
  gridPointerMachine (CircuitWords.first input) (evaluateCircuitVector (CircuitWords.rest input)) incoming word

/-- Serialized circuit pointers charge the complete instance and vertex producers. -/
@[fun_prop] theorem spernerPointer_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits) (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => spernerPointer (input a) incoming (word a)) enc encBits := by
  have hquery : ComputableInPolyTime
      (fun p : α × List Bool => evaluateCircuitVector (CircuitWords.rest (input p.1)) p.2)
      (encPair enc encBits) encBits :=
    evaluateCircuitVector_polyTime
      (CircuitWords.rest_polyTime.comp (hi.comp (fst enc encBits))) (snd enc encBits)
  exact gridPointerMachine_polyTime incoming (CircuitWords.first_polyTime.comp hi) hw
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a))) hquery

/-- Serialized-circuit pointer execution has the same known source at every width. -/
theorem spernerPointer_source (input : List Bool) :
    let origin := encodeGridNode (CircuitWords.first input).length none
    spernerPointer input true origin = origin ∧
      spernerPointer input false origin ≠ origin ∧
      spernerPointer input true (spernerPointer input false origin) = origin := by
  simpa only [spernerPointer, gridPointerMachine_eq_wordGridPointer] using
    word_grid_source (CircuitWords.first input).length
      (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))

/-- Every non-source endpoint of the certified machine denotes a trichromatic cell. -/
theorem spernerPointer_endpoint_decodes (input word : List Bool)
    (hne : word ≠ encodeGridNode (CircuitWords.first input).length none)
    (he : GameTheory.Math.EndOfLine.IsEndpoint
      (spernerPointer input true) (spernerPointer input false) word) :
    ∃ t, decodeGridNode (CircuitWords.first input).length word = some (some t) ∧
      ValidTriangle (2 ^ (CircuitWords.first input).length) t ∧
      Trichromatic
        (standardGridColor (2 ^ (CircuitWords.first input).length)
          (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))
          (corner t 0).1 (corner t 0).2)
        (standardGridColor (2 ^ (CircuitWords.first input).length)
          (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))
          (corner t 1).1 (corner t 1).2)
        (standardGridColor (2 ^ (CircuitWords.first input).length)
          (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))
          (corner t 2).1 (corner t 2).2) := by
  apply word_grid_endpoint_decodes _ hne
  have hp : spernerPointer input true = wordGridPointer (CircuitWords.first input).length
      (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))
      true := funext fun _ => gridPointerMachine_eq_wordGridPointer _ _ _ _
  have hs : spernerPointer input false = wordGridPointer (CircuitWords.first input).length
      (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))
      false := funext fun _ => gridPointerMachine_eq_wordGridPointer _ _ _ _
  rwa [hp, hs] at he

end GameTheory.Complexity.Backend
