import GameTheoryComplexity.Backend.SpernerCornerMachine
import GameTheoryComplexity.Backend.SpernerCrossMachine
import GameTheoryComplexity.Backend.SpernerDoorMachine
import GameTheoryComplexity.Backend.SpernerGridWords

/-! A composed polynomial-time Sperner pointer reads three corner colors and
crosses their selected door. Boundary coordinates retain an extra bit; rejected
node words remain isolated. Color queries may depend on a serialized input seed. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
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
  caseBit₀ (gridNodeAcceptFlag ruler word)
    (caseBit₀ (bitAt [] word) (gridTrianglePointer ruler query incoming word)
      (if incoming then gridWidthWord ruler
        else [true, false] ++ (gridWidthWord ruler).tail.tail)) word

/-- Triangle pointers compose FP word producers with a uniform FP color query. -/
theorem gridTrianglePointerUniformFn_mem_FP (incoming : Bool)
    {ruler seed word : List Bool → List Bool}
    {query : List Bool → List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : word ∈ FP)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => gridTrianglePointer (ruler z) (query (seed z)) incoming (word z)) ∈ FP :=
  gridChooseDoorFn_mem_FP incoming
    (gridCornerColorUniformFn_mem_FP 0 hr hs hw query hq)
    (gridCornerColorUniformFn_mem_FP 1 hr hs hw query hq)
    (gridCornerColorUniformFn_mem_FP 2 hr hs hw query hq)
    (gridCrossWordFn_mem_FP incoming 0 hr hw)
    (gridCrossWordFn_mem_FP incoming 1 hr hw)
    (gridCrossWordFn_mem_FP incoming 2 hr hw) hw

/-- The whole pointer is computed in polynomial time, uniformly in its color seed. -/
theorem gridPointerMachineUniformFn_mem_FP (incoming : Bool)
    {ruler seed word : List Bool → List Bool}
    {query : List Bool → List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : word ∈ FP)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => gridPointerMachine (ruler z) (query (seed z)) incoming (word z)) ∈ FP := by
  have hwidth := gridWidthWordFn_mem_FP hr
  have hsource : (fun z => if incoming then gridWidthWord (ruler z)
      else [true, false] ++ (gridWidthWord (ruler z)).tail.tail) ∈ FP := by
    cases incoming with
    | false =>
      exact appendFn_mem_FP (constFn_mem_FP _)
        (CobhamFP_subset_FP (tailFn (tailFn (FP_subset_CobhamFP hwidth))))
    | true => exact hwidth
  exact selectFn_mem_FP (gridNodeAcceptFlagFn_mem_FP hr hw)
    (selectFn_mem_FP (CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hw)))
      (gridTrianglePointerUniformFn_mem_FP incoming hr hs hw hq) hsource) hw

private theorem zero_bits (b : ℕ) : Nat.toBitsLE b 0 = List.replicate b false := by
  have h : Nat.toBits b 0 = List.replicate b false := by
    induction b with
    | zero => rfl
    | succ b ih => simp [Nat.toBits, ih, List.replicate_succ]
  simpa [Nat.toBitsLE] using congrArg List.reverse h

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
    simpa only [encodeGridNode, List.cons_append, List.nil_append, bitAt_nil_left,
      caseBit₀_cons, Bool.cond_true] using
      gridTrianglePointer_encode ruler query incoming t (hv t rfl)
  | none =>
    have hz : gridWidthWord ruler =
        false :: false :: List.replicate (2 * ruler.length) false := by
      simp [gridWidthWord, gridNodeWidth, Nat.add_comm (2 * ruler.length) 2,
        List.replicate_add, List.replicate_succ]
    change caseBit₀ [true]
      (caseBit₀ (bitAt [] (gridWidthWord ruler)) _ _) (gridWidthWord ruler) = _
    rw [hz]
    cases incoming <;>
      simp only [bitAt_nil_left, caseBit₀_cons, Bool.cond_false, Bool.cond_true,
        gridPointer, encodeGridNode, entranceTriangle, zero_bits, List.tail_cons,
        Bool.false_eq_true, ↓reduceIte]
    · rw [two_mul, List.replicate_add, List.append_assoc]
    · rw [gridNodeWidth, Nat.add_comm (2 * ruler.length) 2, List.replicate_add]
      rfl

/-- Rejected node codes remain isolated under execution. -/
theorem gridPointerMachine_reject (ruler : List Bool) (query : List Bool → List Bool)
    (incoming : Bool) (word : List Bool) (hd : decodeGridNode ruler.length word = none) :
    gridPointerMachine ruler query incoming word = word := by
  have hf : gridNodeAcceptFlag ruler word = [true] ∨
      gridNodeAcceptFlag ruler word = [false] := andBit_flag _ _
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
  gridPointerMachine (pairFst input) (evaluateCircuitVector (pairSnd input)) incoming word

/-- One actual FP computation evaluates the pointer uniformly in the circuit instance. -/
theorem spernerPointer_pair_mem_FP (incoming : Bool) :
    (fun z => spernerPointer (pairFst z) incoming (pairSnd z)) ∈ FP :=
  gridPointerMachineUniformFn_mem_FP incoming
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
    evaluateCircuitVector_pair_mem_FP

/-- Serialized-circuit pointer execution has the same known source at every width. -/
theorem spernerPointer_source (input : List Bool) :
    let origin := encodeGridNode (pairFst input).length none
    spernerPointer input true origin = origin ∧
      spernerPointer input false origin ≠ origin ∧
      spernerPointer input true (spernerPointer input false origin) = origin := by
  simpa only [spernerPointer, gridPointerMachine_eq_wordGridPointer] using
    word_grid_source (pairFst input).length
      (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))

/-- Every non-source endpoint of the certified machine denotes a trichromatic cell. -/
theorem spernerPointer_endpoint_decodes (input word : List Bool)
    (hne : word ≠ encodeGridNode (pairFst input).length none)
    (he : GameTheory.Math.EndOfLine.IsEndpoint
      (spernerPointer input true) (spernerPointer input false) word) :
    ∃ t, decodeGridNode (pairFst input).length word = some (some t) ∧
      ValidTriangle (2 ^ (pairFst input).length) t ∧
      Trichromatic
        (standardGridColor (2 ^ (pairFst input).length)
          (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))
          (corner t 0).1 (corner t 0).2)
        (standardGridColor (2 ^ (pairFst input).length)
          (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))
          (corner t 1).1 (corner t 1).2)
        (standardGridColor (2 ^ (pairFst input).length)
          (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))
          (corner t 2).1 (corner t 2).2) := by
  apply word_grid_endpoint_decodes _ hne
  have hp : spernerPointer input true = wordGridPointer (pairFst input).length
      (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))
      true := funext fun _ => gridPointerMachine_eq_wordGridPointer _ _ _ _
  have hs : spernerPointer input false = wordGridPointer (pairFst input).length
      (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))
      false := funext fun _ => gridPointerMachine_eq_wordGridPointer _ _ _ _
  rwa [hp, hs] at he

end GameTheory.Complexity.Backend
