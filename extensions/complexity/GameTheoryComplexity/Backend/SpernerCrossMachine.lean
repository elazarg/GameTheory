module

public import GameTheoryComplexity.Backend.SpernerGridCodecMachine
public import GameTheoryComplexity.Backend.SpernerBinarySteps
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Polynomial-time crossing of a selected grid edge on binary node words.
Coordinate tests distinguish exterior edges before ripple arithmetic is used.
Only interior crossings change a coordinate, preserving its fixed-width encoding. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime
open WordOperations
open Cslib.BitString
open GameTheory.Math.Sperner

private def crossingNode (upper : Bool) (x y : List Bool) : List Bool :=
  [true, upper] ++ x ++ y

/-- Cross one selected side using fixed-width coordinate tests and ripple steps.
An exterior edge returns the source for incoming crossings and the original word otherwise. -/
def gridCrossWord (ruler : List Bool) (incoming : Bool) (p : Fin 3)
    (word : List Bool) : List Bool :=
  let node (upper : Bool) (x y : List Bool) : List Bool := [true, upper] ++ x ++ y
  let x := gridNodeXBits ruler word
  let y := gridNodeYBits ruler word
  let zero := List.replicate ruler.length false
  let max := List.replicate ruler.length true
  let exterior := if incoming then gridWidthWord ruler else word
  let upper := if p = 0 then node false x y
    else if p = 1 then select (eqFlag y max) exterior
      (node false x (gridSuccBits y))
    else select (eqFlag x zero) exterior (node false (gridPredBits x) y)
  let lower := if p = 0 then select (eqFlag y zero) exterior
      (node true x (gridPredBits y))
    else if p = 1 then select (eqFlag x max) exterior
      (node true (gridSuccBits x) y)
    else node true x y
  select (gridNodeHalfFlag word) upper lower

private theorem crossingNode_polyTime (upper : Bool)
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => crossingNode upper (x a) (y a)) enc encBits :=
  bitsAppend (bitsAppend (const [true, upper]) hx) hy

/-- Selected-side crossing computes only on the finite-width coordinate words. -/
@[fun_prop] theorem gridCrossWord_polyTime (incoming : Bool) (p : Fin 3)
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => gridCrossWord (ruler a) incoming p (word a)) enc encBits := by
  have hx := gridNodeXBits_polyTime hr hw
  have hy := gridNodeYBits_polyTime hr hw
  have hzero := (bitsReplicate false).comp (length_bits.comp hr)
  have hmax := (bitsReplicate true).comp (length_bits.comp hr)
  have hext : ComputableInPolyTime
      (fun a => if incoming then gridWidthWord (ruler a) else word a) enc encBits := by
    cases incoming
    · exact hw
    · exact gridWidthWord_polyTime hr
  have hxp := gridPredBits_polyTime.comp hx
  have hyp := gridPredBits_polyTime.comp hy
  have hxs := gridSuccBits_polyTime.comp hx
  have hys := gridSuccBits_polyTime.comp hy
  have hh := gridNodeHalfFlag_polyTime hw
  have selectFn {flag yes no : α → List Bool}
      (hf : ComputableInPolyTime flag enc encBits)
      (hy : ComputableInPolyTime yes enc encBits)
      (hn : ComputableInPolyTime no enc encBits) :
      ComputableInPolyTime (fun a => select (flag a) (yes a) (no a)) enc encBits :=
    select_polyTime.comp (hf.prod (hy.prod hn))
  have eqFn {left right : α → List Bool}
      (hl : ComputableInPolyTime left enc encBits)
      (hr : ComputableInPolyTime right enc encBits) :
      ComputableInPolyTime (fun a => eqFlag (left a) (right a)) enc encBits :=
    eqFlag_polyTime.comp (hl.prod hr)
  fin_cases p
  · exact selectFn hh (crossingNode_polyTime false hx hy)
      (selectFn (eqFn hy hzero) hext (crossingNode_polyTime true hx hyp))
  · exact selectFn hh
      (selectFn (eqFn hy hmax) hext (crossingNode_polyTime false hx hys))
      (selectFn (eqFn hx hmax) hext (crossingNode_polyTime true hxs hy))
  · exact selectFn hh
      (selectFn (eqFn hx hzero) hext (crossingNode_polyTime false hxp hy))
      (crossingNode_polyTime true hx hy)

private theorem lsbValue_replicate (b : ℕ) :
    lsbValue (List.replicate b false) = 0 ∧
      lsbValue (List.replicate b true) = 2 ^ b - 1 := by
  refine ⟨lsbValue_replicate_false b, ?_⟩
  have h := lsbValue_replicate_true b
  omega

private theorem zeroBits_iff {b x : ℕ} (hx : x < 2 ^ b) :
    lowBits b x = List.replicate b false ↔ x = 0 := by
  constructor
  · intro he
    have h := congrArg lsbValue he
    simpa [lsbValue_lowBits hx, (lsbValue_replicate b).1] using h
  · intro he
    apply lsbValue_injective (by simp)
    rw [lsbValue_lowBits hx, (lsbValue_replicate b).1]
    exact he

private theorem maxBits_iff {b x : ℕ} (hx : x < 2 ^ b) :
    lowBits b x = List.replicate b true ↔ x + 1 = 2 ^ b := by
  constructor
  · intro he
    have h := congrArg lsbValue he
    rw [lsbValue_lowBits hx, (lsbValue_replicate b).2] at h
    omega
  · intro he
    apply lsbValue_injective (by simp)
    rw [lsbValue_lowBits hx, (lsbValue_replicate b).2]
    omega

private theorem succBits_encode {b x : ℕ} (hx : x + 1 < 2 ^ b) :
    gridSuccBits (lowBits b x) = lowBits b (x + 1) := by
  have hx' : x < 2 ^ b := by omega
  apply lsbValue_injective (by simp)
  rw [gridSuccBits_value_of_lt _ (by simpa [lsbValue_lowBits hx'] using hx),
    lsbValue_lowBits hx', lsbValue_lowBits hx]

private theorem predBits_encode {b x : ℕ} (hx : x < 2 ^ b) (hp : 0 < x) :
    gridPredBits (lowBits b x) = lowBits b (x - 1) := by
  have hx' : x - 1 < 2 ^ b := by omega
  apply lsbValue_injective (by simp)
  rw [gridPredBits_value_of_pos _ (by simpa [lsbValue_lowBits hx] using hp),
    lsbValue_lowBits hx, lsbValue_lowBits hx']

private theorem case_eqFlag (a b yes no : List Bool) :
    select (eqFlag a b) yes no = if a = b then yes else no := by
  simp [select, eqFlag]

/-- Binary crossing agrees exactly with geometric adjacency on every valid triangle. -/
theorem gridCrossWord_encode (ruler : List Bool) (incoming : Bool) (p : Fin 3)
    (t : GridTriangle) (hv : ValidTriangle (2 ^ ruler.length) t) :
    gridCrossWord ruler incoming p (encodeGridNode ruler.length (some t)) =
      match across (2 ^ ruler.length) t p with
      | none => if incoming then encodeGridNode ruler.length none
          else encodeGridNode ruler.length (some t)
      | some (u, _) => encodeGridNode ruler.length (some u) := by
  rcases t with ⟨x, y, upper⟩
  rcases hv with ⟨hx, hy⟩
  have hxb : gridNodeXBits ruler (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      lowBits ruler.length x := by simp [gridNodeXBits, encodeGridNode]
  have hyb : gridNodeYBits ruler (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      lowBits ruler.length y := by simp [gridNodeYBits, encodeGridNode]
  have hh : gridNodeHalfFlag (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      [upper] := by simp [gridNodeHalfFlag, encodeGridNode]
  cases upper <;> fin_cases p
  all_goals simp only [gridCrossWord, hxb, hyb, hh]
  all_goals simp [case_eqFlag, zeroBits_iff hx, zeroBits_iff hy,
    maxBits_iff hx, maxBits_iff hy, across]
  all_goals first | rfl | (split_ifs <;> simp_all [gridWidthWord, encodeGridNode])
  all_goals first
    | omega
    | exact succBits_encode (by omega)
    | exact predBits_encode hx (by omega)
    | exact predBits_encode hy (by omega)

end GameTheory.Complexity.Backend
