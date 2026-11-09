module

public import GameTheoryComplexity.Backend.BrouwerPointCodec
public import GameTheory.Math.GridBrouwerSixthGeometry
public import GameTheoryComplexity.Backend.SpernerGridCodecMachine
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheoryComplexity.Backend.GridRoutingDivision
public import GameTheoryComplexity.Backend.GridRoutingArithmetic

@[expose] public section

/-! Point location uses binary division by six and a constant remainder table.
Boundary coordinates are clamped to the final grid cell. The reverse decoder
emits the rational barycenter using shifts, addition, and fixed-width padding. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Numerator field ruler. -/
def brouwerPointRuler (ruler : List Bool) : List Bool := ruler ++ [false, false, false]

/-- Binary representation of the largest numerator, six times the grid size. -/
def brouwerPointBoundBits (ruler : List Bool) : List Bool :=
  routingShiftBits ruler [false, true, true]

/-- First numerator field. -/
def brouwerPointXBits (ruler word : List Bool) : List Bool :=
  word.take (brouwerPointRuler ruler).length

/-- Second numerator field. -/
def brouwerPointYBits (ruler word : List Bool) : List Bool :=
  word.drop (brouwerPointRuler ruler).length

/-- Clamp a boundary quotient to the all-one last-cell coordinate. -/
def brouwerCellBits (ruler bits : List Bool) : List Bool :=
  select (routingEQFlag bits (brouwerPointBoundBits ruler))
    (List.replicate ruler.length true)
    (routingPadBits ruler (routingDivSixBits bits))

/-- The final cell has residual six at the closed square's upper boundary. -/
def brouwerOffsetBits (ruler bits : List Bool) : List Bool :=
  select (routingEQFlag bits (brouwerPointBoundBits ruler))
    [false, true, true] (routingModSixBits bits)

/-- Produce the containing triangle word from the rational point word. -/
def brouwerLocateWord (ruler word : List Bool) : List Bool :=
  let x := brouwerPointXBits ruler word
  let y := brouwerPointYBits ruler word
  [true] ++ routingLTFlag (brouwerOffsetBits ruler x) (brouwerOffsetBits ruler y) ++
    brouwerCellBits ruler x ++ brouwerCellBits ruler y

/-- Source-aware point-to-triangle answer conversion. -/
def brouwerLocate (input word : List Bool) : List Bool :=
  brouwerLocateWord (CircuitWords.first input) word

/-- Numerator of one barycenter coordinate. -/
def brouwerBarycenterCoordinate (ruler coordinate offset : List Bool) : List Bool :=
  routingPadBits (brouwerPointRuler ruler) (routingAddBits (routingSixBits coordinate) offset)

/-- Decode a triangle to its rational barycenter point word. -/
def brouwerBarycenterWord (ruler word : List Bool) : List Bool :=
  brouwerBarycenterCoordinate ruler (gridNodeXBits ruler word)
      (select (gridNodeHalfFlag word) [false, true] [false, false, true]) ++
    brouwerBarycenterCoordinate ruler (gridNodeYBits ruler word)
      (select (gridNodeHalfFlag word) [false, false, true] [false, true])

/-- Source-aware triangle-to-point answer conversion. -/
def brouwerBarycenter (input word : List Bool) : List Bool :=
  brouwerBarycenterWord (CircuitWords.first input) word

@[simp] theorem brouwerPointRuler_length (ruler : List Bool) :
    (brouwerPointRuler ruler).length = pointCoordinateWidth ruler.length := by
  simp [brouwerPointRuler, pointCoordinateWidth]

theorem brouwerPointBoundBits_value (ruler : List Bool) :
    lsbValue (brouwerPointBoundBits ruler) = 6 * 2 ^ ruler.length := by
  rw [brouwerPointBoundBits, routingShiftBits_value]
  simp [lsbValue, Nat.mul_comm]

@[simp] theorem brouwerCellBits_length (ruler bits : List Bool) :
    (brouwerCellBits ruler bits).length = ruler.length := by
  rw [brouwerCellBits, routingEQFlag_value]
  by_cases h : lsbValue bits = lsbValue (brouwerPointBoundBits ruler) <;>
    simp [h, select]

@[simp] theorem brouwerOffsetBits_length (ruler bits : List Bool) :
    (brouwerOffsetBits ruler bits).length = 3 := by
  rw [brouwerOffsetBits, routingEQFlag_value]
  by_cases h : lsbValue bits = lsbValue (brouwerPointBoundBits ruler) <;>
    simp [h, select]

theorem brouwerCellBits_value (ruler bits : List Bool)
    (h : lsbValue bits ≤ 6 * 2 ^ ruler.length) :
    lsbValue (brouwerCellBits ruler bits) =
      sixthCellIndex (2 ^ ruler.length) (lsbValue bits) := by
  rw [brouwerCellBits, routingEQFlag_value, brouwerPointBoundBits_value]
  have hp : 0 < 2 ^ ruler.length := by positivity
  by_cases he : lsbValue bits = 6 * 2 ^ ruler.length
  · have hones := lsbValue_replicate_true ruler.length
    have hv : lsbValue (List.replicate ruler.length true) = 2 ^ ruler.length - 1 := by omega
    simp [he, select, hv, sixthCellIndex]
  · have hq : lsbValue bits / 6 < 2 ^ ruler.length := by omega
    simp only [he, decide_false, select_cons, Bool.false_eq_true, ↓reduceIte]
    rw [routingPadBits_value, routingDivSixBits_value, Nat.mod_eq_of_lt hq]
    exact (Nat.min_eq_left (by omega)).symm

theorem brouwerOffsetBits_value (ruler bits : List Bool)
    (h : lsbValue bits ≤ 6 * 2 ^ ruler.length) :
    lsbValue (brouwerOffsetBits ruler bits) =
      sixthOffset (2 ^ ruler.length) (lsbValue bits) := by
  rw [brouwerOffsetBits, routingEQFlag_value, brouwerPointBoundBits_value]
  have hp : 0 < 2 ^ ruler.length := by positivity
  by_cases he : lsbValue bits = 6 * 2 ^ ruler.length
  · simp only [he, decide_true, select_cons, ↓reduceIte]
    have hb : sixthCellIndex (2 ^ ruler.length) (6 * 2 ^ ruler.length) =
        2 ^ ruler.length - 1 := by simp [sixthCellIndex]
    unfold sixthOffset
    rw [hb]
    norm_num [lsbValue]
    omega
  · have hq : lsbValue bits / 6 ≤ 2 ^ ruler.length - 1 := by omega
    simp only [he, decide_false, select_cons, Bool.false_eq_true, ↓reduceIte]
    rw [routingModSixBits_value]
    unfold sixthOffset sixthCellIndex
    rw [Nat.min_eq_left hq]
    omega

theorem brouwerCellBits_eq (ruler bits : List Bool)
    (h : lsbValue bits ≤ 6 * 2 ^ ruler.length) :
    brouwerCellBits ruler bits = lowBits ruler.length
      (sixthCellIndex (2 ^ ruler.length) (lsbValue bits)) := by
  have he := lowBits_lsbValue (brouwerCellBits ruler bits)
  rw [brouwerCellBits_length, brouwerCellBits_value ruler bits h] at he
  exact he.symm

theorem brouwerOffsetBits_eq (ruler bits : List Bool)
    (h : lsbValue bits ≤ 6 * 2 ^ ruler.length) :
    brouwerOffsetBits ruler bits = lowBits 3
      (sixthOffset (2 ^ ruler.length) (lsbValue bits)) := by
  have he := lowBits_lsbValue (brouwerOffsetBits ruler bits)
  rw [brouwerOffsetBits_length, brouwerOffsetBits_value ruler bits h] at he
  exact he.symm

theorem brouwerLocateWord_eq {ruler word : List Bool} {p : ℕ × ℕ}
    (h : decodeBrouwerPoint ruler.length word = some p) :
    brouwerLocateWord ruler word =
      encodeGridNode ruler.length (some (sixthTriangle (2 ^ ruler.length) p.1 p.2)) := by
  obtain ⟨_, hx, hy, hvx, hvy⟩ := decodeBrouwerPoint_properties h
  have hxx : lsbValue (brouwerPointXBits ruler word) = p.1 := by
    simpa only [brouwerPointXBits, brouwerPointRuler_length] using hvx
  have hyy : lsbValue (brouwerPointYBits ruler word) = p.2 := by
    simpa only [brouwerPointYBits, brouwerPointRuler_length] using hvy
  unfold brouwerLocateWord
  dsimp only
  rw [routingLTFlag_value, brouwerOffsetBits_value _ _ (by simpa [hxx] using hx),
    brouwerOffsetBits_value _ _ (by simpa [hyy] using hy),
    brouwerCellBits_eq _ _ (by simpa [hxx] using hx),
    brouwerCellBits_eq _ _ (by simpa [hyy] using hy), hxx, hyy]
  rfl

/-- Integer numerators of a triangle's barycenter at sixth-grid resolution. -/
abbrev brouwerBarycenterNumerators (t : GridTriangle) : ℕ × ℕ := sixthBarycenterNumerators t

theorem brouwerBarycenterNumerators_bounds {b : ℕ} {t : GridTriangle}
    (h : ValidTriangle (2 ^ b) t) :
    (brouwerBarycenterNumerators t).1 ≤ 6 * 2 ^ b ∧
      (brouwerBarycenterNumerators t).2 ≤ 6 * 2 ^ b := by
  exact sixthBarycenterNumerators_bounds h

theorem brouwerBarycenterCoordinate_eq (ruler coordinate offset : List Bool) :
    brouwerBarycenterCoordinate ruler coordinate offset =
      lowBits (pointCoordinateWidth ruler.length)
        (6 * lsbValue coordinate + lsbValue offset) := by
  rw [brouwerBarycenterCoordinate, routingPadBits_eq_lowBits,
    brouwerPointRuler_length, routingAddBits_value, routingSixBits_value]

theorem brouwerBarycenterWord_eq {ruler word : List Bool} {t : GridTriangle}
    (h : decodeGridNode ruler.length word = some (some t)) :
    brouwerBarycenterWord ruler word =
      encodeBrouwerPoint ruler.length (brouwerBarycenterNumerators t) := by
  have hv := decodeGridNode_valid h t rfl
  rw [← encodeGridNode_decode h]
  unfold brouwerBarycenterWord
  rw [brouwerBarycenterCoordinate_eq, brouwerBarycenterCoordinate_eq]
  have hx : lsbValue (gridNodeXBits ruler (encodeGridNode ruler.length (some t))) = t.x := by
    simp [gridNodeXBits, encodeGridNode, lsbValue_lowBits hv.1]
  have hy : lsbValue (gridNodeYBits ruler (encodeGridNode ruler.length (some t))) = t.y := by
    simp [gridNodeYBits, encodeGridNode, lsbValue_lowBits hv.2]
  rw [hx, hy]
  cases ht : t.upper <;>
    simp [encodeBrouwerPoint, brouwerBarycenterNumerators, sixthBarycenterNumerators, gridNodeHalfFlag,
      encodeGridNode, select, ht, lsbValue]

/-- The numerator ruler charges its full materialized width. -/
@[fun_prop] theorem brouwerPointRuler_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun z => brouwerPointRuler (ruler z)) enc encBits := by
  exact bitsAppend hruler (const [false, false, false])

/-- The upper-bound numerator is computed by a native binary shift. -/
@[fun_prop] theorem brouwerPointBoundBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun z => brouwerPointBoundBits (ruler z)) enc encBits := by
  exact routingShiftBits_polyTime hruler (const [false, true, true])

/-- Horizontal fields use native unary addressing. -/
@[fun_prop] theorem brouwerPointXBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerPointXBits (ruler z) (word z)) enc encBits := by
  exact bitsTakeWithInput hword (length_bits.comp (brouwerPointRuler_polyTime hruler))

/-- Vertical fields use native unary addressing. -/
@[fun_prop] theorem brouwerPointYBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerPointYBits (ruler z) (word z)) enc encBits := by
  exact bitsDropWithInput hword (length_bits.comp (brouwerPointRuler_polyTime hruler))

/-- Closed-boundary clamping charges the complete binary quotient and output field. -/
@[fun_prop] theorem brouwerCellBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler bits : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hbits : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => brouwerCellBits (ruler z) (bits z)) enc encBits := by
  have hguard := routingEQFlag_polyTime hbits (brouwerPointBoundBits_polyTime hruler)
  have hone := (bitsReplicate true).comp (length_bits.comp hruler)
  have hquot := routingPadBits_polyTime hruler (routingDivSixBits_polyTime hbits)
  exact select_polyTime.comp (hguard.prod (hone.prod hquot))

/-- Local offsets charge native remainder arithmetic and the closed-boundary guard. -/
@[fun_prop] theorem brouwerOffsetBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler bits : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hbits : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => brouwerOffsetBits (ruler z) (bits z)) enc encBits := by
  exact select_polyTime.comp
    ((routingEQFlag_polyTime hbits (brouwerPointBoundBits_polyTime hruler)).prod
      ((const [false, true, true]).prod (routingModSixBits_polyTime hbits)))

/-- Point location composes the exact native coordinate fields and constant-size selector. -/
@[fun_prop] theorem brouwerLocateWord_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerLocateWord (ruler z) (word z)) enc encBits := by
  unfold brouwerLocateWord
  fun_prop

/-- Barycenter coordinates charge retained-carry arithmetic and complete fixed-width output. -/
@[fun_prop] theorem brouwerBarycenterCoordinate_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler coordinate offset : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hcoordinate : ComputableInPolyTime coordinate enc encBits)
    (hoffset : ComputableInPolyTime offset enc encBits) :
    ComputableInPolyTime (fun z => brouwerBarycenterCoordinate (ruler z) (coordinate z) (offset z)) enc encBits := by
  exact routingPadBits_polyTime (brouwerPointRuler_polyTime hruler)
    (routingAddBits_polyTime (routingSixBits_polyTime hcoordinate) hoffset)

/-- Both barycenter coordinates use native triangle fields and Boolean half selection. -/
@[fun_prop] theorem brouwerBarycenterWord_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerBarycenterWord (ruler z) (word z)) enc encBits := by
  have hx := gridNodeXBits_polyTime hruler hword
  have hy := gridNodeYBits_polyTime hruler hword
  have hhalf := gridNodeHalfFlag_polyTime hword
  have hox := select_polyTime.comp (hhalf.prod
    ((const [false, true]).prod (const [false, false, true])))
  have hoy := select_polyTime.comp (hhalf.prod
    ((const [false, false, true]).prod (const [false, true])))
  exact bitsAppend (brouwerBarycenterCoordinate_polyTime hruler hx hox)
    (brouwerBarycenterCoordinate_polyTime hruler hy hoy)

/-- Source-aware point location charges public frame decoding and native coordinate arithmetic. -/
@[fun_prop] theorem brouwerLocate_polyTime
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hinput : ComputableInPolyTime input enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerLocate (input z) (word z)) enc encBits := by
  exact brouwerLocateWord_polyTime (CircuitWords.first_polyTime.comp hinput) hword

/-- Source-aware barycenter conversion charges public frame decoding and full output. -/
@[fun_prop] theorem brouwerBarycenter_polyTime
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hinput : ComputableInPolyTime input enc encBits)
    (hword : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => brouwerBarycenter (input z) (word z)) enc encBits := by
  exact brouwerBarycenterWord_polyTime (CircuitWords.first_polyTime.comp hinput) hword

end GameTheory.Complexity.Backend
