module

public import GameTheoryComplexity.Backend.GridRoutingCodec
public import GameTheoryComplexity.Backend.EndOfLineMachineOps

@[expose] public section

/-! Polynomial-time routing codec operations use word rulers for both coordinate
blocks. Extraction preserves the existing bits; acceptance checks only the exact
word length, since every correctly sized word denotes a point. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

/-- An all-zero ruler for one routing coordinate block. -/
def routingCoordinateRuler (ruler : List Bool) : List Bool :=
  List.replicate (routingCoordinateWidth ruler.length) false

/-- The all-zero word representing the routing grid origin. -/
def routingPointZeroWord (ruler : List Bool) : List Bool :=
  List.replicate (routingPointWidth ruler.length) false

/-- Extract the first coordinate's little-endian block. -/
def routingPointXBits (ruler word : List Bool) : List Bool :=
  word.take (routingCoordinateWidth ruler.length)

/-- Extract the second coordinate's little-endian block. -/
def routingPointYBits (ruler word : List Bool) : List Bool :=
  word.drop (routingCoordinateWidth ruler.length)

/-- Accept exactly words with two full coordinate blocks. -/
def routingPointAcceptFlag (ruler word : List Bool) : List Bool :=
  [decide (word.length = routingPointWidth ruler.length)]

/-- The coordinate ruler has exactly the codec's coordinate width. -/
@[simp] theorem routingCoordinateRuler_length (ruler : List Bool) :
    (routingCoordinateRuler ruler).length = routingCoordinateWidth ruler.length := by
  simp [routingCoordinateRuler]

/-- The origin word has exactly the codec's point width. -/
@[simp] theorem routingPointZeroWord_length (ruler : List Bool) :
    (routingPointZeroWord ruler).length = routingPointWidth ruler.length := by
  simp [routingPointZeroWord]

/-- The origin word agrees with the canonical point encoder. -/
theorem routingPointZeroWord_eq_encode (ruler : List Bool) :
    routingPointZeroWord ruler = encodeRoutingPoint ruler.length (0, 0) := by
  simp [routingPointZeroWord]

/-- The first field extractor returns exactly the encoded first coordinate bits. -/
theorem routingPointXBits_encode (ruler : List Bool) (point : ℕ × ℕ) :
    routingPointXBits ruler (encodeRoutingPoint ruler.length point) =
      lowBits (routingCoordinateWidth ruler.length) point.1 := by
  simp [routingPointXBits, encodeRoutingPoint]

/-- The second field extractor returns exactly the encoded second coordinate bits. -/
theorem routingPointYBits_encode (ruler : List Bool) (point : ℕ × ℕ) :
    routingPointYBits ruler (encodeRoutingPoint ruler.length point) =
      lowBits (routingCoordinateWidth ruler.length) point.2 := by
  simp [routingPointYBits, encodeRoutingPoint]

/-- The acceptance control tests exactly the advertised routing word width. -/
theorem routingPointAcceptFlag_width (ruler word : List Bool) :
    routingPointAcceptFlag ruler word = [true] ↔ word.length = routingPointWidth ruler.length := by
  simp [routingPointAcceptFlag]

/-- The acceptance control agrees exactly with successful point decoding. -/
theorem routingPointAcceptFlag_accept (ruler word : List Bool) :
    routingPointAcceptFlag ruler word = [true] ↔
      ∃ point, decodeRoutingPoint ruler.length word = some point := by
  rw [routingPointAcceptFlag_width]
  constructor
  · intro hw
    exact ⟨(lsbValue (word.take (routingCoordinateWidth ruler.length)),
      lsbValue (word.drop (routingCoordinateWidth ruler.length))),
      by simp [decodeRoutingPoint, hw]⟩
  · rintro ⟨point, hd⟩
    exact decodeRoutingPoint_length hd

private theorem coordinateWidth_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun a => routingCoordinateWidth (ruler a).length) enc encUnary :=
  unary_add' (unary_mul' (const 2) (length_bits.comp hr)) (const 3)

private theorem pointWidth_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun a => routingPointWidth (ruler a).length) enc encUnary :=
  unary_mul' (const 2) (coordinateWidth_polyTime hr)

/-- Coordinate-ruler construction charges its entire unary output. -/
@[fun_prop] theorem routingCoordinateRuler_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun a => routingCoordinateRuler (ruler a)) enc encBits :=
  (bitsReplicate false).comp (coordinateWidth_polyTime hr)

@[fun_prop] theorem routingPointZeroWord_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun a => routingPointZeroWord (ruler a)) enc encBits :=
  (bitsReplicate false).comp (pointWidth_polyTime hr)

@[fun_prop] theorem routingPointXBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => routingPointXBits (ruler a) (word a)) enc encBits :=
  hw.bitsTakeWithInput (coordinateWidth_polyTime hr)

@[fun_prop] theorem routingPointYBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => routingPointYBits (ruler a) (word a)) enc encBits :=
  hw.bitsDropWithInput (coordinateWidth_polyTime hr)

@[fun_prop] theorem routingPointAcceptFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => routingPointAcceptFlag (ruler a) (word a)) enc encBits :=
  bitsCons (decide_eq' (length_bits.comp hw) (pointWidth_polyTime hr)) (const [])

end GameTheory.Complexity.Backend
