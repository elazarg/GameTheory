module

public import GameTheoryComplexity.Backend.GridRoutingCodecMachine
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheoryComplexity.Backend.GridRoutingDivision
public import GameTheory.Math.GridWire

@[expose] public section

/-! An original routed vertex has vertical coordinate six times its label.
Binary division followed by a fixed-width low-bit extraction recovers that label
in polynomial time, independently of the coordinate's numeric magnitude. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString GameTheory.Math.GridWire

/-- Recover a `b`-bit vertex label from the routing word's vertical coordinate. -/
def routingEndpointLabelBits (ruler word : List Bool) : List Bool :=
  (routingDivSixBits (routingPointYBits ruler word)).take ruler.length

/-- An accepted routing word yields exactly the original vertex label width. -/
theorem routingEndpointLabelBits_length {ruler word : List Bool}
    (hw : word.length = routingPointWidth ruler.length) :
    (routingEndpointLabelBits ruler word).length = ruler.length := by
  simp only [routingEndpointLabelBits, List.length_take, routingDivSixBits_length,
    routingPointYBits, List.length_drop, hw, routingPointWidth, routingCoordinateWidth]
  omega

/-- Decoding an original vertex recovers its bounded label as a natural number. -/
theorem routingEndpointLabelBits_value {ruler word : List Bool} {i : ℕ}
    (hd : decodeRoutingPoint ruler.length word = some (vertexPoint i))
    (hi : i < 2 ^ ruler.length) : lsbValue (routingEndpointLabelBits ruler word) = i := by
  have hw := decodeRoutingPoint_length hd
  have hy : lsbValue (routingPointYBits ruler word) = 6 * i := by
    unfold decodeRoutingPoint at hd
    rw [ite_eq_left hw] at hd
    have h := congrArg Prod.snd (Option.some.inj hd)
    exact h
  have hq : lsbValue (routingDivSixBits (routingPointYBits ruler word)) = i := by
    rw [routingDivSixBits_value, hy]
    simp
  unfold routingEndpointLabelBits
  rw [routing_lsbValue_take, hq, Nat.mod_eq_of_lt hi]

/-- The recovered label word is the canonical little-endian encoding of the vertex. -/
theorem routingEndpointLabelBits_eq_bits {ruler word : List Bool} {i : ℕ}
    (hd : decodeRoutingPoint ruler.length word = some (vertexPoint i))
    (hi : i < 2 ^ ruler.length) :
    routingEndpointLabelBits ruler word = lowBits ruler.length i := by
  have h := lowBits_lsbValue (routingEndpointLabelBits ruler word)
  rw [routingEndpointLabelBits_length (decodeRoutingPoint_length hd),
    routingEndpointLabelBits_value hd hi] at h
  exact h.symm

/-- Label extraction composes native word producers with the explicit field width. -/
@[fun_prop] theorem routingEndpointLabelBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => routingEndpointLabelBits (ruler z) (word z)) enc encBits :=
  bitsTakeWithInput (routingDivSixBits_polyTime (routingPointYBits_polyTime hr hw))
    (length_bits.comp hr)

end GameTheory.Complexity.Backend
