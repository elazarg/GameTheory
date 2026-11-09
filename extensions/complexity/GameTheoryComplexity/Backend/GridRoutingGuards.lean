module

public import GameTheoryComplexity.Backend.GridRoutingArithmetic
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheory.Math.GridWireBounds

@[expose] public section

/-! Binary rectangle guards reject points outside the live routing image before
local owner queries. Their bounds use shifts of the vertex-width ruler. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

/-- The binary capacity of an original vertex label. -/
def routingVertexBoundBits (ruler : List Bool) : List Bool := routingShiftBits ruler [true]

/-- The squared vertex-label capacity needed for the allocated wire columns. -/
def routingSquaredBoundBits (ruler : List Bool) : List Bool :=
  routingShiftBits ruler (routingVertexBoundBits ruler)

/-- Check the exact rectangle containing every live routed point. -/
def routingRectangleFlag (ruler x y : List Bool) : List Bool :=
  andFlag (routingLTFlag x (routingTripleBits (routingSquaredBoundBits ruler)))
    (routingLTFlag y (routingSixBits (routingVertexBoundBits ruler)))

/-- The vertex capacity is encoded using one more bit than the vertex ruler. -/
@[simp] theorem routingVertexBoundBits_length (ruler : List Bool) :
    (routingVertexBoundBits ruler).length = ruler.length + 1 := by
  simp [routingVertexBoundBits]

/-- The vertex-bound word represents exactly the ruler's power of two. -/
theorem routingVertexBoundBits_value (ruler : List Bool) :
    lsbValue (routingVertexBoundBits ruler) = 2 ^ ruler.length := by
  rw [routingVertexBoundBits, routingShiftBits_value]
  simp only [show lsbValue [true] = 1 from rfl, Nat.mul_one]

/-- The squared capacity word has twice the vertex ruler's width plus one. -/
@[simp] theorem routingSquaredBoundBits_length (ruler : List Bool) :
    (routingSquaredBoundBits ruler).length = 2 * ruler.length + 1 := by
  simp [routingSquaredBoundBits]
  omega

/-- The column allocation capacity is exactly the square of the vertex capacity. -/
theorem routingSquaredBoundBits_value (ruler : List Bool) :
    lsbValue (routingSquaredBoundBits ruler) =
      2 ^ ruler.length * 2 ^ ruler.length := by
  rw [routingSquaredBoundBits, routingShiftBits_value, routingVertexBoundBits_value]

/-- Rectangle membership is exact even for noncanonical binary coordinates. -/
theorem routingRectangleFlag_value (ruler x y : List Bool) :
    routingRectangleFlag ruler x y = [decide
      (lsbValue x < 3 * 2 ^ ruler.length * 2 ^ ruler.length ∧
        lsbValue y < 6 * 2 ^ ruler.length)] := by
  by_cases hx : lsbValue x < 3 * (2 ^ ruler.length * 2 ^ ruler.length) <;>
    by_cases hy : lsbValue y < 6 * 2 ^ ruler.length <;>
    simp [routingRectangleFlag, routingLTFlag_value, routingTripleBits_value,
      routingSquaredBoundBits_value, routingSixBits_value, routingVertexBoundBits_value,
      andFlag, Nat.mul_assoc, hx, hy]

/-- The rectangle guard accepts exactly the bounds of the routed image. -/
theorem routingRectangleFlag_accept (ruler x y : List Bool) :
    routingRectangleFlag ruler x y = [true] ↔
      lsbValue x < 3 * 2 ^ ruler.length * 2 ^ ruler.length ∧
        lsbValue y < 6 * 2 ^ ruler.length := by
  rw [routingRectangleFlag_value]
  simp

/-- Rectangle membership always produces one Boolean flag. -/
@[simp] theorem routingRectangleFlag_length (ruler x y : List Bool) :
    (routingRectangleFlag ruler x y).length = 1 := by
  rw [routingRectangleFlag_value]
  rfl

/-- The vertex capacity is computed from its materialized width ruler. -/
@[fun_prop] theorem routingVertexBoundBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits):
    ComputableInPolyTime (fun z => routingVertexBoundBits (ruler z)) enc encBits := by
  unfold routingVertexBoundBits
  fun_prop

/-- The squared capacity charges both shifts of the width ruler. -/
@[fun_prop] theorem routingSquaredBoundBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits):
    ComputableInPolyTime (fun z => routingSquaredBoundBits (ruler z)) enc encBits := by
  unfold routingSquaredBoundBits
  fun_prop

/-- Rectangle guards compose native ruler and coordinate producers. -/
@[fun_prop] theorem routingRectangleFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits):
    ComputableInPolyTime (fun z => routingRectangleFlag (ruler z) (x z) (y z)) enc encBits := by
  unfold routingRectangleFlag
  fun_prop

/-- No coordinate outside the rectangle can decode to a live routed label. -/
theorem routingRectangleFlag_decode_none (ruler x y : List Bool) (P S : ℕ → ℕ)
    (h : routingRectangleFlag ruler x y ≠ [true]) :
    decodeWireNode (2 ^ ruler.length) P S (lsbValue x, lsbValue y) = none := by
  cases hd : decodeWireNode (2 ^ ruler.length) P S (lsbValue x, lsbValue y) with
  | none => rfl
  | some node =>
    obtain ⟨hl, he⟩ := decodeWireNode_eq_some_iff.mp hd
    have hb := routedCoordinate_bounds hl
    rw [he] at hb
    exact False.elim (h ((routingRectangleFlag_accept ruler x y).mpr hb))

/-- Both global routed pointers isolate every coordinate outside the rectangle. -/
theorem routingRectangleFlag_background (ruler x y : List Bool) (P S : ℕ → ℕ)
    (h : routingRectangleFlag ruler x y ≠ [true]) :
    gridRoutedPredecessor (2 ^ ruler.length) P S (lsbValue x, lsbValue y) =
        (lsbValue x, lsbValue y) ∧
      gridRoutedSuccessor (2 ^ ruler.length) P S (lsbValue x, lsbValue y) =
        (lsbValue x, lsbValue y) :=
  gridRouted_background (routingRectangleFlag_decode_none ruler x y P S h)

/-- No coordinate outside the rectangle is the center of a live crossing. -/
theorem routingRectangleFlag_crossing_none (ruler x y : List Bool) (P S : ℕ → ℕ)
    (h : routingRectangleFlag ruler x y ≠ [true]) :
    crossingOwners (2 ^ ruler.length) P S (lsbValue x, lsbValue y) = none := by
  cases hc : crossingOwners (2 ^ ruler.length) P S (lsbValue x, lsbValue y) with
  | none => rfl
  | some owners =>
    obtain ⟨hi, _, hsi, _, _, _, _, hh, _⟩ := crossingOwners_sound hc
    have hw : onWire (2 ^ ruler.length) owners.1 (S owners.1)
        (lsbValue x, lsbValue y) := by
      rcases hh.2.2 with hy | hy
      · exact Or.inl ⟨hy, Nat.le_of_lt hh.2.1⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hy, Nat.le_of_lt hh.2.1⟩))
    exact False.elim (h ((routingRectangleFlag_accept ruler x y).mpr (onWire_bounds hi hsi hw)))

end GameTheory.Complexity.Backend
