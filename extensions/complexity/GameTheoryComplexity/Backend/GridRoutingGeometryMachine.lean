module

public import GameTheoryComplexity.Backend.GridRoutingArithmetic
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheoryComplexity.Backend.GridRoutingDivision
public import GameTheory.Math.GridWire
public import GameTheory.Math.GridCrossingLocator

@[expose] public section

/-! Binary route geometry uses exact arithmetic with retained carries.
Comparisons inspect numeric values, so unequal widths and high zero padding
do not change membership in a wire segment or crossing interior. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

/-- Allocate the column `3 * (2^b * i + j)` without numeric iteration. -/
def routingColumnBits (ruler i j : List Bool) : List Bool :=
  routingTripleBits (routingAddBits (routingShiftBits ruler i) j)

/-- The incoming horizontal row lies three units above the target vertex. -/
def routingTargetRowBits (j : List Bool) : List Bool :=
  routingAddBits (routingSixBits j) [true, true]

/-- Closed interval membership, allowing either ordering of the endpoints. -/
def routingBetweenFlag (a x c : List Bool) : List Bool :=
  orFlag (andFlag (routingLEFlag a x) (routingLEFlag x c))
    (andFlag (routingLEFlag c x) (routingLEFlag x a))

/-- Strict interval membership, allowing either ordering of the endpoints. -/
def routingStrictBetweenFlag (a x c : List Bool) : List Bool :=
  orFlag (andFlag (routingLTFlag a x) (routingLTFlag x c))
    (andFlag (routingLTFlag c x) (routingLTFlag x a))

/-- Check all four closed segments of a source-indexed route. -/
def routingOnWireFlag (ruler i j x y : List Bool) : List Bool :=
  let col := routingColumnBits ruler i j
  let source := routingSixBits i
  let target := routingSixBits j
  let upper := routingTargetRowBits j
  orFlag (andFlag (routingEQFlag y source) (routingLEFlag x col))
    (orFlag (andFlag (routingEQFlag x col) (routingBetweenFlag source y upper))
      (orFlag (andFlag (routingEQFlag y upper) (routingLEFlag x col))
        (andFlag (routingEQFlag x [])
          (andFlag (routingLEFlag target y) (routingLEFlag y upper)))))

/-- Check the strict horizontal interior used to validate a proper crossing. -/
def routingHorizontalInteriorFlag (ruler i j x y : List Bool) : List Bool :=
  andFlag (routingLTFlag [] x) (andFlag (routingLTFlag x (routingColumnBits ruler i j))
    (orFlag (routingEQFlag y (routingSixBits i))
      (routingEQFlag y (routingTargetRowBits j))))

/-- Check the strict vertical interior used to validate a proper crossing. -/
def routingVerticalInteriorFlag (ruler i j x y : List Bool) : List Bool :=
  andFlag (routingEQFlag x (routingColumnBits ruler i j))
    (routingStrictBetweenFlag (routingSixBits i) y (routingTargetRowBits j))

/-- Round one coordinate to its nearest spacing-three crossing center. -/
def routingCenterBits (bits : List Bool) : List Bool :=
  routingTripleBits (routingDivThreeBits (routingAddBits bits [true]))

/-- Recover the raw source field of a routing column, retaining overflow bits. -/
def routingVerticalOwnerBits (ruler x : List Bool) : List Bool :=
  (routingDivThreeBits x).drop ruler.length

private theorem andFlag_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

private theorem orFlag_decide (a b : Prop) [Decidable a] [Decidable b] :
    orFlag [decide a] [decide b] = [decide (a ∨ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, orFlag]

/-- Column allocation agrees exactly with the natural coordinate formula. -/
theorem routingColumnBits_value (ruler i j : List Bool) :
    lsbValue (routingColumnBits ruler i j) =
      wireColumn (2 ^ ruler.length) (lsbValue i) (lsbValue j) := by
  simp only [routingColumnBits, routingTripleBits_value, routingAddBits_value,
    routingShiftBits_value, wireColumn]

/-- Target row construction keeps the final carry. -/
theorem routingTargetRowBits_value (j : List Bool) :
    lsbValue (routingTargetRowBits j) = 6 * lsbValue j + 3 := by
  simp only [routingTargetRowBits, routingAddBits_value, routingSixBits_value]
  rfl

/-- The closed interval flag is exact even for differently padded words. -/
theorem routingBetweenFlag_value (a x c : List Bool) :
    routingBetweenFlag a x c = [decide (min (lsbValue a) (lsbValue c) ≤
      lsbValue x ∧ lsbValue x ≤ max (lsbValue a) (lsbValue c))] := by
  simp only [routingBetweenFlag, routingLEFlag_value, andFlag_decide, orFlag_decide]
  congr 2
  apply propext
  omega

/-- The strict interval flag excludes both endpoints, including equal endpoints. -/
theorem routingStrictBetweenFlag_value (a x c : List Bool) :
    routingStrictBetweenFlag a x c = [decide (min (lsbValue a) (lsbValue c) <
      lsbValue x ∧ lsbValue x < max (lsbValue a) (lsbValue c))] := by
  simp only [routingStrictBetweenFlag, routingLTFlag_value, andFlag_decide, orFlag_decide]
  congr 2
  apply propext
  omega

/-- The binary membership test agrees with all four natural wire segments. -/
theorem routingOnWireFlag_value (ruler i j x y : List Bool) :
    routingOnWireFlag ruler i j x y = [decide (onWire (2 ^ ruler.length)
      (lsbValue i) (lsbValue j) (lsbValue x, lsbValue y))] := by
  simp only [routingOnWireFlag, routingEQFlag_value, routingLEFlag_value,
    routingBetweenFlag_value, routingColumnBits_value, routingSixBits_value,
    routingTargetRowBits_value, andFlag_decide, orFlag_decide]
  rfl

/-- The horizontal crossing test agrees with the strict natural interior. -/
theorem routingHorizontalInteriorFlag_value (ruler i j x y : List Bool) :
    routingHorizontalInteriorFlag ruler i j x y = [decide (horizontalInterior
      (2 ^ ruler.length) (lsbValue i) (lsbValue j)
      (lsbValue x, lsbValue y))] := by
  simp only [routingHorizontalInteriorFlag, routingLTFlag_value, routingEQFlag_value,
    routingColumnBits_value, routingSixBits_value, routingTargetRowBits_value,
    andFlag_decide, orFlag_decide]
  rfl

/-- The vertical crossing test agrees with the strict natural interior. -/
theorem routingVerticalInteriorFlag_value (ruler i j x y : List Bool) :
    routingVerticalInteriorFlag ruler i j x y = [decide (verticalInterior
      (2 ^ ruler.length) (lsbValue i) (lsbValue j)
      (lsbValue x, lsbValue y))] := by
  simp only [routingVerticalInteriorFlag, routingEQFlag_value, routingColumnBits_value,
    routingStrictBetweenFlag_value, routingSixBits_value, routingTargetRowBits_value,
    andFlag_decide]
  rfl

/-- Rounding retains a carry even at the largest input coordinate. -/
theorem routingCenterBits_value (bits : List Bool) :
    lsbValue (routingCenterBits bits) = 3 * ((lsbValue bits + 1) / 3) := by
  simp only [routingCenterBits, routingTripleBits_value, routingDivThreeBits_value,
    routingAddBits_value]
  rfl

/-- High-field extraction computes the raw owner without truncation. -/
theorem routingVerticalOwnerBits_value (ruler x : List Bool) :
    lsbValue (routingVerticalOwnerBits ruler x) =
      verticalOwner (2 ^ ruler.length) (lsbValue x, 0) := by
  simp only [routingVerticalOwnerBits, routing_lsbValue_drop, routingDivThreeBits_value,
    verticalOwner]

/-- Column allocation charges the shifted field and retained-carry arithmetic. -/
@[fun_prop] theorem routingColumnBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler i j : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits) :
    ComputableInPolyTime (fun z => routingColumnBits (ruler z) (i z) (j z)) enc encBits := by
  unfold routingColumnBits
  fun_prop

/-- Target-row construction charges its complete binary result. -/
@[fun_prop] theorem routingTargetRowBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {j : α → List Bool}
    (hj : ComputableInPolyTime j enc encBits) :
    ComputableInPolyTime (fun z => routingTargetRowBits (j z)) enc encBits := by
  unfold routingTargetRowBits
  fun_prop

/-- Closed interval tests compose the native unsigned comparisons. -/
@[fun_prop] theorem routingBetweenFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {a x c : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hc : ComputableInPolyTime c enc encBits) :
    ComputableInPolyTime (fun z => routingBetweenFlag (a z) (x z) (c z)) enc encBits := by
  unfold routingBetweenFlag
  fun_prop

/-- Strict interval tests compose the native unsigned comparisons. -/
@[fun_prop] theorem routingStrictBetweenFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {a x c : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hc : ComputableInPolyTime c enc encBits) :
    ComputableInPolyTime (fun z => routingStrictBetweenFlag (a z) (x z) (c z)) enc encBits := by
  unfold routingStrictBetweenFlag
  fun_prop

/-- The four route-segment checks use one native polynomial-time computation. -/
@[fun_prop] theorem routingOnWireFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler i j x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingOnWireFlag (ruler z) (i z) (j z) (x z) (y z)) enc encBits := by
  unfold routingOnWireFlag
  fun_prop

/-- The horizontal crossing test composes the native coordinate producers. -/
@[fun_prop] theorem routingHorizontalInteriorFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler i j x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingHorizontalInteriorFlag (ruler z) (i z) (j z) (x z) (y z)) enc encBits := by
  unfold routingHorizontalInteriorFlag
  fun_prop

/-- The vertical crossing test composes the native coordinate producers. -/
@[fun_prop] theorem routingVerticalInteriorFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler i j x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingVerticalInteriorFlag (ruler z) (i z) (j z) (x z) (y z)) enc encBits := by
  unfold routingVerticalInteriorFlag
  fun_prop

/-- Spacing-three rounding uses native binary addition, division and multiplication. -/
@[fun_prop] theorem routingCenterBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hbits : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => routingCenterBits (bits z)) enc encBits := by
  unfold routingCenterBits
  fun_prop

/-- Raw owner extraction charges binary division and unary field addressing. -/
@[fun_prop] theorem routingVerticalOwnerBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler x : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hx : ComputableInPolyTime x enc encBits) :
    ComputableInPolyTime (fun z => routingVerticalOwnerBits (ruler z) (x z)) enc encBits := by
  unfold routingVerticalOwnerBits
  fun_prop

end GameTheory.Complexity.Backend
