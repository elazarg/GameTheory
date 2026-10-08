import GameTheoryComplexity.Backend.GridRoutingArithmetic
import GameTheoryComplexity.Backend.GridRoutingBitFields
import GameTheoryComplexity.Backend.GridRoutingDivision
import GameTheory.Math.GridWire
import GameTheory.Math.GridCrossingLocator

/-! Binary route geometry uses exact arithmetic with retained carries.
Comparisons inspect numeric values, so unequal widths and high zero padding
do not change membership in a wire segment or crossing interior. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

/-- Allocate the column `3 * (2^b * i + j)` without numeric iteration. -/
def routingColumnBits (ruler i j : List Bool) : List Bool :=
  routingTripleBits (routingAddBits (routingShiftBits ruler i) j)

/-- The incoming horizontal row lies three units above the target vertex. -/
def routingTargetRowBits (j : List Bool) : List Bool :=
  routingAddBits (routingSixBits j) [true, true]

/-- Closed interval membership, allowing either ordering of the endpoints. -/
def routingBetweenFlag (a x c : List Bool) : List Bool :=
  orBit (andBit (routingLEFlag a x) (routingLEFlag x c))
    (andBit (routingLEFlag c x) (routingLEFlag x a))

/-- Strict interval membership, allowing either ordering of the endpoints. -/
def routingStrictBetweenFlag (a x c : List Bool) : List Bool :=
  orBit (andBit (routingLTFlag a x) (routingLTFlag x c))
    (andBit (routingLTFlag c x) (routingLTFlag x a))

/-- Check all four closed segments of a source-indexed route. -/
def routingOnWireFlag (ruler i j x y : List Bool) : List Bool :=
  let col := routingColumnBits ruler i j
  let source := routingSixBits i
  let target := routingSixBits j
  let upper := routingTargetRowBits j
  orBit (andBit (routingEQFlag y source) (routingLEFlag x col))
    (orBit (andBit (routingEQFlag x col) (routingBetweenFlag source y upper))
      (orBit (andBit (routingEQFlag y upper) (routingLEFlag x col))
        (andBit (routingEQFlag x [])
          (andBit (routingLEFlag target y) (routingLEFlag y upper)))))

/-- Check the strict horizontal interior used to validate a proper crossing. -/
def routingHorizontalInteriorFlag (ruler i j x y : List Bool) : List Bool :=
  andBit (routingLTFlag [] x) (andBit (routingLTFlag x (routingColumnBits ruler i j))
    (orBit (routingEQFlag y (routingSixBits i))
      (routingEQFlag y (routingTargetRowBits j))))

/-- Check the strict vertical interior used to validate a proper crossing. -/
def routingVerticalInteriorFlag (ruler i j x y : List Bool) : List Bool :=
  andBit (routingEQFlag x (routingColumnBits ruler i j))
    (routingStrictBetweenFlag (routingSixBits i) y (routingTargetRowBits j))

/-- Round one coordinate to its nearest spacing-three crossing center. -/
def routingCenterBits (bits : List Bool) : List Bool :=
  routingTripleBits (routingDivThreeBits (routingAddBits bits [true]))

/-- Recover the raw source field of a routing column, retaining overflow bits. -/
def routingVerticalOwnerBits (ruler x : List Bool) : List Bool :=
  (routingDivThreeBits x).drop ruler.length

private theorem andBit_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

private theorem orBit_decide (a b : Prop) [Decidable a] [Decidable b] :
    orBit [decide a] [decide b] = [decide (a ∨ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, orBit, caseBit₀]

/-- Column allocation agrees exactly with the natural coordinate formula. -/
theorem routingColumnBits_value (ruler i j : List Bool) :
    Nat.fromBitsLE (routingColumnBits ruler i j) =
      wireColumn (2 ^ ruler.length) (Nat.fromBitsLE i) (Nat.fromBitsLE j) := by
  simp only [routingColumnBits, routingTripleBits_value, routingAddBits_value,
    routingShiftBits_value, wireColumn]

/-- Target row construction keeps the final carry. -/
theorem routingTargetRowBits_value (j : List Bool) :
    Nat.fromBitsLE (routingTargetRowBits j) = 6 * Nat.fromBitsLE j + 3 := by
  simp only [routingTargetRowBits, routingAddBits_value, routingSixBits_value]
  rfl

/-- The closed interval flag is exact even for differently padded words. -/
theorem routingBetweenFlag_value (a x c : List Bool) :
    routingBetweenFlag a x c = [decide (min (Nat.fromBitsLE a) (Nat.fromBitsLE c) ≤
      Nat.fromBitsLE x ∧ Nat.fromBitsLE x ≤ max (Nat.fromBitsLE a) (Nat.fromBitsLE c))] := by
  simp only [routingBetweenFlag, routingLEFlag_value, andBit_decide, orBit_decide]
  congr 2
  apply propext
  omega

/-- The strict interval flag excludes both endpoints, including equal endpoints. -/
theorem routingStrictBetweenFlag_value (a x c : List Bool) :
    routingStrictBetweenFlag a x c = [decide (min (Nat.fromBitsLE a) (Nat.fromBitsLE c) <
      Nat.fromBitsLE x ∧ Nat.fromBitsLE x < max (Nat.fromBitsLE a) (Nat.fromBitsLE c))] := by
  simp only [routingStrictBetweenFlag, routingLTFlag_value, andBit_decide, orBit_decide]
  congr 2
  apply propext
  omega

/-- The binary membership test agrees with all four natural wire segments. -/
theorem routingOnWireFlag_value (ruler i j x y : List Bool) :
    routingOnWireFlag ruler i j x y = [decide (onWire (2 ^ ruler.length)
      (Nat.fromBitsLE i) (Nat.fromBitsLE j) (Nat.fromBitsLE x, Nat.fromBitsLE y))] := by
  simp only [routingOnWireFlag, routingEQFlag_value, routingLEFlag_value,
    routingBetweenFlag_value, routingColumnBits_value, routingSixBits_value,
    routingTargetRowBits_value, andBit_decide, orBit_decide]
  rfl

/-- The horizontal crossing test agrees with the strict natural interior. -/
theorem routingHorizontalInteriorFlag_value (ruler i j x y : List Bool) :
    routingHorizontalInteriorFlag ruler i j x y = [decide (horizontalInterior
      (2 ^ ruler.length) (Nat.fromBitsLE i) (Nat.fromBitsLE j)
      (Nat.fromBitsLE x, Nat.fromBitsLE y))] := by
  simp only [routingHorizontalInteriorFlag, routingLTFlag_value, routingEQFlag_value,
    routingColumnBits_value, routingSixBits_value, routingTargetRowBits_value,
    andBit_decide, orBit_decide]
  rfl

/-- The vertical crossing test agrees with the strict natural interior. -/
theorem routingVerticalInteriorFlag_value (ruler i j x y : List Bool) :
    routingVerticalInteriorFlag ruler i j x y = [decide (verticalInterior
      (2 ^ ruler.length) (Nat.fromBitsLE i) (Nat.fromBitsLE j)
      (Nat.fromBitsLE x, Nat.fromBitsLE y))] := by
  simp only [routingVerticalInteriorFlag, routingEQFlag_value, routingColumnBits_value,
    routingStrictBetweenFlag_value, routingSixBits_value, routingTargetRowBits_value,
    andBit_decide]
  rfl

/-- Rounding retains a carry even at the largest input coordinate. -/
theorem routingCenterBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingCenterBits bits) = 3 * ((Nat.fromBitsLE bits + 1) / 3) := by
  simp only [routingCenterBits, routingTripleBits_value, routingDivThreeBits_value,
    routingAddBits_value]
  rfl

/-- High-field extraction computes the raw owner without truncation. -/
theorem routingVerticalOwnerBits_value (ruler x : List Bool) :
    Nat.fromBitsLE (routingVerticalOwnerBits ruler x) =
      verticalOwner (2 ^ ruler.length) (Nat.fromBitsLE x, 0) := by
  simp only [routingVerticalOwnerBits, routing_fromBitsLE_drop, routingDivThreeBits_value,
    verticalOwner]

/-- Column allocation composes polynomial-time producers uniformly. -/
theorem routingColumnBitsFn_mem_FP {ruler i j : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) :
    (fun z => routingColumnBits (ruler z) (i z) (j z)) ∈ FP :=
  routingTripleBitsFn_mem_FP
    (routingAddBitsFn_mem_FP (routingShiftBitsFn_mem_FP hr hi) hj)

/-- Target-row allocation has an actual uniform polynomial-time certificate. -/
theorem routingTargetRowBitsFn_mem_FP {j : List Bool → List Bool} (hj : j ∈ FP) :
    (fun z => routingTargetRowBits (j z)) ∈ FP :=
  routingAddBitsFn_mem_FP (routingSixBitsFn_mem_FP hj) (constFn_mem_FP _)

/-- Closed interval tests compose polynomial-time producers uniformly. -/
theorem routingBetweenFlagFn_mem_FP {a x c : List Bool → List Bool}
    (ha : a ∈ FP) (hx : x ∈ FP) (hc : c ∈ FP) :
    (fun z => routingBetweenFlag (a z) (x z) (c z)) ∈ FP :=
  orBitFn_mem_FP
    (andBitFn_mem_FP (routingLEFlagFn_mem_FP ha hx) (routingLEFlagFn_mem_FP hx hc))
    (andBitFn_mem_FP (routingLEFlagFn_mem_FP hc hx) (routingLEFlagFn_mem_FP hx ha))

/-- Strict interval tests compose polynomial-time producers uniformly. -/
theorem routingStrictBetweenFlagFn_mem_FP {a x c : List Bool → List Bool}
    (ha : a ∈ FP) (hx : x ∈ FP) (hc : c ∈ FP) :
    (fun z => routingStrictBetweenFlag (a z) (x z) (c z)) ∈ FP :=
  orBitFn_mem_FP
    (andBitFn_mem_FP (routingLTFlagFn_mem_FP ha hx) (routingLTFlagFn_mem_FP hx hc))
    (andBitFn_mem_FP (routingLTFlagFn_mem_FP hc hx) (routingLTFlagFn_mem_FP hx ha))

/-- All four route-segment checks have one composed uniform FP certificate. -/
theorem routingOnWireFlagFn_mem_FP {ruler i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingOnWireFlag (ruler z) (i z) (j z) (x z) (y z)) ∈ FP := by
  have hcol := routingColumnBitsFn_mem_FP hr hi hj
  have hsource := routingSixBitsFn_mem_FP hi
  have htarget := routingSixBitsFn_mem_FP hj
  have hupper := routingTargetRowBitsFn_mem_FP hj
  exact orBitFn_mem_FP
    (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hsource) (routingLEFlagFn_mem_FP hx hcol))
    (orBitFn_mem_FP
      (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx hcol)
        (routingBetweenFlagFn_mem_FP hsource hy hupper))
      (orBitFn_mem_FP
        (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hupper) (routingLEFlagFn_mem_FP hx hcol))
        (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx (constFn_mem_FP []))
          (andBitFn_mem_FP (routingLEFlagFn_mem_FP htarget hy)
            (routingLEFlagFn_mem_FP hy hupper)))))

/-- Horizontal proper-crossing tests have a uniform FP certificate. -/
theorem routingHorizontalInteriorFlagFn_mem_FP {ruler i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingHorizontalInteriorFlag (ruler z) (i z) (j z) (x z) (y z)) ∈ FP :=
  andBitFn_mem_FP (routingLTFlagFn_mem_FP (constFn_mem_FP []) hx)
    (andBitFn_mem_FP (routingLTFlagFn_mem_FP hx (routingColumnBitsFn_mem_FP hr hi hj))
      (orBitFn_mem_FP (routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP hi))
        (routingEQFlagFn_mem_FP hy (routingTargetRowBitsFn_mem_FP hj))))

/-- Vertical proper-crossing tests have a uniform FP certificate. -/
theorem routingVerticalInteriorFlagFn_mem_FP {ruler i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingVerticalInteriorFlag (ruler z) (i z) (j z) (x z) (y z)) ∈ FP :=
  andBitFn_mem_FP (routingEQFlagFn_mem_FP hx (routingColumnBitsFn_mem_FP hr hi hj))
    (routingStrictBetweenFlagFn_mem_FP (routingSixBitsFn_mem_FP hi) hy
      (routingTargetRowBitsFn_mem_FP hj))

/-- Spacing-three rounding uses exact binary addition, division and multiplication. -/
theorem routingCenterBitsFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => routingCenterBits (bits z)) ∈ FP := by
  have hadd := routingAddBitsFn_mem_FP hb (constFn_mem_FP [true])
  have hdiv := mem_FP_comp (f := fun z => routingAddBits (bits z) [true])
    (g := routingDivThreeBits) hadd routingDivThreeBits_mem_FP
  exact routingTripleBitsFn_mem_FP hdiv

/-- Raw owner extraction is polynomial-time before any range guard or narrowing. -/
theorem routingVerticalOwnerBitsFn_mem_FP {ruler x : List Bool → List Bool}
    (hr : ruler ∈ FP) (hx : x ∈ FP) :
    (fun z => routingVerticalOwnerBits (ruler z) (x z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact dropFn (FP_subset_CobhamFP hr)
    (FP_subset_CobhamFP (mem_FP_comp hx routingDivThreeBits_mem_FP))

end GameTheory.Complexity.Backend
