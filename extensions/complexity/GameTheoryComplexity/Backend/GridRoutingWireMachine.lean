module

public import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
public import GameTheoryComplexity.Backend.GridRoutingCodecMachine
public import GameTheoryComplexity.Backend.SpernerBinarySteps

@[expose] public section

/-! A binary machine follows either direction of a single routed wire.
Comparisons use exact unsigned values; output coordinate fields are canonical
at the routing width. Arithmetic recursion counts input bits. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- Decrement an unsigned binary word, saturating at zero. -/
def routingSaturatingPredBits (bits : List Bool) : List Bool :=
  select (routingLTFlag [] bits) (gridPredBits bits) bits

/-- Saturating decrement agrees with natural subtraction on every word. -/
theorem routingSaturatingPredBits_value (bits : List Bool) :
    lsbValue (routingSaturatingPredBits bits) = lsbValue bits - 1 := by
  unfold routingSaturatingPredBits
  rw [routingLTFlag_value]
  change lsbValue (select [decide (0 < lsbValue bits)]
    (gridPredBits bits) bits) = _
  by_cases h : 0 < lsbValue bits
  · simpa [h, select] using gridPredBits_value_of_pos bits h
  · have hz : lsbValue bits = 0 := by omega
    simp [hz, select]

/-- Saturating decrement charges its zero guard and native binary predecessor. -/
@[fun_prop] theorem routingSaturatingPredBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => routingSaturatingPredBits (bits z)) enc encBits := by
  unfold routingSaturatingPredBits
  fun_prop

private theorem coordinateFields_eq_encode (ruler x y : List Bool) :
    routingPadBits (routingCoordinateRuler ruler) x ++
      routingPadBits (routingCoordinateRuler ruler) y =
      encodeRoutingPoint ruler.length (lsbValue x, lsbValue y) := by
  simp only [routingPadBits_eq_lowBits,
    routingCoordinateRuler_length, encodeRoutingPoint]

/-- Follow an individual wire, with `true` selecting its predecessor. -/
def routingWireStepBits (ruler i j x y : List Bool) (incoming : Bool) : List Bool :=
  let col := routingColumnBits ruler i j
  let source := routingSixBits i
  let target := routingSixBits j
  let upper := routingTargetRowBits j
  let xp := routingAddBits x [true]
  let xm := routingSaturatingPredBits x
  let yp := routingAddBits y [true]
  let ym := routingSaturatingPredBits y
  let pack := fun x y : List Bool =>
    routingPadBits (routingCoordinateRuler ruler) x ++
      routingPadBits (routingCoordinateRuler ruler) y
  if incoming then
    select (andFlag (routingEQFlag y source)
      (andFlag (routingLTFlag [] x) (routingLEFlag x col))) (pack xm y)
    (select (andFlag (routingEQFlag x col)
      (andFlag (routingBetweenFlag source y upper) (notFlag (routingEQFlag y source))))
      (pack x (select (routingLTFlag source upper) ym yp))
    (select (andFlag (routingEQFlag y upper) (routingLTFlag x col)) (pack xp y)
    (select (andFlag (routingEQFlag x [])
      (andFlag (routingLEFlag target y) (routingLTFlag y upper))) (pack x yp) (pack x y))))
  else
    select (andFlag (routingEQFlag y source) (routingLTFlag x col)) (pack xp y)
    (select (andFlag (routingEQFlag x col)
      (andFlag (routingBetweenFlag source y upper) (notFlag (routingEQFlag y upper))))
      (pack x (select (routingLTFlag source upper) yp ym))
    (select (andFlag (routingEQFlag y upper)
      (andFlag (routingLTFlag [] x) (routingLEFlag x col))) (pack xm y)
    (select (andFlag (routingEQFlag x [])
      (andFlag (routingLTFlag target y) (routingLEFlag y upper))) (pack x ym) (pack x y))))

private theorem bitsNil : lsbValue [] = 0 := rfl

private theorem bitsOne : lsbValue [true] = 1 := rfl

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

private theorem flagNot_decide (a : Prop) [Decidable a] :
    notFlag [decide a] = [decide (¬a)] := by
  by_cases h : a <;> simp [h, notFlag]

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    select [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, select]

/-- The binary step agrees with the natural wire pointer on arbitrary input words. -/
theorem routingWireStepBits_eq_encode (ruler i j x y : List Bool) (incoming : Bool) :
    routingWireStepBits ruler i j x y incoming = encodeRoutingPoint ruler.length
      (if incoming then wirePredecessor (2 ^ ruler.length) (lsbValue i)
        (lsbValue j) (lsbValue x, lsbValue y)
      else wireSuccessor (2 ^ ruler.length) (lsbValue i)
        (lsbValue j) (lsbValue x, lsbValue y)) := by
  cases incoming <;>
    simp only [routingWireStepBits, Bool.false_eq_true, ↓reduceIte,
      routingEQFlag_value, routingLTFlag_value, routingLEFlag_value,
      routingBetweenFlag_value, routingColumnBits_value, routingSixBits_value,
      routingTargetRowBits_value, flagNot_decide, flagAnd_decide, select_decide,
      wirePredecessor, wireSuccessor]
  all_goals simp only [bitsNil, and_assoc]
  all_goals split_ifs <;>
    simp_all only [coordinateFields_eq_encode, routingAddBits_value,
      routingSaturatingPredBits_value, bitsOne] <;> simp_all
  all_goals split_ifs <;> rfl

/-- Each wire step emits two complete canonical routing coordinate fields. -/
@[simp] theorem routingWireStepBits_length (ruler i j x y : List Bool) (incoming : Bool) :
    (routingWireStepBits ruler i j x y incoming).length = routingPointWidth ruler.length := by
  rw [routingWireStepBits_eq_encode, encodeRoutingPoint_length]
/-- Individual wire steps charge all native coordinate producers and output fields. -/
@[fun_prop] theorem routingWireStepBits_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler i j x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => routingWireStepBits (ruler z) (i z) (j z)
      (x z) (y z) incoming) enc encBits := by
  unfold routingWireStepBits
  cases incoming <;> dsimp only <;> fun_prop

end GameTheory.Complexity.Backend
