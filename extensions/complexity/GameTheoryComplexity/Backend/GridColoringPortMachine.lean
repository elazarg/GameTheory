module

public import GameTheoryComplexity.Backend.GridColoringTileMachine
public import GameTheoryComplexity.Backend.GridRoutingPointerMachine
public import GameTheory.Math.GridWireColoringPorts

@[expose] public section

/-! Binary unit-step directions supply finite tile ports. Numeric comparisons
allow arbitrary padding, and the routing rectangle guard prevents truncation. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Sperner GameTheory.Math.GridWire

/-- A fixed three-bit code represents an absent or cardinal tile port. -/
def encodeColoringPort (port : Option (Fin 4)) : List Bool :=
  lowBits 3 (match port with | none => 0 | some d => d.val + 1)

@[simp] theorem decodeColoringPort_encode (port : Option (Fin 4)) :
    decodeColoringPort (encodeColoringPort port) = port := by
  cases port with
  | none => rfl
  | some d => fin_cases d <;> rfl

/-- Compute a unit-step direction from four arbitrary binary coordinate words. -/
def coloringDirectionBits (x y u v : List Bool) : List Bool :=
  let xp := routingAddBits x [true]
  let yp := routingAddBits y [true]
  let up := routingAddBits u [true]
  let vp := routingAddBits v [true]
  select (andFlag (routingEQFlag x u) (routingEQFlag yp v)) (encodeColoringPort (some 0))
    (select (andFlag (routingEQFlag xp u) (routingEQFlag y v)) (encodeColoringPort (some 1))
      (select (andFlag (routingEQFlag x u) (routingEQFlag vp y)) (encodeColoringPort (some 2))
        (select (andFlag (routingEQFlag up x) (routingEQFlag y v))
          (encodeColoringPort (some 3)) (encodeColoringPort none))))

/-- Direction extraction agrees on all words with the natural-coordinate unit-step test. -/
theorem coloringDirectionBits_value (x y u v : List Bool) :
    coloringDirectionBits x y u v = encodeColoringPort
      (gridDirection (lsbValue x, lsbValue y)
        (lsbValue u, lsbValue v)) := by
  simp only [coloringDirectionBits, routingEQFlag_value, routingAddBits_value,
    show lsbValue [true] = 1 from rfl, gridDirection]
  split_ifs <;> simp_all [andFlag, select]
  all_goals split_ifs <;> simp_all

/-- Direction extraction charges four native coordinate producers and fixed selectors. -/
@[fun_prop] theorem coloringDirectionBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {x y u v : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits)
    (hu : ComputableInPolyTime u enc encBits) (hv : ComputableInPolyTime v enc encBits) :
    ComputableInPolyTime (fun z => coloringDirectionBits (x z) (y z) (u z) (v z)) enc encBits := by
  unfold coloringDirectionBits
  fun_prop

/-- Normalize coincident incoming and outgoing steps before extracting a tile port. -/
def coloringNormalizedPortBits (x y px py sx sy : List Bool) (incoming : Bool) : List Bool :=
  select (andFlag (routingEQFlag px sx) (routingEQFlag py sy)) (encodeColoringPort none)
    (if incoming then coloringDirectionBits x y px py else coloringDirectionBits x y sx sy)

/-- Two-cycle erasure is exactly a numeric equality test on the two neighboring points. -/
theorem coloringNormalizedPortBits_value (x y px py sx sy : List Bool) (incoming : Bool) :
    coloringNormalizedPortBits x y px py sx sy incoming = encodeColoringPort
      (gridDirection (lsbValue x, lsbValue y)
        (if (lsbValue px, lsbValue py) = (lsbValue sx, lsbValue sy)
          then (lsbValue x, lsbValue y)
          else if incoming then (lsbValue px, lsbValue py)
          else (lsbValue sx, lsbValue sy))) := by
  simp only [coloringNormalizedPortBits, routingEQFlag_value, coloringDirectionBits_value]
  by_cases hx : lsbValue px = lsbValue sx <;>
    by_cases hy : lsbValue py = lsbValue sy <;>
    cases incoming <;> simp [hx, hy, andFlag, select, gridDirection_self]

/-- Normalized ports charge both raw neighboring points and the selected direction. -/
@[fun_prop] theorem coloringNormalizedPortBits_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {x y px py sx sy : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits)
    (hpX : ComputableInPolyTime px enc encBits) (hpY : ComputableInPolyTime py enc encBits)
    (hsX : ComputableInPolyTime sx enc encBits) (hsY : ComputableInPolyTime sy enc encBits) :
    ComputableInPolyTime (fun z => coloringNormalizedPortBits (x z) (y z) (px z) (py z)
      (sx z) (sy z) incoming) enc encBits := by
  have hguard := andFlag_polyTime.comp
    ((routingEQFlag_polyTime hpX hsX).prod (routingEQFlag_polyTime hpY hsY))
  cases incoming
  · exact select_polyTime.comp (hguard.prod ((const (encodeColoringPort none)).prod
      (coloringDirectionBits_polyTime hx hy hsX hsY)))
  · exact select_polyTime.comp (hguard.prod ((const (encodeColoringPort none)).prod
      (coloringDirectionBits_polyTime hx hy hpX hpY)))

/-- Canonical routing fields retain the low bits of both raw coordinates. -/
def coloringPointBits (ruler x y : List Bool) : List Bool :=
  routingPadBits (routingCoordinateRuler ruler) x ++
    routingPadBits (routingCoordinateRuler ruler) y

private theorem coloringPointBits_eq_encode (ruler x y : List Bool) :
    coloringPointBits ruler x y =
      encodeRoutingPoint ruler.length (lsbValue x, lsbValue y) := by
  simp only [coloringPointBits, routingPadBits_eq_lowBits,
    routingCoordinateRuler_length, encodeRoutingPoint]

/-- Follow a routed pointer after canonical fixed-width coordinate packing. -/
def coloringPointerBits (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) : List Bool :=
  routingPointerMachine ruler P S incoming (coloringPointBits ruler x y)

/-- Routed tile ports preserve arbitrary binary coordinates with an outer rectangle guard. -/
def coloringRoutedPortBits (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) : List Bool :=
  let pred := coloringPointerBits ruler P S true x y
  let succ := coloringPointerBits ruler P S false x y
  select (routingRectangleFlag ruler x y)
    (coloringNormalizedPortBits x y (routingPointXBits ruler pred)
      (routingPointYBits ruler pred) (routingPointXBits ruler succ)
      (routingPointYBits ruler succ) incoming) (encodeColoringPort none)

private theorem coloringPointerBits_fields (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) (ha : routingRectangleFlag ruler x y = [true]) :
    (lsbValue (routingPointXBits ruler (coloringPointerBits ruler P S incoming x y)),
      lsbValue (routingPointYBits ruler (coloringPointerBits ruler P S incoming x y))) =
      (if incoming then gridRoutedPredecessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
      else gridRoutedSuccessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
          (lsbValue x, lsbValue y) := by
  have hr := (routingRectangleFlag_accept ruler x y).mp ha
  have hc := routingCoordinateCapacity ruler.length
  have hb : lsbValue x < 2 ^ routingCoordinateWidth ruler.length ∧
      lsbValue y < 2 ^ routingCoordinateWidth ruler.length := by
    constructor <;> omega
  have hout := routingPointer_bounded (b := ruler.length)
    (p := (lsbValue x, lsbValue y)) hb
    (P := routingOriginalPointer ruler P) (S := routingOriginalPointer ruler S)
  rw [coloringPointerBits, routingPointerMachine_eq_words, coloringPointBits_eq_encode,
    wordRoutingPointer_encode hb incoming]
  rw [routingPointXBits_encode, routingPointYBits_encode]
  cases incoming
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lsbValue_lowBits hout.2.2.1, lsbValue_lowBits hout.2.2.2]
  · simp only [↓reduceIte]
    rw [lsbValue_lowBits hout.1, lsbValue_lowBits hout.2.1]

/-- All-word port extraction agrees with the globally routed, two-cycle-normalized graph. -/
theorem coloringRoutedPortBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) :
    coloringRoutedPortBits ruler P S incoming x y = encodeColoringPort
      ((if incoming then gridIncomingPort else gridOutgoingPort)
        (gridRoutedPredecessor (2 ^ ruler.length)
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
        (gridRoutedSuccessor (2 ^ ruler.length)
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
        (lsbValue x, lsbValue y)) := by
  by_cases ha : routingRectangleFlag ruler x y = [true]
  · rw [coloringRoutedPortBits, ha]
    simp only [select_cons, ↓reduceIte]
    rw [coloringNormalizedPortBits_value, coloringPointerBits_fields ruler P S true x y ha,
      coloringPointerBits_fields ruler P S false x y ha]
    cases incoming <;>
      simp only [Bool.false_eq_true, ↓reduceIte, gridIncomingPort, gridOutgoingPort,
        GameTheory.Math.EndOfLine.eraseTwoCyclePredecessor,
        GameTheory.Math.EndOfLine.eraseTwoCycleSuccessor]
  · have hb := routingRectangleFlag_background ruler x y
      (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) ha
    have hf : routingRectangleFlag ruler x y = [false] := by
      rw [routingRectangleFlag_value] at ha ⊢
      cases h : decide (lsbValue x < 3 * 2 ^ ruler.length * 2 ^ ruler.length ∧
        lsbValue y < 6 * 2 ^ ruler.length) <;> simp_all
    rw [coloringRoutedPortBits, hf]
    simp only [select_cons, Bool.false_eq_true, ↓reduceIte]
    cases incoming <;>
      simp [gridIncomingPort, gridOutgoingPort,
        GameTheory.Math.EndOfLine.eraseTwoCyclePredecessor,
        GameTheory.Math.EndOfLine.eraseTwoCycleSuccessor, hb.1, hb.2]

@[fun_prop] theorem coloringPointBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => coloringPointBits (ruler z) (x z) (y z)) enc encBits :=
  bitsAppend (routingPadBits_polyTime (routingCoordinateRuler_polyTime hr) hx)
    (routingPadBits_polyTime (routingCoordinateRuler_polyTime hr) hy)

/-- Routed coordinate queries charge native pointer execution and complete field packing. -/
@[fun_prop] theorem coloringPointerBitsUniform_polyTime (incoming : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => coloringPointerBits (ruler z) (P (seed z)) (S (seed z)) incoming (x z) (y z)) enc encBits := by
  exact routingPointerMachineUniform_polyTime incoming P S hruler hseed
    (coloringPointBits_polyTime hruler hx hy) hP hS

/-- Routed port extraction charges seeded pointer queries and exact rectangle guards. -/
@[fun_prop] theorem coloringRoutedPortBitsUniform_polyTime (incoming : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => coloringRoutedPortBits (ruler z) (P (seed z)) (S (seed z)) incoming (x z) (y z)) enc encBits := by
  have hp := coloringPointerBitsUniform_polyTime true P S hruler hseed hx hy hP hS
  have hsucc := coloringPointerBitsUniform_polyTime false P S hruler hseed hx hy hP hS
  have hn := coloringNormalizedPortBits_polyTime incoming hx hy
    (routingPointXBits_polyTime hruler hp) (routingPointYBits_polyTime hruler hp)
    (routingPointXBits_polyTime hruler hsucc) (routingPointYBits_polyTime hruler hsucc)
  exact select_polyTime.comp ((routingRectangleFlag_polyTime hruler hx hy).prod
    (hn.prod (const (encodeColoringPort none))))

end GameTheory.Complexity.Backend
