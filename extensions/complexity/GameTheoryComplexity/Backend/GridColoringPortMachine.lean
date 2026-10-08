import GameTheoryComplexity.Backend.GridColoringTileMachine
import GameTheoryComplexity.Backend.GridRoutingPointerMachine
import GameTheory.Math.GridWireColoringPorts

/-! Binary unit-step directions supply finite tile ports. Numeric comparisons
allow arbitrary padding, and the routing rectangle guard prevents truncation. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner GameTheory.Math.GridWire

/-- A fixed three-bit code represents an absent or cardinal tile port. -/
def encodeColoringPort (port : Option (Fin 4)) : List Bool :=
  Nat.toBitsLE 3 (match port with | none => 0 | some d => d.val + 1)

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
  caseBit₀ (andBit (routingEQFlag x u) (routingEQFlag yp v)) (encodeColoringPort (some 0))
    (caseBit₀ (andBit (routingEQFlag xp u) (routingEQFlag y v)) (encodeColoringPort (some 1))
      (caseBit₀ (andBit (routingEQFlag x u) (routingEQFlag vp y)) (encodeColoringPort (some 2))
        (caseBit₀ (andBit (routingEQFlag up x) (routingEQFlag y v))
          (encodeColoringPort (some 3)) (encodeColoringPort none))))

/-- Direction extraction agrees on all words with the natural-coordinate unit-step test. -/
theorem coloringDirectionBits_value (x y u v : List Bool) :
    coloringDirectionBits x y u v = encodeColoringPort
      (gridDirection (Nat.fromBitsLE x, Nat.fromBitsLE y)
        (Nat.fromBitsLE u, Nat.fromBitsLE v)) := by
  simp only [coloringDirectionBits, routingEQFlag_value, routingAddBits_value,
    show Nat.fromBitsLE [true] = 1 from rfl, gridDirection]
  split_ifs <;> simp_all [andBit, caseBit₀]

/-- Direction extraction composes four actual polynomial-time coordinate producers. -/
theorem coloringDirectionBitsFn_mem_FP {x y u v : List Bool → List Bool}
    (hx : x ∈ FP) (hy : y ∈ FP) (hu : u ∈ FP) (hv : v ∈ FP) :
    (fun z => coloringDirectionBits (x z) (y z) (u z) (v z)) ∈ FP := by
  have hx1 := routingAddBitsFn_mem_FP hx (constFn_mem_FP [true])
  have hy1 := routingAddBitsFn_mem_FP hy (constFn_mem_FP [true])
  have hu1 := routingAddBitsFn_mem_FP hu (constFn_mem_FP [true])
  have hv1 := routingAddBitsFn_mem_FP hv (constFn_mem_FP [true])
  have hand {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
      (fun z => andBit (a z) (b z)) ∈ FP :=
    CobhamFP_subset_FP (Cobham.andFn (FP_subset_CobhamFP ha) (FP_subset_CobhamFP hb))
  exact selectFn_mem_FP (hand (routingEQFlagFn_mem_FP hx hu)
    (routingEQFlagFn_mem_FP hy1 hv)) (constFn_mem_FP (encodeColoringPort (some 0)))
    (selectFn_mem_FP (hand (routingEQFlagFn_mem_FP hx1 hu)
      (routingEQFlagFn_mem_FP hy hv)) (constFn_mem_FP (encodeColoringPort (some 1)))
      (selectFn_mem_FP (hand (routingEQFlagFn_mem_FP hx hu)
        (routingEQFlagFn_mem_FP hv1 hy)) (constFn_mem_FP (encodeColoringPort (some 2)))
        (selectFn_mem_FP (hand (routingEQFlagFn_mem_FP hu1 hx)
          (routingEQFlagFn_mem_FP hy hv)) (constFn_mem_FP (encodeColoringPort (some 3)))
          (constFn_mem_FP (encodeColoringPort none)))))

/-- Normalize coincident incoming and outgoing steps before extracting a tile port. -/
def coloringNormalizedPortBits (x y px py sx sy : List Bool) (incoming : Bool) : List Bool :=
  caseBit₀ (andBit (routingEQFlag px sx) (routingEQFlag py sy)) (encodeColoringPort none)
    (if incoming then coloringDirectionBits x y px py else coloringDirectionBits x y sx sy)

/-- Two-cycle erasure is exactly a numeric equality test on the two neighboring points. -/
theorem coloringNormalizedPortBits_value (x y px py sx sy : List Bool) (incoming : Bool) :
    coloringNormalizedPortBits x y px py sx sy incoming = encodeColoringPort
      (gridDirection (Nat.fromBitsLE x, Nat.fromBitsLE y)
        (if (Nat.fromBitsLE px, Nat.fromBitsLE py) = (Nat.fromBitsLE sx, Nat.fromBitsLE sy)
          then (Nat.fromBitsLE x, Nat.fromBitsLE y)
          else if incoming then (Nat.fromBitsLE px, Nat.fromBitsLE py)
          else (Nat.fromBitsLE sx, Nat.fromBitsLE sy))) := by
  simp only [coloringNormalizedPortBits, routingEQFlag_value, coloringDirectionBits_value]
  by_cases hx : Nat.fromBitsLE px = Nat.fromBitsLE sx <;>
    by_cases hy : Nat.fromBitsLE py = Nat.fromBitsLE sy <;>
    cases incoming <;> simp [hx, hy, andBit, caseBit₀, gridDirection_self]

/-- Normalized port extraction composes actual polynomial-time coordinate producers. -/
theorem coloringNormalizedPortBitsFn_mem_FP (incoming : Bool)
    {x y px py sx sy : List Bool → List Bool}
    (hx : x ∈ FP) (hy : y ∈ FP) (hpX : px ∈ FP) (hpY : py ∈ FP)
    (hsX : sx ∈ FP) (hsY : sy ∈ FP) :
    (fun z => coloringNormalizedPortBits (x z) (y z) (px z) (py z) (sx z) (sy z)
      incoming) ∈ FP := by
  have he : (fun z => andBit (routingEQFlag (px z) (sx z))
      (routingEQFlag (py z) (sy z))) ∈ FP :=
    CobhamFP_subset_FP (Cobham.andFn
      (FP_subset_CobhamFP (routingEQFlagFn_mem_FP hpX hsX))
      (FP_subset_CobhamFP (routingEQFlagFn_mem_FP hpY hsY)))
  cases incoming
  · exact selectFn_mem_FP he (constFn_mem_FP (encodeColoringPort none))
      (coloringDirectionBitsFn_mem_FP hx hy hsX hsY)
  · exact selectFn_mem_FP he (constFn_mem_FP (encodeColoringPort none))
      (coloringDirectionBitsFn_mem_FP hx hy hpX hpY)

private def coloringPointBits (ruler x y : List Bool) : List Bool :=
  routingPadBits (routingCoordinateRuler ruler) x ++
    routingPadBits (routingCoordinateRuler ruler) y

private theorem coloringPointBits_eq_encode (ruler x y : List Bool) :
    coloringPointBits ruler x y =
      encodeRoutingPoint ruler.length (Nat.fromBitsLE x, Nat.fromBitsLE y) := by
  simp only [coloringPointBits, routingPadBits_eq_toBitsLE,
    routingCoordinateRuler_length, encodeRoutingPoint]

private def coloringPointerBits (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) : List Bool :=
  routingPointerMachine ruler P S incoming (coloringPointBits ruler x y)

/-- Routed tile ports preserve arbitrary binary coordinates with an outer rectangle guard. -/
def coloringRoutedPortBits (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) : List Bool :=
  let pred := coloringPointerBits ruler P S true x y
  let succ := coloringPointerBits ruler P S false x y
  caseBit₀ (routingRectangleFlag ruler x y)
    (coloringNormalizedPortBits x y (routingPointXBits ruler pred)
      (routingPointYBits ruler pred) (routingPointXBits ruler succ)
      (routingPointYBits ruler succ) incoming) (encodeColoringPort none)

private theorem coloringPointerBits_fields (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) (ha : routingRectangleFlag ruler x y = [true]) :
    (Nat.fromBitsLE (routingPointXBits ruler (coloringPointerBits ruler P S incoming x y)),
      Nat.fromBitsLE (routingPointYBits ruler (coloringPointerBits ruler P S incoming x y))) =
      (if incoming then gridRoutedPredecessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
      else gridRoutedSuccessor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
          (Nat.fromBitsLE x, Nat.fromBitsLE y) := by
  have hr := (routingRectangleFlag_accept ruler x y).mp ha
  have hc := routingCoordinateCapacity ruler.length
  have hb : Nat.fromBitsLE x < 2 ^ routingCoordinateWidth ruler.length ∧
      Nat.fromBitsLE y < 2 ^ routingCoordinateWidth ruler.length := by
    constructor <;> omega
  have hout := routingPointer_bounded (b := ruler.length)
    (p := (Nat.fromBitsLE x, Nat.fromBitsLE y)) hb
    (P := routingOriginalPointer ruler P) (S := routingOriginalPointer ruler S)
  rw [coloringPointerBits, routingPointerMachine_eq_words, coloringPointBits_eq_encode,
    wordRoutingPointer_encode hb incoming]
  rw [routingPointXBits_encode, routingPointYBits_encode]
  cases incoming
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.fromBitsLE_toBitsLE hout.2.2.1, Nat.fromBitsLE_toBitsLE hout.2.2.2]
  · simp only [↓reduceIte]
    rw [Nat.fromBitsLE_toBitsLE hout.1, Nat.fromBitsLE_toBitsLE hout.2.1]

/-- All-word port extraction agrees with the globally routed, two-cycle-normalized graph. -/
theorem coloringRoutedPortBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (incoming : Bool) (x y : List Bool) :
    coloringRoutedPortBits ruler P S incoming x y = encodeColoringPort
      ((if incoming then gridIncomingPort else gridOutgoingPort)
        (gridRoutedPredecessor (2 ^ ruler.length)
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
        (gridRoutedSuccessor (2 ^ ruler.length)
          (routingOriginalPointer ruler P) (routingOriginalPointer ruler S))
        (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  by_cases ha : routingRectangleFlag ruler x y = [true]
  · rw [coloringRoutedPortBits, ha]
    simp only [caseBit₀, Bool.cond_true]
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
      cases h : decide (Nat.fromBitsLE x < 3 * 2 ^ ruler.length * 2 ^ ruler.length ∧
        Nat.fromBitsLE y < 6 * 2 ^ ruler.length) <;> simp_all
    rw [coloringRoutedPortBits, hf]
    simp only [caseBit₀, Bool.cond_false]
    cases incoming <;>
      simp [gridIncomingPort, gridOutgoingPort,
        GameTheory.Math.EndOfLine.eraseTwoCyclePredecessor,
        GameTheory.Math.EndOfLine.eraseTwoCycleSuccessor, hb.1, hb.2]

private theorem coloringPointerBitsUniformFn_mem_FP (incoming : Bool)
    (P S : List Bool → List Bool → List Bool) {ruler seed x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => coloringPointerBits (ruler z) (P (seed z)) (S (seed z))
      incoming (x z) (y z)) ∈ FP := by
  have hw : (fun z => coloringPointBits (ruler z) (x z) (y z)) ∈ FP :=
    appendFn_mem_FP
      (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr) hx)
      (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr) hy)
  exact routingPointerMachineUniformFn_mem_FP incoming P S hr hs hw hP hS

/-- Routed port extraction has an actual uniform certificate with varying pointer-query seeds. -/
theorem coloringRoutedPortBitsUniformFn_mem_FP (incoming : Bool)
    (P S : List Bool → List Bool → List Bool) {ruler seed x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => coloringRoutedPortBits (ruler z) (P (seed z)) (S (seed z))
      incoming (x z) (y z)) ∈ FP := by
  let pred : List Bool → List Bool := fun z =>
    coloringPointerBits (ruler z) (P (seed z)) (S (seed z)) true (x z) (y z)
  let succ : List Bool → List Bool := fun z =>
    coloringPointerBits (ruler z) (P (seed z)) (S (seed z)) false (x z) (y z)
  have hp : pred ∈ FP := coloringPointerBitsUniformFn_mem_FP true P S hr hs hx hy hP hS
  have hsucc : succ ∈ FP := coloringPointerBitsUniformFn_mem_FP false P S hr hs hx hy hP hS
  have hn := coloringNormalizedPortBitsFn_mem_FP incoming hx hy
    (routingPointXBitsFn_mem_FP hr hp) (routingPointYBitsFn_mem_FP hr hp)
    (routingPointXBitsFn_mem_FP hr hsucc) (routingPointYBitsFn_mem_FP hr hsucc)
  exact selectFn_mem_FP (routingRectangleFlagFn_mem_FP hr hx hy) hn
    (constFn_mem_FP (encodeColoringPort none))

end GameTheory.Complexity.Backend
