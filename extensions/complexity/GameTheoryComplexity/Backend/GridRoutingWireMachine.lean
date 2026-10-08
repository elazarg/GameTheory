import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
import GameTheoryComplexity.Backend.GridRoutingCodecMachine
import GameTheoryComplexity.Backend.SpernerBinarySteps

/-! A binary machine follows either direction of a single routed wire.
Comparisons use exact unsigned values; output coordinate fields are canonical
at the routing width. Arithmetic recursion counts input bits. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire

/-- Decrement an unsigned binary word, saturating at zero. -/
def routingSaturatingPredBits (bits : List Bool) : List Bool :=
  caseBit₀ (routingLTFlag [] bits) (gridPredBits bits) bits

/-- Saturating decrement agrees with natural subtraction on every word. -/
theorem routingSaturatingPredBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingSaturatingPredBits bits) = Nat.fromBitsLE bits - 1 := by
  unfold routingSaturatingPredBits
  rw [routingLTFlag_value]
  change Nat.fromBitsLE (caseBit₀ [decide (0 < Nat.fromBitsLE bits)]
    (gridPredBits bits) bits) = _
  by_cases h : 0 < Nat.fromBitsLE bits
  · simpa [h, caseBit₀] using gridPredBits_value_of_pos bits h
  · have hz : Nat.fromBitsLE bits = 0 := by omega
    simp [hz, caseBit₀]

/-- The zero guard composes an actual binary decrement machine. -/
theorem routingSaturatingPredBitsFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => routingSaturatingPredBits (bits z)) ∈ FP :=
  selectFn_mem_FP (routingLTFlagFn_mem_FP (constFn_mem_FP []) hb)
    (mem_FP_comp hb gridPredBits_mem_FP) hb

private def pairCoordinateBits (ruler x y : List Bool) : List Bool :=
  routingPadBits (routingCoordinateRuler ruler) x ++
    routingPadBits (routingCoordinateRuler ruler) y

private theorem pairCoordinateBits_eq (ruler x y : List Bool) :
    pairCoordinateBits ruler x y =
      encodeRoutingPoint ruler.length (Nat.fromBitsLE x, Nat.fromBitsLE y) := by
  simp only [pairCoordinateBits, routingPadBits_eq_toBitsLE,
    routingCoordinateRuler_length, encodeRoutingPoint]

private theorem pairCoordinateBitsFn_mem_FP {ruler x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => pairCoordinateBits (ruler z) (x z) (y z)) ∈ FP :=
  appendFn_mem_FP (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr) hx)
    (routingPadBitsFn_mem_FP (routingCoordinateRulerFn_mem_FP hr) hy)

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
  let pack := pairCoordinateBits ruler
  if incoming then
    caseBit₀ (andBit (routingEQFlag y source)
      (andBit (routingLTFlag [] x) (routingLEFlag x col))) (pack xm y)
    (caseBit₀ (andBit (routingEQFlag x col)
      (andBit (routingBetweenFlag source y upper) (notBit (routingEQFlag y source))))
      (pack x (caseBit₀ (routingLTFlag source upper) ym yp))
    (caseBit₀ (andBit (routingEQFlag y upper) (routingLTFlag x col)) (pack xp y)
    (caseBit₀ (andBit (routingEQFlag x [])
      (andBit (routingLEFlag target y) (routingLTFlag y upper))) (pack x yp) (pack x y))))
  else
    caseBit₀ (andBit (routingEQFlag y source) (routingLTFlag x col)) (pack xp y)
    (caseBit₀ (andBit (routingEQFlag x col)
      (andBit (routingBetweenFlag source y upper) (notBit (routingEQFlag y upper))))
      (pack x (caseBit₀ (routingLTFlag source upper) yp ym))
    (caseBit₀ (andBit (routingEQFlag y upper)
      (andBit (routingLTFlag [] x) (routingLEFlag x col))) (pack xm y)
    (caseBit₀ (andBit (routingEQFlag x [])
      (andBit (routingLTFlag target y) (routingLEFlag y upper))) (pack x ym) (pack x y))))

private theorem bitsNil : Nat.fromBitsLE [] = 0 := rfl

private theorem bitsOne : Nat.fromBitsLE [true] = 1 := rfl

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

private theorem flagNot_decide (a : Prop) [Decidable a] :
    notBit [decide a] = [decide (¬a)] := by
  by_cases h : a <;> simp [h, notBit, caseBit₀]

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    caseBit₀ [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, caseBit₀]

/-- The binary step agrees with the natural wire pointer on arbitrary input words. -/
theorem routingWireStepBits_eq_encode (ruler i j x y : List Bool) (incoming : Bool) :
    routingWireStepBits ruler i j x y incoming = encodeRoutingPoint ruler.length
      (if incoming then wirePredecessor (2 ^ ruler.length) (Nat.fromBitsLE i)
        (Nat.fromBitsLE j) (Nat.fromBitsLE x, Nat.fromBitsLE y)
      else wireSuccessor (2 ^ ruler.length) (Nat.fromBitsLE i)
        (Nat.fromBitsLE j) (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  cases incoming <;>
    simp only [routingWireStepBits, Bool.false_eq_true, ↓reduceIte,
      routingEQFlag_value, routingLTFlag_value, routingLEFlag_value,
      routingBetweenFlag_value, routingColumnBits_value, routingSixBits_value,
      routingTargetRowBits_value, flagNot_decide, flagAnd_decide, select_decide,
      wirePredecessor, wireSuccessor]
  all_goals simp only [bitsNil, and_assoc]
  all_goals split_ifs <;>
    simp_all only [pairCoordinateBits_eq, routingAddBits_value,
      routingSaturatingPredBits_value, bitsOne] <;> simp_all <;> split_ifs <;> rfl

/-- Each wire step emits two complete canonical routing coordinate fields. -/
@[simp] theorem routingWireStepBits_length (ruler i j x y : List Bool) (incoming : Bool) :
    (routingWireStepBits ruler i j x y incoming).length = routingPointWidth ruler.length := by
  rw [routingWireStepBits_eq_encode, encodeRoutingPoint_length]
/-- Individual wire steps compose actual polynomial-time producers uniformly. -/
theorem routingWireStepBitsFn_mem_FP (incoming : Bool)
    {ruler i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingWireStepBits (ruler z) (i z) (j z) (x z) (y z) incoming) ∈ FP := by
  have hcol := routingColumnBitsFn_mem_FP hr hi hj
  have hsource := routingSixBitsFn_mem_FP hi
  have htarget := routingSixBitsFn_mem_FP hj
  have hupper := routingTargetRowBitsFn_mem_FP hj
  have hxp := routingAddBitsFn_mem_FP hx (constFn_mem_FP [true])
  have hxm := routingSaturatingPredBitsFn_mem_FP hx
  have hyp := routingAddBitsFn_mem_FP hy (constFn_mem_FP [true])
  have hym := routingSaturatingPredBitsFn_mem_FP hy
  have hxy := pairCoordinateBitsFn_mem_FP hr hx hy
  have hxpy := pairCoordinateBitsFn_mem_FP hr hxp hy
  have hxmy := pairCoordinateBitsFn_mem_FP hr hxm hy
  have hxyp := pairCoordinateBitsFn_mem_FP hr hx hyp
  have hxym := pairCoordinateBitsFn_mem_FP hr hx hym
  have hdir := routingLTFlagFn_mem_FP hsource hupper
  have hbetween := routingBetweenFlagFn_mem_FP hsource hy hupper
  cases incoming
  · exact selectFn_mem_FP
      (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hsource) (routingLTFlagFn_mem_FP hx hcol))
      hxpy
      (selectFn_mem_FP
        (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx hcol)
          (andBitFn_mem_FP hbetween (notBitFn_mem_FP (routingEQFlagFn_mem_FP hy hupper))))
        (pairCoordinateBitsFn_mem_FP hr hx (selectFn_mem_FP hdir hyp hym))
        (selectFn_mem_FP
          (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hupper)
            (andBitFn_mem_FP (routingLTFlagFn_mem_FP (constFn_mem_FP []) hx)
              (routingLEFlagFn_mem_FP hx hcol))) hxmy
          (selectFn_mem_FP
            (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx (constFn_mem_FP []))
              (andBitFn_mem_FP (routingLTFlagFn_mem_FP htarget hy)
                (routingLEFlagFn_mem_FP hy hupper))) hxym hxy)))
  · exact selectFn_mem_FP
      (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hsource)
        (andBitFn_mem_FP (routingLTFlagFn_mem_FP (constFn_mem_FP []) hx)
          (routingLEFlagFn_mem_FP hx hcol))) hxmy
      (selectFn_mem_FP
        (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx hcol)
          (andBitFn_mem_FP hbetween (notBitFn_mem_FP (routingEQFlagFn_mem_FP hy hsource))))
        (pairCoordinateBitsFn_mem_FP hr hx (selectFn_mem_FP hdir hym hyp))
        (selectFn_mem_FP
          (andBitFn_mem_FP (routingEQFlagFn_mem_FP hy hupper) (routingLTFlagFn_mem_FP hx hcol))
          hxpy
          (selectFn_mem_FP
            (andBitFn_mem_FP (routingEQFlagFn_mem_FP hx (constFn_mem_FP []))
              (andBitFn_mem_FP (routingLEFlagFn_mem_FP htarget hy)
                (routingLTFlagFn_mem_FP hy hupper))) hxyp hxy)))

end GameTheory.Complexity.Backend
