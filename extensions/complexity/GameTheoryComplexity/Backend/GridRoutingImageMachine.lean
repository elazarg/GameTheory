import GameTheoryComplexity.Backend.GridRoutingCrossingMachine
import GameTheoryComplexity.Backend.GridRoutingWireMachine
import GameTheory.Math.GridWireSwitch

/-! Crossing image coordinates and owner switches are computed by local binary
queries and exact arithmetic. Fields retain their full values until a caller
chooses a serialization width. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

private def bendAxisBits (bits flag : List Bool) (increasing : Bool) : List Bool :=
  routingAddBits (routingSaturatingPredBits bits)
    (if increasing then caseBit₀ flag [false, true] [] else caseBit₀ flag [] [false, true])

private def selectImageAxisBits (bits direction cross isI isK : List Bool)
    (axisX : Bool) : List Bool :=
  caseBit₀ cross (caseBit₀ isI (bendAxisBits bits direction (!axisX))
    (caseBit₀ isK (bendAxisBits bits direction axisX) bits)) bits

private def imageAxisBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) (axisX : Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  let direction := if axisX then routingEQFlag y (routingSixBits i)
    else routingLTFlag (routingSixBits k) (routingTargetRowBits (routingQueryBits ruler S k))
  let bits := if axisX then x else y
  selectImageAxisBits bits direction (routingCrossingFlag ruler P S x y)
    (routingEQFlag owner i) (routingEQFlag owner k) axisX

/-- Exact horizontal coordinate of an imaged source-indexed wire occurrence. -/
def routingImageXBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool := imageAxisBits ruler P S owner x y true

/-- Exact vertical coordinate of an imaged source-indexed wire occurrence. -/
def routingImageYBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool := imageAxisBits ruler P S owner x y false

/-- Swap the two crossing owners, keeping all other owner labels unchanged. -/
def routingSwitchOwnerBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  caseBit₀ (routingCrossingFlag ruler P S x y)
    (caseBit₀ (routingEQFlag owner i) k (caseBit₀ (routingEQFlag owner k) i owner)) owner

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    caseBit₀ [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, caseBit₀]

private theorem crossingFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingCrossingFlag ruler P S x y =
      [decide (crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (Nat.fromBitsLE x, Nat.fromBitsLE y) ≠ none)] := by
  have hl := routingCrossingFlag_length ruler P S x y
  have ha := routingCrossingFlag_accept ruler P S x y
  cases hf : routingCrossingFlag ruler P S x y with
  | nil => simp [hf] at hl
  | cons bit rest =>
    cases rest with
    | nil => cases bit <;> simp_all
    | cons c cs => simp [hf] at hl

private theorem crossingLabels {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ} {i k : ℕ}
    (hc : crossingOwners n P S p = some (i,k)) :
    horizontalOwner P p = i ∧ verticalOwner n p = k := by
  dsimp only [crossingOwners] at hc
  split_ifs at hc
  exact Prod.mk.inj (Option.some.inj hc)

private theorem bitsZero : Nat.fromBitsLE [] = 0 := rfl
private theorem bitsTwo : Nat.fromBitsLE [false, true] = 2 := rfl

private theorem bendAxisBits_value (bits : List Bool) (a : Prop) [Decidable a]
    (increasing : Bool) : Nat.fromBitsLE (bendAxisBits bits [decide a] increasing) =
      Nat.fromBitsLE bits - 1 + (if increasing then if a then 2 else 0
        else if a then 0 else 2) := by
  cases increasing <;> by_cases h : a <;>
    simp [bendAxisBits, routingAddBits_value, routingSaturatingPredBits_value,
      h, caseBit₀, bitsZero, bitsTwo]

private theorem imageAxisBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) (axisX : Bool) : Nat.fromBitsLE
      (imageAxisBits ruler P S owner x y axisX) =
      (if axisX then Prod.fst else Prod.snd)
        (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (Nat.fromBitsLE owner)
          (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  cases hc : crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (Nat.fromBitsLE x, Nat.fromBitsLE y) with
  | none =>
    cases axisX <;>
      simp [imageAxisBits, selectImageAxisBits, crossingFlag_value, hc, wireImagePoint]
  | some owners =>
    rcases owners with ⟨i,k⟩
    obtain ⟨hi,hk⟩ := crossingLabels hc
    have hi' : Nat.fromBitsLE (routingHorizontalOwnerBits ruler P y) = i :=
      (routingHorizontalOwnerBits_value ruler P y).trans hi
    have hk' : Nat.fromBitsLE (routingVerticalOwnerBits ruler x) = k :=
      (routingVerticalOwnerBits_value ruler x).trans hk
    cases axisX <;>
      simp only [imageAxisBits, selectImageAxisBits, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte,
        crossingFlag_value, hc, select_decide]
    all_goals simp only [routingEQFlag_value, routingLTFlag_value, routingSixBits_value,
      routingTargetRowBits_value, routingQueryBits_value, hi', hk', select_decide]
    all_goals split_ifs <;>
      simp_all [bendAxisBits_value, wireImagePoint, placedCoordinate,
        horizontalBend, verticalBend, crossingCoordinate]
    all_goals by_cases hright : Nat.fromBitsLE y = 6 * i
    all_goals by_cases hup : 6 * k < 6 * routingOriginalPointer ruler S k + 3
    all_goals simp_all <;> split_ifs <;> simp_all <;> omega

/-- The horizontal image field agrees with the natural geometric realization. -/
theorem routingImageXBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : Nat.fromBitsLE (routingImageXBits ruler P S owner x y) =
      (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (Nat.fromBitsLE owner)
        (Nat.fromBitsLE x, Nat.fromBitsLE y)).1 :=
  imageAxisBits_value ruler P S owner x y true

/-- The vertical image field agrees with the natural geometric realization. -/
theorem routingImageYBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : Nat.fromBitsLE (routingImageYBits ruler P S owner x y) =
      (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (Nat.fromBitsLE owner)
        (Nat.fromBitsLE x, Nat.fromBitsLE y)).2 :=
  imageAxisBits_value ruler P S owner x y false


/-- The owner field agrees with the natural crossing switch on every interior label. -/
theorem routingSwitchOwnerBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) :
    routedSwitch (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (.inr (Nat.fromBitsLE owner,
        (Nat.fromBitsLE x, Nat.fromBitsLE y))) =
      .inr (Nat.fromBitsLE (routingSwitchOwnerBits ruler P S owner x y),
        (Nat.fromBitsLE x, Nat.fromBitsLE y)) := by
  cases hc : crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (Nat.fromBitsLE x, Nat.fromBitsLE y) with
  | none => simp [routingSwitchOwnerBits, crossingFlag_value, hc, routedSwitch, caseBit₀]
  | some owners =>
    rcases owners with ⟨i,k⟩
    obtain ⟨hi,hk⟩ := crossingLabels hc
    have hi' : Nat.fromBitsLE (routingHorizontalOwnerBits ruler P y) = i :=
      (routingHorizontalOwnerBits_value ruler P y).trans hi
    have hk' : Nat.fromBitsLE (routingVerticalOwnerBits ruler x) = k :=
      (routingVerticalOwnerBits_value ruler x).trans hk
    simp only [routingSwitchOwnerBits, crossingFlag_value, hc, select_decide,
      routingEQFlag_value, hi', hk', routedSwitch]
    split_ifs <;> simp_all

private theorem bendAxisBitsFn_mem_FP (increasing : Bool)
    {bits flag : List Bool → List Bool} (hb : bits ∈ FP) (hf : flag ∈ FP) :
    (fun z => bendAxisBits (bits z) (flag z) increasing) ∈ FP := by
  cases increasing
  · exact routingAddBitsFn_mem_FP (routingSaturatingPredBitsFn_mem_FP hb)
      (selectFn_mem_FP hf (constFn_mem_FP []) (constFn_mem_FP [false,true]))
  · exact routingAddBitsFn_mem_FP (routingSaturatingPredBitsFn_mem_FP hb)
      (selectFn_mem_FP hf (constFn_mem_FP [false,true]) (constFn_mem_FP []))

private theorem selectImageAxisBitsFn_mem_FP (axisX : Bool)
    {bits direction cross isI isK : List Bool → List Bool}
    (hb : bits ∈ FP) (hd : direction ∈ FP) (hc : cross ∈ FP)
    (hi : isI ∈ FP) (hk : isK ∈ FP) :
    (fun z => selectImageAxisBits (bits z) (direction z) (cross z) (isI z) (isK z) axisX) ∈ FP := by
  have hhorizontal := bendAxisBitsFn_mem_FP (!axisX) (bits := bits) (flag := direction) hb hd
  have hvertical := bendAxisBitsFn_mem_FP axisX (bits := bits) (flag := direction) hb hd
  have htail := selectFn_mem_FP hi hhorizontal (selectFn_mem_FP hk hvertical hb)
  exact selectFn_mem_FP hc htail hb

private theorem imageAxisBitsUniformFn_mem_FP (axisX : Bool)
    (P S : List Bool → List Bool → List Bool)
    {ruler seed owner x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => imageAxisBits (ruler z) (P (seed z)) (S (seed z))
      (owner z) (x z) (y z) axisX) ∈ FP := by
  have hi := routingHorizontalOwnerBitsUniformFn_mem_FP P hr hs hy hP
  have hk := routingVerticalOwnerBitsFn_mem_FP hr hx
  let cross := fun z => routingCrossingFlag (ruler z) (P (seed z)) (S (seed z)) (x z) (y z)
  let isI := fun z => routingEQFlag (owner z)
    (routingHorizontalOwnerBits (ruler z) (P (seed z)) (y z))
  let isK := fun z => routingEQFlag (owner z) (routingVerticalOwnerBits (ruler z) (x z))
  have hcross : cross ∈ FP := routingCrossingFlagUniformFn_mem_FP P S hr hs hx hy hP hS
  have hownerI : isI ∈ FP := routingEQFlagFn_mem_FP ho hi
  have hownerK : isK ∈ FP := routingEQFlagFn_mem_FP ho hk
  let rightward := fun z => routingEQFlag (y z)
    (routingSixBits (routingHorizontalOwnerBits (ruler z) (P (seed z)) (y z)))
  let upward := fun z => routingLTFlag
    (routingSixBits (routingVerticalOwnerBits (ruler z) (x z)))
    (routingTargetRowBits (routingQueryBits (ruler z) (S (seed z))
      (routingVerticalOwnerBits (ruler z) (x z))))
  have hright : rightward ∈ FP := routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP hi)
  have hsk := routingQueryBitsUniformFn_mem_FP S hr hs hk hS
  have hupper := routingTargetRowBitsFn_mem_FP hsk
  have hkrow := routingSixBitsFn_mem_FP hk
  have hup : upward ∈ FP := routingLTFlagFn_mem_FP hkrow hupper
  cases axisX
  · have hcert := selectImageAxisBitsFn_mem_FP false
      (bits := y) (direction := upward) (cross := cross) (isI := isI) (isK := isK)
      hy hup hcross hownerI hownerK
    have he : (fun z => imageAxisBits (ruler z) (P (seed z)) (S (seed z))
        (owner z) (x z) (y z) false) =
        (fun z => selectImageAxisBits (y z) (upward z) (cross z) (isI z) (isK z) false) := by
      funext z
      simp only [imageAxisBits, cross, isI, isK, upward, Bool.false_eq_true, ↓reduceIte]
    rw [he]
    exact hcert
  · have hcert := selectImageAxisBitsFn_mem_FP true
      (bits := x) (direction := rightward) (cross := cross) (isI := isI) (isK := isK)
      hx hright hcross hownerI hownerK
    have he : (fun z => imageAxisBits (ruler z) (P (seed z)) (S (seed z))
        (owner z) (x z) (y z) true) =
        (fun z => selectImageAxisBits (x z) (rightward z) (cross z) (isI z) (isK z) true) := by
      funext z
      simp only [imageAxisBits, cross, isI, isK, rightward, ↓reduceIte]
    rw [he]
    exact hcert

/-- Horizontal image coordinates have one uniform actual polynomial-time certificate. -/
theorem routingImageXBitsUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool)
    {ruler seed owner x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingImageXBits (ruler z) (P (seed z)) (S (seed z))
      (owner z) (x z) (y z)) ∈ FP :=
  imageAxisBitsUniformFn_mem_FP true P S hr hs ho hx hy hP hS

/-- Vertical image coordinates have one uniform actual polynomial-time certificate. -/
theorem routingImageYBitsUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool)
    {ruler seed owner x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingImageYBits (ruler z) (P (seed z)) (S (seed z))
      (owner z) (x z) (y z)) ∈ FP :=
  imageAxisBitsUniformFn_mem_FP false P S hr hs ho hx hy hP hS

/-- Switching source labels uses a constant number of polynomial-time local queries. -/
theorem routingSwitchOwnerBitsUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool)
    {ruler seed owner x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingSwitchOwnerBits (ruler z) (P (seed z)) (S (seed z))
      (owner z) (x z) (y z)) ∈ FP := by
  have hi := routingHorizontalOwnerBitsUniformFn_mem_FP P hr hs hy hP
  have hk := routingVerticalOwnerBitsFn_mem_FP hr hx
  exact selectFn_mem_FP (routingCrossingFlagUniformFn_mem_FP P S hr hs hx hy hP hS)
    (selectFn_mem_FP (routingEQFlagFn_mem_FP ho hi) hk
      (selectFn_mem_FP (routingEQFlagFn_mem_FP ho hk) hi ho)) ho

end GameTheory.Complexity.Backend








