module

public import GameTheoryComplexity.Backend.GridRoutingCrossingMachine
public import GameTheoryComplexity.Backend.GridRoutingWireMachine
public import GameTheory.Math.GridWireSwitch

@[expose] public section

/-! Crossing image coordinates and owner switches are computed by local binary
queries and exact arithmetic. Fields retain their full values until a caller
chooses a serialization width. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing

/-- Move one binary axis to its selected spacing-three bend. -/
def routingBendAxisBits (bits flag : List Bool) (increasing : Bool) : List Bool :=
  routingAddBits (routingSaturatingPredBits bits)
    (if increasing then select flag [false, true] [] else select flag [] [false, true])

/-- Select the exact axis of an owner occurrence at a proper crossing. -/
def routingSelectImageAxisBits (bits direction cross isI isK : List Bool)
    (axisX : Bool) : List Bool :=
  select cross (select isI (routingBendAxisBits bits direction (!axisX))
    (select isK (routingBendAxisBits bits direction axisX) bits)) bits

/-- Compute either realized image axis without narrowing the raw fields. -/
def routingImageAxisBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) (axisX : Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  let direction := if axisX then routingEQFlag y (routingSixBits i)
    else routingLTFlag (routingSixBits k) (routingTargetRowBits (routingQueryBits ruler S k))
  let bits := if axisX then x else y
  routingSelectImageAxisBits bits direction (routingCrossingFlag ruler P S x y)
    (routingEQFlag owner i) (routingEQFlag owner k) axisX

/-- Exact horizontal coordinate of an imaged source-indexed wire occurrence. -/
def routingImageXBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool := routingImageAxisBits ruler P S owner x y true

/-- Exact vertical coordinate of an imaged source-indexed wire occurrence. -/
def routingImageYBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool := routingImageAxisBits ruler P S owner x y false

/-- Swap the two crossing owners, keeping all other owner labels unchanged. -/
def routingSwitchOwnerBits (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  select (routingCrossingFlag ruler P S x y)
    (select (routingEQFlag owner i) k (select (routingEQFlag owner k) i owner)) owner

private theorem select_decide (a : Prop) [Decidable a] (x y : List Bool) :
    select [decide a] x y = if a then x else y := by
  by_cases h : a <;> simp [h, select]

private theorem crossingFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingCrossingFlag ruler P S x y =
      [decide (crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) ≠ none)] := by
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

private theorem bitsZero : lsbValue [] = 0 := rfl
private theorem bitsTwo : lsbValue [false, true] = 2 := rfl

private theorem bendAxisBits_value (bits : List Bool) (a : Prop) [Decidable a]
    (increasing : Bool) : lsbValue (routingBendAxisBits bits [decide a] increasing) =
      lsbValue bits - 1 + (if increasing then if a then 2 else 0
        else if a then 0 else 2) := by
  cases increasing <;> by_cases h : a <;>
    simp [routingBendAxisBits, routingAddBits_value, routingSaturatingPredBits_value,
      h, select, bitsZero, bitsTwo]

private theorem imageAxisBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) (axisX : Bool) : lsbValue
      (routingImageAxisBits ruler P S owner x y axisX) =
      (if axisX then Prod.fst else Prod.snd)
        (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
          (routingOriginalPointer ruler S) (lsbValue owner)
          (lsbValue x, lsbValue y)) := by
  cases hc : crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) with
  | none =>
    cases axisX <;>
      simp [routingImageAxisBits, routingSelectImageAxisBits, crossingFlag_value, hc, wireImagePoint]
  | some owners =>
    rcases owners with ⟨i,k⟩
    obtain ⟨hi,hk⟩ := crossingLabels hc
    have hi' : lsbValue (routingHorizontalOwnerBits ruler P y) = i :=
      (routingHorizontalOwnerBits_value ruler P y).trans hi
    have hk' : lsbValue (routingVerticalOwnerBits ruler x) = k :=
      (routingVerticalOwnerBits_value ruler x).trans hk
    cases axisX <;>
      simp only [routingImageAxisBits, routingSelectImageAxisBits, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte,
        crossingFlag_value, hc, select_decide]
    all_goals simp only [routingEQFlag_value, routingLTFlag_value, routingSixBits_value,
      routingTargetRowBits_value, routingQueryBits_value, hi', hk', select_decide]
    all_goals split_ifs <;>
      simp_all [bendAxisBits_value, wireImagePoint, placedCoordinate,
        horizontalBend, verticalBend, crossingCoordinate]
    all_goals by_cases hright : lsbValue y = 6 * i
    all_goals by_cases hup : 6 * k < 6 * routingOriginalPointer ruler S k + 3
    all_goals simp_all
    all_goals split_ifs <;> simp_all
    all_goals omega

/-- The horizontal image field agrees with the natural geometric realization. -/
theorem routingImageXBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : lsbValue (routingImageXBits ruler P S owner x y) =
      (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue owner)
        (lsbValue x, lsbValue y)).1 :=
  imageAxisBits_value ruler P S owner x y true

/-- The vertical image field agrees with the natural geometric realization. -/
theorem routingImageYBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : lsbValue (routingImageYBits ruler P S owner x y) =
      (wireImagePoint (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue owner)
        (lsbValue x, lsbValue y)).2 :=
  imageAxisBits_value ruler P S owner x y false


/-- The owner field agrees with the natural crossing switch on every interior label. -/
theorem routingSwitchOwnerBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) :
    routedSwitch (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (.inr (lsbValue owner,
        (lsbValue x, lsbValue y))) =
      .inr (lsbValue (routingSwitchOwnerBits ruler P S owner x y),
        (lsbValue x, lsbValue y)) := by
  cases hc : crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
      (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) with
  | none => simp [routingSwitchOwnerBits, crossingFlag_value, hc, routedSwitch, select]
  | some owners =>
    rcases owners with ⟨i,k⟩
    obtain ⟨hi,hk⟩ := crossingLabels hc
    have hi' : lsbValue (routingHorizontalOwnerBits ruler P y) = i :=
      (routingHorizontalOwnerBits_value ruler P y).trans hi
    have hk' : lsbValue (routingVerticalOwnerBits ruler x) = k :=
      (routingVerticalOwnerBits_value ruler x).trans hk
    simp only [routingSwitchOwnerBits, crossingFlag_value, hc, select_decide,
      routingEQFlag_value, hi', hk', routedSwitch]
    split_ifs <;> simp_all

/-- A bend charges its native saturating predecessor and retained-carry offset. -/
@[fun_prop] theorem routingBendAxisBits_polyTime (increasing : Bool)
    {α : Type} {enc : α ↪ List Bool} {bits flag : α → List Bool}
    (hbits : ComputableInPolyTime bits enc encBits)
    (hflag : ComputableInPolyTime flag enc encBits) :
    ComputableInPolyTime (fun z => routingBendAxisBits (bits z) (flag z) increasing) enc encBits := by
  cases increasing
  · exact routingAddBits_polyTime (routingSaturatingPredBits_polyTime hbits)
      (select_polyTime.comp (hflag.prod ((const []).prod (const [false, true]))))
  · exact routingAddBits_polyTime (routingSaturatingPredBits_polyTime hbits)
      (select_polyTime.comp (hflag.prod ((const [false, true]).prod (const []))))

/-- Image selection charges all complete candidate fields and Boolean guards. -/
@[fun_prop] theorem routingSelectImageAxisBits_polyTime (axisX : Bool)
    {α : Type} {enc : α ↪ List Bool} {bits direction cross isI isK : α → List Bool}
    (hbits : ComputableInPolyTime bits enc encBits)
    (hdirection : ComputableInPolyTime direction enc encBits)
    (hcross : ComputableInPolyTime cross enc encBits)
    (hisI : ComputableInPolyTime isI enc encBits)
    (hisK : ComputableInPolyTime isK enc encBits) :
    ComputableInPolyTime (fun z => routingSelectImageAxisBits (bits z) (direction z) (cross z) (isI z) (isK z) axisX) enc encBits := by
  have hhorizontal := routingBendAxisBits_polyTime (!axisX) hbits hdirection
  have hvertical := routingBendAxisBits_polyTime axisX hbits hdirection
  have htail := select_polyTime.comp (hisI.prod (hhorizontal.prod
    (select_polyTime.comp (hisK.prod (hvertical.prod hbits)))))
  exact select_polyTime.comp (hcross.prod (htail.prod hbits))

/-- Both image axes use native seeded local queries and binary arithmetic. -/
@[fun_prop] theorem routingImageAxisBitsUniform_polyTime (axisX : Bool)
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingImageAxisBits (ruler z) (P (seed z)) (S (seed z)) (owner z) (x z) (y z) axisX) enc encBits := by
  have hi := routingHorizontalOwnerBitsUniform_polyTime P hruler hseed hy hP
  have hk := routingVerticalOwnerBits_polyTime hruler hx
  have hcross := routingCrossingFlagUniform_polyTime P S hruler hseed hx hy hP hS
  have hownerI := routingEQFlag_polyTime howner hi
  have hownerK := routingEQFlag_polyTime howner hk
  have hright := routingEQFlag_polyTime hy (routingSixBits_polyTime hi)
  have hsk := routingQueryBitsUniform_polyTime S hruler hseed hk hS
  have hup := routingLTFlag_polyTime (routingSixBits_polyTime hk) (routingTargetRowBits_polyTime hsk)
  cases axisX
  · exact routingSelectImageAxisBits_polyTime false hy hup hcross hownerI hownerK
  · exact routingSelectImageAxisBits_polyTime true hx hright hcross hownerI hownerK

/-- The image coordinate has one native uniform polynomial-time machine. -/
@[fun_prop] theorem routingImageXBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingImageXBits (ruler z) (P (seed z)) (S (seed z)) (owner z) (x z) (y z)) enc encBits := by
  exact routingImageAxisBitsUniform_polyTime true P S hruler hseed howner hx hy hP hS

/-- The image coordinate has one native uniform polynomial-time machine. -/
@[fun_prop] theorem routingImageYBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingImageYBits (ruler z) (P (seed z)) (S (seed z)) (owner z) (x z) (y z)) enc encBits := by
  exact routingImageAxisBitsUniform_polyTime false P S hruler hseed howner hx hy hP hS

/-- Owner switching charges a constant number of native seeded local queries. -/
@[fun_prop] theorem routingSwitchOwnerBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (howner : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingSwitchOwnerBits (ruler z) (P (seed z)) (S (seed z)) (owner z) (x z) (y z)) enc encBits := by
  have hi := routingHorizontalOwnerBitsUniform_polyTime P hruler hseed hy hP
  have hk := routingVerticalOwnerBits_polyTime hruler hx
  exact select_polyTime.comp ((routingCrossingFlagUniform_polyTime P S hruler hseed hx hy hP hS).prod
    ((select_polyTime.comp ((routingEQFlag_polyTime howner hi).prod
      (hk.prod (select_polyTime.comp ((routingEQFlag_polyTime howner hk).prod
        (hi.prod howner)))))).prod howner))

end GameTheory.Complexity.Backend
