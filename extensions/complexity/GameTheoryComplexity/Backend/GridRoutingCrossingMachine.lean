module

public import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
public import GameTheoryComplexity.Backend.GridRoutingQueries

@[expose] public section

/-! Crossing validation identifies two local owners and checks their consistent
edges and strict interiors. Guarded original queries retain out-of-range labels
as isolated points rather than narrowing them into unrelated vertices. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

/-- Recover the horizontal owner using an exact row divisibility test. -/
def routingHorizontalOwnerBits (ruler : List Bool) (query : List Bool → List Bool)
    (y : List Bool) : List Bool :=
  let row := routingDivSixBits y
  select (routingEQFlag y (routingSixBits row)) row (routingQueryBits ruler query row)

private theorem multiple_six (y : ℕ) : y = 6 * (y / 6) ↔ y % 6 = 0 := by omega

/-- Owner extraction agrees with the natural guarded original pointer. -/
theorem routingHorizontalOwnerBits_value (ruler : List Bool) (query : List Bool → List Bool)
    (y : List Bool) : lsbValue (routingHorizontalOwnerBits ruler query y) =
      horizontalOwner (routingOriginalPointer ruler query) (0, lsbValue y) := by
  simp only [routingHorizontalOwnerBits, routingEQFlag_value, routingSixBits_value,
    routingDivSixBits_value, horizontalOwner]
  by_cases hy : lsbValue y % 6 = 0
  · have he := (multiple_six (lsbValue y)).mpr hy
    have hd : decide (lsbValue y = 6 * (lsbValue y / 6)) = true :=
      decide_eq_true he
    simp only [hd, hy, select, List.headD_cons, ite_true, routingDivSixBits_value]
  · have he : ¬ lsbValue y = 6 * (lsbValue y / 6) := by
      exact mt (multiple_six _).mp hy
    have hd : decide (lsbValue y = 6 * (lsbValue y / 6)) = false :=
      decide_eq_false he
    simp only [hd, hy, select, List.headD_cons, Bool.false_eq_true, ite_false, routingQueryBits_value,
      routingDivSixBits_value]

/-- Validate both locally identified consistent edges and their strict crossing. -/
def routingCrossingFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  let si := routingQueryBits ruler S i
  let sk := routingQueryBits ruler S k
  andFlag (routingActiveEdgeFlag ruler P S i)
    (andFlag (routingActiveEdgeFlag ruler P S k)
      (andFlag (notFlag (routingEQFlag i k))
        (andFlag (routingHorizontalInteriorFlag ruler i si x y)
          (routingVerticalInteriorFlag ruler k sk x y))))

private theorem andFlag_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

private theorem notFlag_decide (a : Prop) [Decidable a] :
    notFlag [decide a] = [decide (¬a)] := by
  by_cases ha : a <;> simp [ha, notFlag]

/-- The crossing flag accepts exactly the natural decoder's successful owner query. -/
theorem routingCrossingFlag_accept (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingCrossingFlag ruler P S x y = [true] ↔
      crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (lsbValue x, lsbValue y) ≠ none := by
  simp only [routingCrossingFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingHorizontalInteriorFlag_value, routingVerticalInteriorFlag_value,
    routingQueryBits_value, routingHorizontalOwnerBits_value, routingVerticalOwnerBits_value,
    notFlag_decide, andFlag_decide]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  unfold crossingOwners
  dsimp only
  split_ifs <;> simp_all only [activeEdge, horizontalOwner, verticalOwner] <;> tauto

/-- Proper-crossing validation always produces one Boolean flag. -/
@[simp] theorem routingCrossingFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : (routingCrossingFlag ruler P S x y).length = 1 := by
  simp only [routingCrossingFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingHorizontalInteriorFlag_value, routingVerticalInteriorFlag_value,
    notFlag_decide, andFlag_decide]
  rfl

/-- Horizontal owner extraction charges native division and the guarded query. -/
@[fun_prop] theorem routingHorizontalOwnerBitsUniform_polyTime
    (query : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hq : ComputableInPolyTime (fun p : List Bool × List Bool => query p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingHorizontalOwnerBits (ruler z) (query (seed z)) (y z))
      enc encBits := by
  have hrow := routingDivSixBits_polyTime hy
  exact select_polyTime.comp ((routingEQFlag_polyTime hy (routingSixBits_polyTime hrow)).prod
    (hrow.prod (routingQueryBitsUniform_polyTime query hr hs hrow hq)))

/-- Proper-crossing validation charges all local arithmetic and both native queries. -/
@[fun_prop] theorem routingCrossingFlagUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingCrossingFlag (ruler z) (P (seed z)) (S (seed z))
      (x z) (y z)) enc encBits := by
  have hi := routingHorizontalOwnerBitsUniform_polyTime P hr hs hy hP
  have hk := routingVerticalOwnerBits_polyTime hr hx
  have hsi := routingQueryBitsUniform_polyTime S hr hs hi hS
  have hsk := routingQueryBitsUniform_polyTime S hr hs hk hS
  exact andFlag_polyTime.comp ((routingActiveEdgeFlagUniform_polyTime P S hr hs hi hP hS).prod
    (andFlag_polyTime.comp ((routingActiveEdgeFlagUniform_polyTime P S hr hs hk hP hS).prod
      (andFlag_polyTime.comp ((notFlag_polyTime.comp (routingEQFlag_polyTime hi hk)).prod
        (andFlag_polyTime.comp ((routingHorizontalInteriorFlag_polyTime hr hi hsi hx hy).prod
          (routingVerticalInteriorFlag_polyTime hr hk hsk hx hy))))))))

end GameTheory.Complexity.Backend
