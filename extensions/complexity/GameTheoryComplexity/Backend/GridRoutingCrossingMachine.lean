import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
import GameTheoryComplexity.Backend.GridRoutingQueries

/-! Crossing validation identifies two local owners and checks their consistent
edges and strict interiors. Guarded original queries retain out-of-range labels
as isolated points rather than narrowing them into unrelated vertices. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.GridWire GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

/-- Recover the horizontal owner using an exact row divisibility test. -/
def routingHorizontalOwnerBits (ruler : List Bool) (query : List Bool → List Bool)
    (y : List Bool) : List Bool :=
  let row := routingDivSixBits y
  caseBit₀ (routingEQFlag y (routingSixBits row)) row (routingQueryBits ruler query row)

private theorem multiple_six (y : ℕ) : y = 6 * (y / 6) ↔ y % 6 = 0 := by omega

/-- Owner extraction agrees with the natural guarded original pointer. -/
theorem routingHorizontalOwnerBits_value (ruler : List Bool) (query : List Bool → List Bool)
    (y : List Bool) : Nat.fromBitsLE (routingHorizontalOwnerBits ruler query y) =
      horizontalOwner (routingOriginalPointer ruler query) (0, Nat.fromBitsLE y) := by
  simp only [routingHorizontalOwnerBits, routingEQFlag_value, routingSixBits_value,
    routingDivSixBits_value, horizontalOwner]
  by_cases hy : Nat.fromBitsLE y % 6 = 0
  · have he := (multiple_six (Nat.fromBitsLE y)).mpr hy
    have hd : decide (Nat.fromBitsLE y = 6 * (Nat.fromBitsLE y / 6)) = true :=
      decide_eq_true he
    simp only [hd, hy, caseBit₀, Bool.cond_true, ite_true, routingDivSixBits_value]
  · have he : ¬ Nat.fromBitsLE y = 6 * (Nat.fromBitsLE y / 6) := by
      exact mt (multiple_six _).mp hy
    have hd : decide (Nat.fromBitsLE y = 6 * (Nat.fromBitsLE y / 6)) = false :=
      decide_eq_false he
    simp only [hd, hy, caseBit₀, Bool.cond_false, ite_false, routingQueryBits_value,
      routingDivSixBits_value]

/-- Validate both locally identified consistent edges and their strict crossing. -/
def routingCrossingFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  let i := routingHorizontalOwnerBits ruler P y
  let k := routingVerticalOwnerBits ruler x
  let si := routingQueryBits ruler S i
  let sk := routingQueryBits ruler S k
  andBit (routingActiveEdgeFlag ruler P S i)
    (andBit (routingActiveEdgeFlag ruler P S k)
      (andBit (notBit (routingEQFlag i k))
        (andBit (routingHorizontalInteriorFlag ruler i si x y)
          (routingVerticalInteriorFlag ruler k sk x y))))

private theorem andBit_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

private theorem notBit_decide (a : Prop) [Decidable a] :
    notBit [decide a] = [decide (¬a)] := by
  by_cases ha : a <;> simp [ha, notBit, caseBit₀]

/-- The crossing flag accepts exactly the natural decoder's successful owner query. -/
theorem routingCrossingFlag_accept (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingCrossingFlag ruler P S x y = [true] ↔
      crossingOwners (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S) (Nat.fromBitsLE x, Nat.fromBitsLE y) ≠ none := by
  simp only [routingCrossingFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingHorizontalInteriorFlag_value, routingVerticalInteriorFlag_value,
    routingQueryBits_value, routingHorizontalOwnerBits_value, routingVerticalOwnerBits_value,
    notBit_decide, andBit_decide]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  unfold crossingOwners
  dsimp only
  split_ifs <;> simp_all only [activeEdge, horizontalOwner, verticalOwner] <;> tauto

/-- Proper-crossing validation always produces one Boolean flag. -/
@[simp] theorem routingCrossingFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : (routingCrossingFlag ruler P S x y).length = 1 := by
  simp only [routingCrossingFlag, routingActiveEdgeFlag_value, routingEQFlag_value,
    routingHorizontalInteriorFlag_value, routingVerticalInteriorFlag_value,
    notBit_decide, andBit_decide]
  rfl

/-- Horizontal owner extraction composes guarded original queries uniformly. -/
theorem routingHorizontalOwnerBitsUniformFn_mem_FP
    (query : List Bool → List Bool → List Bool) {ruler seed y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hy : y ∈ FP)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingHorizontalOwnerBits (ruler z) (query (seed z)) (y z)) ∈ FP := by
  have hrow := mem_FP_comp (f := y) (g := routingDivSixBits) hy routingDivSixBits_mem_FP
  exact selectFn_mem_FP (routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP hrow)) hrow
    (routingQueryBitsUniformFn_mem_FP query hr hs hrow hq)

/-- Proper-crossing validation uses only polynomial-time local arithmetic and queries. -/
theorem routingCrossingFlagUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool) {ruler seed x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingCrossingFlag (ruler z) (P (seed z)) (S (seed z)) (x z) (y z)) ∈ FP := by
  have hi := routingHorizontalOwnerBitsUniformFn_mem_FP P hr hs hy hP
  have hk := routingVerticalOwnerBitsFn_mem_FP hr hx
  have hsi := routingQueryBitsUniformFn_mem_FP S hr hs hi hS
  have hsk := routingQueryBitsUniformFn_mem_FP S hr hs hk hS
  exact andBitFn_mem_FP (routingActiveEdgeFlagUniformFn_mem_FP P S hr hs hi hP hS)
    (andBitFn_mem_FP (routingActiveEdgeFlagUniformFn_mem_FP P S hr hs hk hP hS)
      (andBitFn_mem_FP (notBitFn_mem_FP (routingEQFlagFn_mem_FP hi hk))
        (andBitFn_mem_FP (routingHorizontalInteriorFlagFn_mem_FP hr hi hsi hx hy)
          (routingVerticalInteriorFlagFn_mem_FP hr hk hsk hx hy))))

end GameTheory.Complexity.Backend
