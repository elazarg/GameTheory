import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
import GameTheoryComplexity.Backend.GridRoutingQueries

/-! Binary live-label tests validate bounded original vertices and active wire
interiors. Coordinates and owner fields retain their full raw numeric values. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.GridWire

/-- A vertex label is live exactly when its raw value fits the original vertex set. -/
def routingLiveVertexFlag (ruler owner : List Bool) : List Bool :=
  routingLTFlag owner (routingVertexBoundBits ruler)

/-- Validate an active wire interior and exclude its two original endpoint coordinates. -/
def routingLiveInteriorFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool :=
  let next := routingQueryBits ruler S owner
  let sourceVertex := andBit (routingEQFlag x []) (routingEQFlag y (routingSixBits owner))
  let targetVertex := andBit (routingEQFlag x []) (routingEQFlag y (routingSixBits next))
  andBit (routingActiveEdgeFlag ruler P S owner)
    (andBit (routingOnWireFlag ruler owner next x y)
      (andBit (notBit sourceVertex) (notBit targetVertex)))

/-- Vertex liveness agrees with the natural label predicate for arbitrary pointers. -/
theorem routingLiveVertexFlag_value (ruler owner : List Bool) (P S : ℕ → ℕ) :
    routingLiveVertexFlag ruler owner =
      [decide (liveWireNode (2 ^ ruler.length) P S (.inl (Nat.fromBitsLE owner)))] := by
  simp only [routingLiveVertexFlag, routingLTFlag_value, routingVertexBoundBits_value,
    liveWireNode]
  congr 2

/-- Vertex liveness always emits one Boolean flag. -/
@[simp] theorem routingLiveVertexFlag_length (ruler owner : List Bool) :
    (routingLiveVertexFlag ruler owner).length = 1 :=
  routingLTFlag_length _ _

/-- Vertex liveness composes arbitrary polynomial-time ruler and owner producers. -/
theorem routingLiveVertexFlagFn_mem_FP {ruler owner : List Bool → List Bool}
    (hr : ruler ∈ FP) (ho : owner ∈ FP) :
    (fun z => routingLiveVertexFlag (ruler z) (owner z)) ∈ FP :=
  routingLTFlagFn_mem_FP ho (routingVertexBoundBitsFn_mem_FP hr)

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andBit [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andBit, caseBit₀]

private theorem flagNot_decide (a : Prop) [Decidable a] :
    notBit [decide a] = [decide (¬a)] := by
  by_cases h : a <;> simp [h, notBit, caseBit₀]

/-- Interior liveness is exactly the natural predicate, including endpoint exclusion. -/
theorem routingLiveInteriorFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : routingLiveInteriorFlag ruler P S owner x y =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S)
        (.inr (Nat.fromBitsLE owner, (Nat.fromBitsLE x, Nat.fromBitsLE y))))] := by
  simp only [routingLiveInteriorFlag, routingActiveEdgeFlag_value, routingOnWireFlag_value,
    routingEQFlag_value, routingSixBits_value, routingQueryBits_value,
    flagAnd_decide, flagNot_decide, liveWireNode, vertexPoint]
  congr 2
  apply propext
  simp only [ne_eq, Prod.mk.injEq, show Nat.fromBitsLE [] = 0 from rfl]

/-- Interior liveness always emits one Boolean flag. -/
@[simp] theorem routingLiveInteriorFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : (routingLiveInteriorFlag ruler P S owner x y).length = 1 := by
  rw [routingLiveInteriorFlag_value]
  rfl

/-- Interior liveness is uniform in seeded pointer queries and all raw word producers. -/
theorem routingLiveInteriorFlagUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool)
    {ruler seed owner x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (ho : owner ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingLiveInteriorFlag (ruler z) (P (seed z))
      (S (seed z)) (owner z) (x z) (y z)) ∈ FP := by
  have hnext := routingQueryBitsUniformFn_mem_FP S hr hs ho hS
  have hzero := routingEQFlagFn_mem_FP hx (constFn_mem_FP [])
  have hsource := andBitFn_mem_FP hzero
    (routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP ho))
  have htarget := andBitFn_mem_FP hzero
    (routingEQFlagFn_mem_FP hy (routingSixBitsFn_mem_FP hnext))
  exact andBitFn_mem_FP (routingActiveEdgeFlagUniformFn_mem_FP P S hr hs ho hP hS)
    (andBitFn_mem_FP (routingOnWireFlagFn_mem_FP hr ho hnext hx hy)
      (andBitFn_mem_FP (notBitFn_mem_FP hsource) (notBitFn_mem_FP htarget)))

end GameTheory.Complexity.Backend
