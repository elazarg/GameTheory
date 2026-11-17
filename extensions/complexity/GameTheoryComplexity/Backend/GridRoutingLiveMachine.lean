module

public import GameTheoryComplexity.Backend.GridRoutingGeometryMachine
public import GameTheoryComplexity.Backend.GridRoutingQueries

@[expose] public section

/-! Binary live-label tests validate bounded original vertices and active wire
interiors. Coordinates and owner fields retain their full raw numeric values. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire

/-- A vertex label is live exactly when its raw value fits the original vertex set. -/
def routingLiveVertexFlag (ruler owner : List Bool) : List Bool :=
  routingLTFlag owner (routingVertexBoundBits ruler)

/-- Validate an active wire interior and exclude its two original endpoint coordinates. -/
def routingLiveInteriorFlag (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : List Bool :=
  let next := routingQueryBits ruler S owner
  let sourceVertex := andFlag (routingEQFlag x []) (routingEQFlag y (routingSixBits owner))
  let targetVertex := andFlag (routingEQFlag x []) (routingEQFlag y (routingSixBits next))
  andFlag (routingActiveEdgeFlag ruler P S owner)
    (andFlag (routingOnWireFlag ruler owner next x y)
      (andFlag (notFlag sourceVertex) (notFlag targetVertex)))

/-- Vertex liveness agrees with the natural label predicate for arbitrary pointers. -/
theorem routingLiveVertexFlag_value (ruler owner : List Bool) (P S : ℕ → ℕ) :
    routingLiveVertexFlag ruler owner =
      [decide (liveWireNode (2 ^ ruler.length) P S (.inl (lsbValue owner)))] := by
  simp only [routingLiveVertexFlag, routingLTFlag_value, routingVertexBoundBits_value,
    liveWireNode]
  congr 2

/-- Vertex liveness always emits one Boolean flag. -/
@[simp] theorem routingLiveVertexFlag_length (ruler owner : List Bool) :
    (routingLiveVertexFlag ruler owner).length = 1 :=
  routingLTFlag_length _ _

/-- Vertex liveness charges native ruler and owner producers. -/
@[fun_prop] theorem routingLiveVertexFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler owner : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (ho : ComputableInPolyTime owner enc encBits) :
    ComputableInPolyTime (fun z => routingLiveVertexFlag (ruler z) (owner z)) enc encBits :=
  routingLTFlag_polyTime ho (routingVertexBoundBits_polyTime hr)

private theorem flagAnd_decide (a b : Prop) [Decidable a] [Decidable b] :
    andFlag [decide a] [decide b] = [decide (a ∧ b)] := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, andFlag]

private theorem flagNot_decide (a : Prop) [Decidable a] :
    notFlag [decide a] = [decide (¬a)] := by
  by_cases h : a <;> simp [h, notFlag]

/-- Interior liveness is exactly the natural predicate, including endpoint exclusion. -/
theorem routingLiveInteriorFlag_value (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : routingLiveInteriorFlag ruler P S owner x y =
      [decide (liveWireNode (2 ^ ruler.length) (routingOriginalPointer ruler P)
        (routingOriginalPointer ruler S)
        (.inr (lsbValue owner, (lsbValue x, lsbValue y))))] := by
  simp only [routingLiveInteriorFlag, routingActiveEdgeFlag_value, routingOnWireFlag_value,
    routingEQFlag_value, routingSixBits_value, routingQueryBits_value,
    flagAnd_decide, flagNot_decide, liveWireNode, vertexPoint]
  congr 2
  apply propext
  simp only [ne_eq, Prod.mk.injEq, show lsbValue [] = 0 from rfl]

/-- Interior liveness always emits one Boolean flag. -/
@[simp] theorem routingLiveInteriorFlag_length (ruler : List Bool) (P S : List Bool → List Bool)
    (owner x y : List Bool) : (routingLiveInteriorFlag ruler P S owner x y).length = 1 := by
  rw [routingLiveInteriorFlag_value]
  rfl

/-- Interior liveness charges both seeded native queries and every raw field producer. -/
@[fun_prop] theorem routingLiveInteriorFlagUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed owner x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (ho : ComputableInPolyTime owner enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingLiveInteriorFlag (ruler z) (P (seed z))
      (S (seed z)) (owner z) (x z) (y z)) enc encBits := by
  have hnext := routingQueryBitsUniform_polyTime S hr hs ho hS
  have hzero := routingEQFlag_polyTime hx (const [])
  have hsource := andFlag_polyTime.comp (hzero.prod
    (routingEQFlag_polyTime hy (routingSixBits_polyTime ho)))
  have htarget := andFlag_polyTime.comp (hzero.prod
    (routingEQFlag_polyTime hy (routingSixBits_polyTime hnext)))
  exact andFlag_polyTime.comp ((routingActiveEdgeFlagUniform_polyTime P S hr hs ho hP hS).prod
    (andFlag_polyTime.comp ((routingOnWireFlag_polyTime hr ho hnext hx hy).prod
      (andFlag_polyTime.comp ((notFlag_polyTime.comp hsource).prod
        (notFlag_polyTime.comp htarget))))))

end GameTheory.Complexity.Backend
