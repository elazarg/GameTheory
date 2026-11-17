module

public import GameTheoryComplexity.Backend.GridRoutingGuards

@[expose] public section

/-! Original binary pointer queries are normalized only on bounded vertex labels.
Outside labels retain their full value and word; local edge guards use the canonical
mutually consistent edge predicate. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.GridWire GameTheory.Math.EndOfLine

/-- Extend a normalized binary pointer to naturals by identity outside its vertex set. -/
def routingOriginalPointer (ruler : List Bool) (query : List Bool → List Bool) (i : ℕ) : ℕ :=
  if i < 2 ^ ruler.length then
    lsbValue (routingPadBits ruler (query (lowBits ruler.length i)))
  else i

/-- Query bounded labels at their canonical width, retaining every rejected raw word. -/
def routingQueryBits (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) : List Bool :=
  select (routingLTFlag raw (routingVertexBoundBits ruler))
    (routingPadBits ruler (query (routingPadBits ruler raw))) raw

/-- The total natural extension preserves the bounded original vertex set. -/
theorem routingOriginalPointer_lt (ruler : List Bool) (query : List Bool → List Bool)
    {i : ℕ} (hi : i < 2 ^ ruler.length) :
    routingOriginalPointer ruler query i < 2 ^ ruler.length := by
  simp only [routingOriginalPointer, ite_eq_left hi, routingPadBits_value]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Outside the original vertex set the natural pointer is the identity. -/
theorem routingOriginalPointer_of_ge (ruler : List Bool) (query : List Bool → List Bool)
    {i : ℕ} (hi : 2 ^ ruler.length ≤ i) : routingOriginalPointer ruler query i = i := by
  simp [routingOriginalPointer, Nat.not_lt.mpr hi]

/-- Accepted raw labels query the padded binary input and normalize the output width. -/
theorem routingQueryBits_of_lt (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : lsbValue raw < 2 ^ ruler.length) :
    routingQueryBits ruler query raw = routingPadBits ruler (query (routingPadBits ruler raw)) := by
  simp [routingQueryBits, routingLTFlag_value, routingVertexBoundBits_value, h, select]

/-- Rejected labels retain their complete raw word, including its padding and width. -/
theorem routingQueryBits_of_ge (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : 2 ^ ruler.length ≤ lsbValue raw) :
    routingQueryBits ruler query raw = raw := by
  simp [routingQueryBits, routingLTFlag_value, routingVertexBoundBits_value,
    Nat.not_lt.mpr h, select]

/-- The word-level query agrees with the total natural extension on every raw input. -/
theorem routingQueryBits_value (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) :
    lsbValue (routingQueryBits ruler query raw) =
      routingOriginalPointer ruler query (lsbValue raw) := by
  by_cases h : lsbValue raw < 2 ^ ruler.length
  · rw [routingQueryBits_of_lt ruler query raw h, routingPadBits_eq_lowBits ruler raw]
    simp only [routingOriginalPointer, ite_eq_left h]
  · rw [routingQueryBits_of_ge ruler query raw (Nat.le_of_not_gt h),
      routingOriginalPointer_of_ge ruler query (Nat.le_of_not_gt h)]

/-- Every accepted query result has exactly the original vertex width. -/
theorem routingQueryBits_length_of_lt (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : lsbValue raw < 2 ^ ruler.length) :
    (routingQueryBits ruler query raw).length = ruler.length := by
  rw [routingQueryBits_of_lt ruler query raw h]
  exact routingPadBits_length _ _

/-- Every accepted query result is the canonical encoding of the natural pointer value. -/
theorem routingQueryBits_eq_bits_of_lt (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : lsbValue raw < 2 ^ ruler.length) :
    routingQueryBits ruler query raw =
      lowBits ruler.length (routingOriginalPointer ruler query (lsbValue raw)) := by
  have he := lowBits_lsbValue (routingQueryBits ruler query raw)
  rw [routingQueryBits_length_of_lt ruler query raw h, routingQueryBits_value] at he
  exact he.symm

/-- Seeded queries charge native seed, ruler and raw-label producers. -/
@[fun_prop] theorem routingQueryBitsUniform_polyTime
    (query : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed raw : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (hw : ComputableInPolyTime raw enc encBits)
    (hq : ComputableInPolyTime (fun p : List Bool × List Bool => query p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingQueryBits (ruler z) (query (seed z)) (raw z))
      enc encBits := by
  have hguard := routingLTFlag_polyTime hw (routingVertexBoundBits_polyTime hr)
  have hin := routingPadBits_polyTime hr hw
  have hout := routingPadBits_polyTime hr (hq.comp (hs.prod hin))
  exact select_polyTime.comp (hguard.prod (hout.prod hw))

/-- Fixed native queries compose with arbitrary ruler and raw-label producers. -/
@[fun_prop] theorem routingQueryBits_polyTime (query : List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler raw : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime raw enc encBits)
    (hq : ComputableInPolyTime query encBits encBits) :
    ComputableInPolyTime (fun z => routingQueryBits (ruler z) query (raw z)) enc encBits :=
  routingQueryBitsUniform_polyTime (fun _ => query) hr (const []) hw
    (hq.comp (snd encBits encBits))

/-- Test a bounded, nontrivial outgoing edge whose predecessor query returns its source. -/
def routingActiveEdgeFlag (ruler : List Bool) (Pquery Squery : List Bool → List Bool)
    (raw : List Bool) : List Bool :=
  let next := routingQueryBits ruler Squery raw
  andFlag (routingLTFlag raw (routingVertexBoundBits ruler))
    (andFlag (routingLTFlag next (routingVertexBoundBits ruler))
      (andFlag (notFlag (routingEQFlag next raw))
        (routingEQFlag (routingQueryBits ruler Pquery next) raw)))

/-- The binary active-edge test is exactly the canonical routed edge predicate. -/
theorem routingActiveEdgeFlag_value (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    routingActiveEdgeFlag ruler Pquery Squery raw = [decide
      (activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler Pquery)
        (routingOriginalPointer ruler Squery) (lsbValue raw))] := by
  simp only [routingActiveEdgeFlag, routingLTFlag_value, routingVertexBoundBits_value,
    routingEQFlag_value, routingQueryBits_value, activeEdge, HasSuccessor]
  by_cases hr : lsbValue raw < 2 ^ ruler.length <;>
    by_cases hn : routingOriginalPointer ruler Squery (lsbValue raw) <
      2 ^ ruler.length <;>
    by_cases he : routingOriginalPointer ruler Squery (lsbValue raw) =
      lsbValue raw <;>
    by_cases hp : routingOriginalPointer ruler Pquery
      (routingOriginalPointer ruler Squery (lsbValue raw)) = lsbValue raw <;>
    simp [hr, hn, he, hp, andFlag, notFlag]

/-- The active-edge flag accepts exactly a bounded mutually consistent original edge. -/
theorem routingActiveEdgeFlag_accept (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    routingActiveEdgeFlag ruler Pquery Squery raw = [true] ↔
      activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler Pquery)
        (routingOriginalPointer ruler Squery) (lsbValue raw) := by
  rw [routingActiveEdgeFlag_value]
  simp

/-- The active-edge test always emits one Boolean flag. -/
@[simp] theorem routingActiveEdgeFlag_length (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    (routingActiveEdgeFlag ruler Pquery Squery raw).length = 1 := by
  rw [routingActiveEdgeFlag_value]
  rfl

/-- Active-edge testing charges both native seeded pointer computations. -/
@[fun_prop] theorem routingActiveEdgeFlagUniform_polyTime
    (Pquery Squery : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed raw : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hs : ComputableInPolyTime seed enc encBits)
    (hw : ComputableInPolyTime raw enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => Pquery p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => Squery p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingActiveEdgeFlag (ruler z) (Pquery (seed z))
      (Squery (seed z)) (raw z)) enc encBits := by
  have hbound := routingVertexBoundBits_polyTime hr
  have hnext := routingQueryBitsUniform_polyTime Squery hr hs hw hS
  have hprev := routingQueryBitsUniform_polyTime Pquery hr hs hnext hP
  exact andFlag_polyTime.comp ((routingLTFlag_polyTime hw hbound).prod
    (andFlag_polyTime.comp ((routingLTFlag_polyTime hnext hbound).prod
      (andFlag_polyTime.comp ((notFlag_polyTime.comp (routingEQFlag_polyTime hnext hw)).prod
        (routingEQFlag_polyTime hprev hw))))))

/-- Fixed native pointers support uniform active-edge testing. -/
@[fun_prop] theorem routingActiveEdgeFlag_polyTime (Pquery Squery : List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler raw : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime raw enc encBits)
    (hP : ComputableInPolyTime Pquery encBits encBits)
    (hS : ComputableInPolyTime Squery encBits encBits) :
    ComputableInPolyTime (fun z => routingActiveEdgeFlag (ruler z) Pquery Squery (raw z))
      enc encBits :=
  routingActiveEdgeFlagUniform_polyTime (fun _ => Pquery) (fun _ => Squery)
    hr (const []) hw (hP.comp (snd encBits encBits)) (hS.comp (snd encBits encBits))

end GameTheory.Complexity.Backend
