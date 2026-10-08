import GameTheoryComplexity.Backend.GridRoutingGuards

/-! Original binary pointer queries are normalized only on bounded vertex labels.
Outside labels retain their full value and word; local edge guards use the canonical
mutually consistent edge predicate. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.GridWire GameTheory.Math.EndOfLine

/-- Extend a normalized binary pointer to naturals by identity outside its vertex set. -/
def routingOriginalPointer (ruler : List Bool) (query : List Bool → List Bool) (i : ℕ) : ℕ :=
  if i < 2 ^ ruler.length then
    Nat.fromBitsLE (routingPadBits ruler (query (Nat.toBitsLE ruler.length i)))
  else i

/-- Query bounded labels at their canonical width, retaining every rejected raw word. -/
def routingQueryBits (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) : List Bool :=
  caseBit₀ (routingLTFlag raw (routingVertexBoundBits ruler))
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
    (raw : List Bool) (h : Nat.fromBitsLE raw < 2 ^ ruler.length) :
    routingQueryBits ruler query raw = routingPadBits ruler (query (routingPadBits ruler raw)) := by
  simp [routingQueryBits, routingLTFlag_value, routingVertexBoundBits_value, h, caseBit₀]

/-- Rejected labels retain their complete raw word, including its padding and width. -/
theorem routingQueryBits_of_ge (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : 2 ^ ruler.length ≤ Nat.fromBitsLE raw) :
    routingQueryBits ruler query raw = raw := by
  simp [routingQueryBits, routingLTFlag_value, routingVertexBoundBits_value,
    Nat.not_lt.mpr h, caseBit₀]

/-- The word-level query agrees with the total natural extension on every raw input. -/
theorem routingQueryBits_value (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) :
    Nat.fromBitsLE (routingQueryBits ruler query raw) =
      routingOriginalPointer ruler query (Nat.fromBitsLE raw) := by
  by_cases h : Nat.fromBitsLE raw < 2 ^ ruler.length
  · rw [routingQueryBits_of_lt ruler query raw h, routingPadBits_eq_toBitsLE ruler raw]
    simp only [routingOriginalPointer, ite_eq_left h]
  · rw [routingQueryBits_of_ge ruler query raw (Nat.le_of_not_gt h),
      routingOriginalPointer_of_ge ruler query (Nat.le_of_not_gt h)]

/-- Every accepted query result has exactly the original vertex width. -/
theorem routingQueryBits_length_of_lt (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : Nat.fromBitsLE raw < 2 ^ ruler.length) :
    (routingQueryBits ruler query raw).length = ruler.length := by
  rw [routingQueryBits_of_lt ruler query raw h]
  exact routingPadBits_length _ _

/-- Every accepted query result is the canonical encoding of the natural pointer value. -/
theorem routingQueryBits_eq_bits_of_lt (ruler : List Bool) (query : List Bool → List Bool)
    (raw : List Bool) (h : Nat.fromBitsLE raw < 2 ^ ruler.length) :
    routingQueryBits ruler query raw =
      Nat.toBitsLE ruler.length (routingOriginalPointer ruler query (Nat.fromBitsLE raw)) := by
  have he := Nat.toBitsLE_fromBitsLE (routingQueryBits ruler query raw)
  rw [routingQueryBits_length_of_lt ruler query raw h, routingQueryBits_value] at he
  exact he.symm

private theorem seededQueryFn_mem_FP (query : List Bool → List Bool → List Bool)
    {seed vertex : List Bool → List Bool} (hs : seed ∈ FP) (hv : vertex ∈ FP)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => query (seed z) (vertex z)) ∈ FP := by
  have h := mem_FP_comp (pairFn_mem_FP hs hv) hq
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using h

/-- Seeded binary queries compose polynomial-time seed, ruler and raw-label producers. -/
theorem routingQueryBitsUniformFn_mem_FP (query : List Bool → List Bool → List Bool)
    {ruler seed raw : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : raw ∈ FP)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingQueryBits (ruler z) (query (seed z)) (raw z)) ∈ FP := by
  have hguard := routingLTFlagFn_mem_FP hw (routingVertexBoundBitsFn_mem_FP hr)
  have hin := routingPadBitsFn_mem_FP hr hw
  have hout := routingPadBitsFn_mem_FP hr (seededQueryFn_mem_FP query hs hin hq)
  exact CobhamFP_subset_FP
    (Cobham.iteFn (FP_subset_CobhamFP hguard) (FP_subset_CobhamFP hout) (FP_subset_CobhamFP hw))

/-- A fixed polynomial-time query composes arbitrary ruler and raw-label producers. -/
theorem routingQueryBitsFn_mem_FP (query : List Bool → List Bool)
    {ruler raw : List Bool → List Bool} (hr : ruler ∈ FP) (hw : raw ∈ FP) (hq : query ∈ FP) :
    (fun z => routingQueryBits (ruler z) query (raw z)) ∈ FP :=
  routingQueryBitsUniformFn_mem_FP (fun _ => query) hr (constFn_mem_FP []) hw
    (mem_FP_comp pairSnd_mem_FP hq)

/-- Test a bounded, nontrivial outgoing edge whose predecessor query returns its source. -/
def routingActiveEdgeFlag (ruler : List Bool) (Pquery Squery : List Bool → List Bool)
    (raw : List Bool) : List Bool :=
  let next := routingQueryBits ruler Squery raw
  andBit (routingLTFlag raw (routingVertexBoundBits ruler))
    (andBit (routingLTFlag next (routingVertexBoundBits ruler))
      (andBit (notBit (routingEQFlag next raw))
        (routingEQFlag (routingQueryBits ruler Pquery next) raw)))

/-- The binary active-edge test is exactly the canonical routed edge predicate. -/
theorem routingActiveEdgeFlag_value (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    routingActiveEdgeFlag ruler Pquery Squery raw = [decide
      (activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler Pquery)
        (routingOriginalPointer ruler Squery) (Nat.fromBitsLE raw))] := by
  simp only [routingActiveEdgeFlag, routingLTFlag_value, routingVertexBoundBits_value,
    routingEQFlag_value, routingQueryBits_value, activeEdge, HasSuccessor]
  by_cases hr : Nat.fromBitsLE raw < 2 ^ ruler.length <;>
    by_cases hn : routingOriginalPointer ruler Squery (Nat.fromBitsLE raw) <
      2 ^ ruler.length <;>
    by_cases he : routingOriginalPointer ruler Squery (Nat.fromBitsLE raw) =
      Nat.fromBitsLE raw <;>
    by_cases hp : routingOriginalPointer ruler Pquery
      (routingOriginalPointer ruler Squery (Nat.fromBitsLE raw)) = Nat.fromBitsLE raw <;>
    simp [hr, hn, he, hp, andBit, notBit, caseBit₀]

/-- The active-edge flag accepts exactly a bounded mutually consistent original edge. -/
theorem routingActiveEdgeFlag_accept (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    routingActiveEdgeFlag ruler Pquery Squery raw = [true] ↔
      activeEdge (2 ^ ruler.length) (routingOriginalPointer ruler Pquery)
        (routingOriginalPointer ruler Squery) (Nat.fromBitsLE raw) := by
  rw [routingActiveEdgeFlag_value]
  simp

/-- The active-edge test always emits one Boolean flag. -/
@[simp] theorem routingActiveEdgeFlag_length (ruler : List Bool)
    (Pquery Squery : List Bool → List Bool) (raw : List Bool) :
    (routingActiveEdgeFlag ruler Pquery Squery raw).length = 1 := by
  rw [routingActiveEdgeFlag_value]
  rfl

/-- Active-edge testing is uniform in the seed of both polynomial-time pointer queries. -/
theorem routingActiveEdgeFlagUniformFn_mem_FP
    (Pquery Squery : List Bool → List Bool → List Bool)
    {ruler seed raw : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : raw ∈ FP)
    (hP : (fun z => Pquery (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => Squery (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingActiveEdgeFlag (ruler z) (Pquery (seed z))
      (Squery (seed z)) (raw z)) ∈ FP := by
  have hbound := routingVertexBoundBitsFn_mem_FP hr
  have hnext := routingQueryBitsUniformFn_mem_FP Squery hr hs hw hS
  have hprev := routingQueryBitsUniformFn_mem_FP Pquery hr hs hnext hP
  apply CobhamFP_subset_FP
  exact Cobham.andFn (FP_subset_CobhamFP (routingLTFlagFn_mem_FP hw hbound))
    (Cobham.andFn (FP_subset_CobhamFP (routingLTFlagFn_mem_FP hnext hbound))
      (Cobham.andFn (Cobham.notFn (FP_subset_CobhamFP (routingEQFlagFn_mem_FP hnext hw)))
        (FP_subset_CobhamFP (routingEQFlagFn_mem_FP hprev hw))))

/-- Fixed polynomial-time pointers support uniformly polynomial-time active-edge tests. -/
theorem routingActiveEdgeFlagFn_mem_FP (Pquery Squery : List Bool → List Bool)
    {ruler raw : List Bool → List Bool} (hr : ruler ∈ FP) (hw : raw ∈ FP)
    (hP : Pquery ∈ FP) (hS : Squery ∈ FP) :
    (fun z => routingActiveEdgeFlag (ruler z) Pquery Squery (raw z)) ∈ FP :=
  routingActiveEdgeFlagUniformFn_mem_FP (fun _ => Pquery) (fun _ => Squery)
    hr (constFn_mem_FP []) hw (mem_FP_comp pairSnd_mem_FP hP) (mem_FP_comp pairSnd_mem_FP hS)

end GameTheory.Complexity.Backend
