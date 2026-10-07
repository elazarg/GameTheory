import GameTheoryComplexity.Backend.SpernerGridCodec
import GameTheoryComplexity.Backend.EndOfLineMachineOps
import Complexitylib.Classes.P.Cobham.Internal.Extract

/-! Polynomial-time word operations for grid node codecs. Widths are supplied
by word rulers; fields are extracted from existing bits, and a one-bit control
accepts exactly the canonical source or a correctly sized triangle word. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps

/-- The all-zero source word for a coordinate-width ruler. -/
def gridWidthWord (ruler : List Bool) : List Bool :=
  List.replicate (gridNodeWidth ruler.length) false

/-- The first coordinate's little-endian bits. -/
def gridNodeXBits (ruler word : List Bool) : List Bool := word.tail.tail.take ruler.length

/-- The second coordinate's little-endian bits. -/
def gridNodeYBits (ruler word : List Bool) : List Bool := word.tail.tail.drop ruler.length

/-- The orientation bit, padded with false when absent. -/
def gridNodeHalfFlag (word : List Bool) : List Bool := bitAt [] word.tail

/-- Accept the exact-width triangle tag or the canonical all-zero source. -/
def gridNodeAcceptFlag (ruler word : List Bool) : List Bool :=
  andBit (eqFlag (List.replicate word.length false) (gridWidthWord ruler))
    (orBit (bitAt [] word) (eqFlag word (gridWidthWord ruler)))

private theorem head_flag (word : List Bool) : bitAt [] word = [true] ∨
    bitAt [] word = [false] := by
  rw [bitAt_eq]
  cases h : bitOf word 0 <;> simp

private theorem head_accept (word : List Bool) :
    bitAt [] word = [true] ↔ word.headD false = true := by
  simp [bitAt_eq, bitOf]

/-- The acceptance control agrees exactly with successful node decoding. -/
theorem gridNodeAcceptFlag_accept (ruler word : List Bool) :
    gridNodeAcceptFlag ruler word = [true] ↔
      ∃ node, decodeGridNode ruler.length word = some node := by
  rw [gridNodeAcceptFlag, andBit_eq_true_iff (eqFlag_flag _ _)
    (orBit_flag (head_flag _) (eqFlag_flag _ _)),
    orBit_eq_true_iff (head_flag _) (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, gridWidthWord, zeroWords_eq_iff, head_accept]
  by_cases hw : word.length = gridNodeWidth ruler.length
  · simp only [hw, true_and]
    rw [decodeGridNode, ite_eq_left hw]
    by_cases ht : word.headD false = true
    · rw [ite_eq_left ht]
      exact ⟨fun _ => ⟨_, rfl⟩, fun _ => Or.inl ht⟩
    · rw [ite_eq_right ht]
      simp only [ht, Bool.false_eq_true, false_or]
      by_cases hz : word = List.replicate (gridNodeWidth ruler.length) false
      · rw [ite_eq_left hz]
        exact ⟨fun _ => ⟨_, rfl⟩, fun _ => hz⟩
      · rw [ite_eq_right hz]
        simp [hz]
  · simp [decodeGridNode, hw]

/-- The width ruler produces the source word in polynomial time. -/
theorem gridWidthWordFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => gridWidthWord (ruler z)) ∈ FP := by
  have h := appendFn_mem_FP
    (mulLenFn_mem_FP (constFn_mem_FP [false, false]) hr) (constFn_mem_FP [false, false])
  simp only [gridWidthWord, gridNodeWidth, List.replicate_add]
  exact h

/-- Extracting the first coordinate composes polynomial-time word producers. -/
theorem gridNodeXBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => gridNodeXBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact takeFn (FP_subset_CobhamFP hr) (tailFn (tailFn (FP_subset_CobhamFP hw)))

/-- Extracting the second coordinate composes polynomial-time word producers. -/
theorem gridNodeYBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => gridNodeYBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact dropFn (FP_subset_CobhamFP hr) (tailFn (tailFn (FP_subset_CobhamFP hw)))

/-- Reading the orientation singleton composes polynomial-time word producers. -/
theorem gridNodeHalfFlagFn_mem_FP {word : List Bool → List Bool} (hw : word ∈ FP) :
    (fun z => gridNodeHalfFlag (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact headFlagFn (tailFn (FP_subset_CobhamFP hw))

/-- Exact node acceptance has an actual polynomial-time word-machine certificate. -/
theorem gridNodeAcceptFlagFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => gridNodeAcceptFlag (ruler z) (word z)) ∈ FP := by
  have hzero : (fun z => List.replicate (word z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hw
  have hwidth := gridWidthWordFn_mem_FP hr
  have hhead : (fun z => bitAt [] (word z)) ∈ FP :=
    CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hw))
  exact andBitFn_mem_FP (eqFlagFn_mem_FP hzero hwidth)
    (orBitFn_mem_FP hhead (eqFlagFn_mem_FP hw hwidth))

end GameTheory.Complexity.Backend
