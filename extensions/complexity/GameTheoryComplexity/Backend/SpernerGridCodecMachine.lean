module

public import GameTheoryComplexity.Backend.SpernerGridCodec
public import GameTheoryComplexity.Backend.EndOfLineMachineOps

@[expose] public section

/-! Polynomial-time word operations for grid node codecs. Widths are supplied
by word rulers; fields are extracted from existing bits, and a one-bit control
accepts exactly the canonical source or a correctly sized triangle word. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime

/-- The all-zero source word for a coordinate-width ruler. -/
def gridWidthWord (ruler : List Bool) : List Bool :=
  List.replicate (gridNodeWidth ruler.length) false

/-- The first coordinate's little-endian bits. -/
def gridNodeXBits (ruler word : List Bool) : List Bool := word.tail.tail.take ruler.length

/-- The second coordinate's little-endian bits. -/
def gridNodeYBits (ruler word : List Bool) : List Bool := word.tail.tail.drop ruler.length

/-- The orientation bit, padded with false when absent. -/
def gridNodeHalfFlag (word : List Bool) : List Bool := [word.tail.headD false]

/-- Accept the exact-width triangle tag or the canonical all-zero source. -/
def gridNodeAcceptFlag (ruler word : List Bool) : List Bool :=
  [decide (word.length = gridNodeWidth ruler.length) &&
    (word.headD false || decide (word = gridWidthWord ruler))]

/-- The acceptance control agrees exactly with successful node decoding. -/
theorem gridNodeAcceptFlag_accept (ruler word : List Bool) :
    gridNodeAcceptFlag ruler word = [true] ↔
      ∃ node, decodeGridNode ruler.length word = some node := by
  simp only [gridNodeAcceptFlag, List.cons.injEq, and_true]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, gridWidthWord]
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
        exact ⟨fun _ => ⟨_, rfl⟩, fun _ => decide_eq_true hz⟩
      · rw [ite_eq_right hz]
        simp [hz]
  · simp [decodeGridNode, hw]

/-- The unary width computation charges all ruler bits. -/
@[fun_prop] theorem gridWidthWord_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun a => gridWidthWord (ruler a)) enc encBits :=
  (bitsReplicate false).comp
    (unary_add' (unary_mul' (const 2) (length_bits.comp hr)) (const 2))

/-- Coordinate extraction is bounded by the unary ruler length. -/
@[fun_prop] theorem gridNodeXBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => gridNodeXBits (ruler a) (word a)) enc encBits :=
  (bitsTail.comp (bitsTail.comp hw)).bitsTakeWithInput (length_bits.comp hr)

@[fun_prop] theorem gridNodeYBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => gridNodeYBits (ruler a) (word a)) enc encBits :=
  (bitsTail.comp (bitsTail.comp hw)).bitsDropWithInput (length_bits.comp hr)

/-- Orientation lookup retains the false default on truncated words. -/
@[fun_prop] theorem gridNodeHalfFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {word : α → List Bool}
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => gridNodeHalfFlag (word a)) enc encBits :=
  bitsCons ((ComputableInPolyTime.headD false).comp (bitsTail.comp hw)) (const [])

/-- The canonical source and triangle-tag checks are actual native computations. -/
@[fun_prop] theorem gridNodeAcceptFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => gridNodeAcceptFlag (ruler a) (word a)) enc encBits := by
  have hn := unary_add' (unary_mul' (const 2) (length_bits.comp hr)) (const 2)
  have hwidth := decide_eq' (length_bits.comp hw) hn
  have hhead : ComputableInPolyTime (fun a => (word a).headD false) enc encBool :=
    (ComputableInPolyTime.headD (encA := encBool) false).comp hw
  have hsource := decide_eq' hw (gridWidthWord_polyTime hr)
  exact bitsCons (bool_and' hwidth (bool_or.comp (hhead.prod hsource))) (const [])

end GameTheory.Complexity.Backend
