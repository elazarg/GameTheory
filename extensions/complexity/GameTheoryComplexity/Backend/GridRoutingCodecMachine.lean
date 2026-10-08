import GameTheoryComplexity.Backend.GridRoutingCodec
import GameTheoryComplexity.Backend.EndOfLineMachineOps
import Complexitylib.Classes.P.Cobham.Internal.Extract

/-! Polynomial-time routing codec operations use word rulers for both coordinate
blocks. Extraction preserves the existing bits; acceptance checks only the exact
word length, since every correctly sized word denotes a point. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps

/-- An all-zero ruler for one routing coordinate block. -/
def routingCoordinateRuler (ruler : List Bool) : List Bool :=
  List.replicate (routingCoordinateWidth ruler.length) false

/-- The all-zero word representing the routing grid origin. -/
def routingPointZeroWord (ruler : List Bool) : List Bool :=
  List.replicate (routingPointWidth ruler.length) false

/-- Extract the first coordinate's little-endian block. -/
def routingPointXBits (ruler word : List Bool) : List Bool :=
  word.take (routingCoordinateWidth ruler.length)

/-- Extract the second coordinate's little-endian block. -/
def routingPointYBits (ruler word : List Bool) : List Bool :=
  word.drop (routingCoordinateWidth ruler.length)

/-- Accept exactly words with two full coordinate blocks. -/
def routingPointAcceptFlag (ruler word : List Bool) : List Bool :=
  eqFlag (List.replicate word.length false) (routingPointZeroWord ruler)

/-- The coordinate ruler has exactly the codec's coordinate width. -/
@[simp] theorem routingCoordinateRuler_length (ruler : List Bool) :
    (routingCoordinateRuler ruler).length = routingCoordinateWidth ruler.length := by
  simp [routingCoordinateRuler]

/-- The origin word has exactly the codec's point width. -/
@[simp] theorem routingPointZeroWord_length (ruler : List Bool) :
    (routingPointZeroWord ruler).length = routingPointWidth ruler.length := by
  simp [routingPointZeroWord]

/-- The origin word agrees with the canonical point encoder. -/
theorem routingPointZeroWord_eq_encode (ruler : List Bool) :
    routingPointZeroWord ruler = encodeRoutingPoint ruler.length (0, 0) := by
  simp [routingPointZeroWord]

/-- The first field extractor returns exactly the encoded first coordinate bits. -/
theorem routingPointXBits_encode (ruler : List Bool) (point : ℕ × ℕ) :
    routingPointXBits ruler (encodeRoutingPoint ruler.length point) =
      Nat.toBitsLE (routingCoordinateWidth ruler.length) point.1 := by
  simp [routingPointXBits, encodeRoutingPoint]

/-- The second field extractor returns exactly the encoded second coordinate bits. -/
theorem routingPointYBits_encode (ruler : List Bool) (point : ℕ × ℕ) :
    routingPointYBits ruler (encodeRoutingPoint ruler.length point) =
      Nat.toBitsLE (routingCoordinateWidth ruler.length) point.2 := by
  simp [routingPointYBits, encodeRoutingPoint]

/-- The acceptance control tests exactly the advertised routing word width. -/
theorem routingPointAcceptFlag_width (ruler word : List Bool) :
    routingPointAcceptFlag ruler word = [true] ↔ word.length = routingPointWidth ruler.length := by
  simp [routingPointAcceptFlag, eqFlag_eq_true_iff, routingPointZeroWord]

/-- The acceptance control agrees exactly with successful point decoding. -/
theorem routingPointAcceptFlag_accept (ruler word : List Bool) :
    routingPointAcceptFlag ruler word = [true] ↔
      ∃ point, decodeRoutingPoint ruler.length word = some point := by
  rw [routingPointAcceptFlag_width]
  constructor
  · intro hw
    exact ⟨(Nat.fromBitsLE (word.take (routingCoordinateWidth ruler.length)),
      Nat.fromBitsLE (word.drop (routingCoordinateWidth ruler.length))),
      by simp [decodeRoutingPoint, hw]⟩
  · rintro ⟨point, hd⟩
    exact decodeRoutingPoint_length hd

/-- Constructing a coordinate ruler composes actual polynomial-time machines. -/
theorem routingCoordinateRulerFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => routingCoordinateRuler (ruler z)) ∈ FP := by
  have h := appendFn_mem_FP
    (mulLenFn_mem_FP (constFn_mem_FP [false, false]) hr)
    (constFn_mem_FP [false, false, false])
  simp only [routingCoordinateRuler, routingCoordinateWidth, List.replicate_add]
  exact h

/-- Constructing the origin word composes actual polynomial-time machines. -/
theorem routingPointZeroWordFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => routingPointZeroWord (ruler z)) ∈ FP := by
  have h := routingCoordinateRulerFn_mem_FP hr
  have hh := appendFn_mem_FP h h
  simp only [routingPointZeroWord, routingPointWidth, two_mul, List.replicate_add]
  exact hh

/-- First-coordinate extraction composes polynomial-time word producers. -/
theorem routingPointXBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => routingPointXBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  have h : (fun z => (word z).take (routingCoordinateRuler (ruler z)).length) ∈ CobhamFP :=
    takeFn (FP_subset_CobhamFP (routingCoordinateRulerFn_mem_FP hr)) (FP_subset_CobhamFP hw)
  simpa only [routingCoordinateRuler_length, routingPointXBits] using h

/-- Second-coordinate extraction composes polynomial-time word producers. -/
theorem routingPointYBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => routingPointYBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  have h : (fun z => (word z).drop (routingCoordinateRuler (ruler z)).length) ∈ CobhamFP :=
    dropFn (FP_subset_CobhamFP (routingCoordinateRulerFn_mem_FP hr)) (FP_subset_CobhamFP hw)
  simpa only [routingCoordinateRuler_length, routingPointYBits] using h

/-- Exact-width acceptance has an actual polynomial-time word-machine certificate. -/
theorem routingPointAcceptFlagFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => routingPointAcceptFlag (ruler z) (word z)) ∈ FP := by
  have hzero : (fun z => List.replicate (word z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hw
  exact eqFlagFn_mem_FP hzero (routingPointZeroWordFn_mem_FP hr)

end GameTheory.Complexity.Backend
