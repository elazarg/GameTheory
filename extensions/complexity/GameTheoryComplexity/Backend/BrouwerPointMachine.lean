import GameTheoryComplexity.Backend.BrouwerPointCodec
import GameTheory.Math.GridBrouwerSixthGeometry
import GameTheoryComplexity.Backend.SpernerGridCodecMachine
import GameTheoryComplexity.Backend.GridRoutingBitFields
import GameTheoryComplexity.Backend.GridRoutingDivision
import GameTheoryComplexity.Backend.GridRoutingArithmetic

/-! Point location uses binary division by six and a constant remainder table.
Boundary coordinates are clamped to the final grid cell. The reverse decoder
emits the rational barycenter using shifts, addition, and fixed-width padding. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Numerator field ruler. -/
def brouwerPointRuler (ruler : List Bool) : List Bool := ruler ++ [false, false, false]

/-- Binary representation of the largest numerator, six times the grid size. -/
def brouwerPointBoundBits (ruler : List Bool) : List Bool :=
  routingShiftBits ruler [false, true, true]

/-- First numerator field. -/
def brouwerPointXBits (ruler word : List Bool) : List Bool :=
  word.take (brouwerPointRuler ruler).length

/-- Second numerator field. -/
def brouwerPointYBits (ruler word : List Bool) : List Bool :=
  word.drop (brouwerPointRuler ruler).length

/-- Binary remainder modulo six, using the modulo-three remainder and quotient parity. -/
def brouwerModSixBits (bits : List Bool) : List Bool :=
  let r := routingModThreeBits bits
  caseBit₀ (routingDivThreeBits bits)
    (caseBit₀ r.tail [true, false, true]
      (caseBit₀ r [false, false, true] [true, true, false]))
    (caseBit₀ r.tail [false, true, false]
      (caseBit₀ r [true, false, false] [false, false, false]))

/-- Clamp a boundary quotient to the all-one last-cell coordinate. -/
def brouwerCellBits (ruler bits : List Bool) : List Bool :=
  caseBit₀ (routingEQFlag bits (brouwerPointBoundBits ruler))
    (List.replicate ruler.length true)
    (routingPadBits ruler (routingDivSixBits bits))

/-- The final cell has residual six at the closed square's upper boundary. -/
def brouwerOffsetBits (ruler bits : List Bool) : List Bool :=
  caseBit₀ (routingEQFlag bits (brouwerPointBoundBits ruler))
    [false, true, true] (brouwerModSixBits bits)

/-- Produce the containing triangle word from the rational point word. -/
def brouwerLocateWord (ruler word : List Bool) : List Bool :=
  let x := brouwerPointXBits ruler word
  let y := brouwerPointYBits ruler word
  [true] ++ routingLTFlag (brouwerOffsetBits ruler x) (brouwerOffsetBits ruler y) ++
    brouwerCellBits ruler x ++ brouwerCellBits ruler y

/-- Source-aware point-to-triangle answer conversion. -/
def brouwerLocate (input word : List Bool) : List Bool :=
  brouwerLocateWord (pairFst input) word

/-- Numerator of one barycenter coordinate. -/
def brouwerBarycenterCoordinate (ruler coordinate offset : List Bool) : List Bool :=
  routingPadBits (brouwerPointRuler ruler) (routingAddBits (routingSixBits coordinate) offset)

/-- Decode a triangle to its rational barycenter point word. -/
def brouwerBarycenterWord (ruler word : List Bool) : List Bool :=
  brouwerBarycenterCoordinate ruler (gridNodeXBits ruler word)
      (caseBit₀ (gridNodeHalfFlag word) [false, true] [false, false, true]) ++
    brouwerBarycenterCoordinate ruler (gridNodeYBits ruler word)
      (caseBit₀ (gridNodeHalfFlag word) [false, false, true] [false, true])

/-- Source-aware triangle-to-point answer conversion. -/
def brouwerBarycenter (input word : List Bool) : List Bool :=
  brouwerBarycenterWord (pairFst input) word

@[simp] theorem brouwerPointRuler_length (ruler : List Bool) :
    (brouwerPointRuler ruler).length = pointCoordinateWidth ruler.length := by
  simp [brouwerPointRuler, pointCoordinateWidth]

theorem brouwerPointBoundBits_value (ruler : List Bool) :
    Nat.fromBitsLE (brouwerPointBoundBits ruler) = 6 * 2 ^ ruler.length := by
  rw [brouwerPointBoundBits, routingShiftBits_value]
  simp [Nat.fromBitsLE, Nat.fromBits, Nat.mul_comm]

@[simp] theorem brouwerModSixBits_length (bits : List Bool) :
    (brouwerModSixBits bits).length = 3 := by
  have hl (q x y : List Bool) (hx : x.length = 3) (hy : y.length = 3) :
      (caseBit₀ q x y).length = 3 := by
    cases q with
    | nil => exact hy
    | cons b q => cases b <;> assumption
  unfold brouwerModSixBits
  apply hl <;> apply hl <;> first | rfl | apply hl <;> rfl

private theorem fromBitsLE_head_tail (bits : List Bool) :
    Nat.fromBitsLE bits = 2 * Nat.fromBitsLE bits.tail +
      if bits.headD false then 1 else 0 := by
  cases bits with
  | nil => rfl
  | cons b bits =>
    simp only [Nat.fromBitsLE_cons, List.tail_cons, List.headD_cons]
    exact Nat.add_comm _ _

private theorem caseBit_head (bits x y : List Bool) :
    caseBit₀ bits x y = if bits.headD false then x else y := by
  cases bits with
  | nil => rfl
  | cons b bits => cases b <;> rfl

private theorem fromBitsLE_head_mod (bits : List Bool) :
    Nat.fromBitsLE bits % 2 = if bits.headD false then 1 else 0 := by
  rw [fromBitsLE_head_tail]
  cases bits.headD false <;> simp

theorem brouwerModSixBits_value (bits : List Bool) :
    Nat.fromBitsLE (brouwerModSixBits bits) = Nat.fromBitsLE bits % 6 := by
  have hr : routingModThreeBits bits = Nat.toBitsLE 2 (Nat.fromBitsLE bits % 3) := by
    have h := Nat.toBitsLE_fromBitsLE (routingModThreeBits bits)
    rw [routingModThreeBits_length, routingModThreeBits_value] at h
    exact h.symm
  have hq := fromBitsLE_head_mod (routingDivThreeBits bits)
  rw [routingDivThreeBits_value] at hq
  have he : Nat.fromBitsLE bits % 6 = Nat.fromBitsLE bits % 3 +
      3 * ((Nat.fromBitsLE bits / 3) % 2) := by
    rw [show 6 = 3 * 2 by decide, Nat.mod_mul]
  unfold brouwerModSixBits
  rw [hr, caseBit_head]
  have hrlt := Nat.mod_lt (Nat.fromBitsLE bits) (by decide : 0 < 3)
  rw [he, hq]
  generalize hk : Nat.fromBitsLE bits % 3 = k at hrlt ⊢
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl <;>
    cases hb : (routingDivThreeBits bits).headD false <;>
    norm_num [Nat.toBitsLE, Nat.toBits, caseBit₀, Nat.fromBitsLE, Nat.fromBits]

private theorem fromBitsLE_ones (b : ℕ) :
    Nat.fromBitsLE (List.replicate b true) = 2 ^ b - 1 := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hp : 0 < 2 ^ b := by positivity
    simp only [List.replicate_succ, Nat.fromBitsLE_cons, ite_true, ih, pow_succ]
    omega

@[simp] theorem brouwerCellBits_length (ruler bits : List Bool) :
    (brouwerCellBits ruler bits).length = ruler.length := by
  rw [brouwerCellBits, routingEQFlag_value]
  by_cases h : Nat.fromBitsLE bits = Nat.fromBitsLE (brouwerPointBoundBits ruler) <;>
    simp [h, caseBit₀]

@[simp] theorem brouwerOffsetBits_length (ruler bits : List Bool) :
    (brouwerOffsetBits ruler bits).length = 3 := by
  rw [brouwerOffsetBits, routingEQFlag_value]
  by_cases h : Nat.fromBitsLE bits = Nat.fromBitsLE (brouwerPointBoundBits ruler) <;>
    simp [h, caseBit₀]

theorem brouwerCellBits_value (ruler bits : List Bool)
    (h : Nat.fromBitsLE bits ≤ 6 * 2 ^ ruler.length) :
    Nat.fromBitsLE (brouwerCellBits ruler bits) =
      sixthCellIndex (2 ^ ruler.length) (Nat.fromBitsLE bits) := by
  rw [brouwerCellBits, routingEQFlag_value, brouwerPointBoundBits_value]
  have hp : 0 < 2 ^ ruler.length := by positivity
  by_cases he : Nat.fromBitsLE bits = 6 * 2 ^ ruler.length
  · simp [he, caseBit₀, fromBitsLE_ones, sixthCellIndex]
  · have hq : Nat.fromBitsLE bits / 6 < 2 ^ ruler.length := by omega
    simp only [he, decide_false, caseBit₀, Bool.cond_false]
    rw [routingPadBits_value, routingDivSixBits_value, Nat.mod_eq_of_lt hq]
    exact (Nat.min_eq_left (by omega)).symm

theorem brouwerOffsetBits_value (ruler bits : List Bool)
    (h : Nat.fromBitsLE bits ≤ 6 * 2 ^ ruler.length) :
    Nat.fromBitsLE (brouwerOffsetBits ruler bits) =
      sixthOffset (2 ^ ruler.length) (Nat.fromBitsLE bits) := by
  rw [brouwerOffsetBits, routingEQFlag_value, brouwerPointBoundBits_value]
  have hp : 0 < 2 ^ ruler.length := by positivity
  by_cases he : Nat.fromBitsLE bits = 6 * 2 ^ ruler.length
  · simp only [he, decide_true, caseBit₀, Bool.cond_true]
    have hb : sixthCellIndex (2 ^ ruler.length) (6 * 2 ^ ruler.length) =
        2 ^ ruler.length - 1 := by simp [sixthCellIndex]
    unfold sixthOffset
    rw [hb]
    norm_num [Nat.fromBitsLE_cons, Nat.fromBitsLE, Nat.fromBits]
    omega
  · have hq : Nat.fromBitsLE bits / 6 ≤ 2 ^ ruler.length - 1 := by omega
    simp only [he, decide_false, caseBit₀, Bool.cond_false]
    rw [brouwerModSixBits_value]
    unfold sixthOffset sixthCellIndex
    rw [Nat.min_eq_left hq]
    omega

theorem brouwerCellBits_eq (ruler bits : List Bool)
    (h : Nat.fromBitsLE bits ≤ 6 * 2 ^ ruler.length) :
    brouwerCellBits ruler bits = Nat.toBitsLE ruler.length
      (sixthCellIndex (2 ^ ruler.length) (Nat.fromBitsLE bits)) := by
  have he := Nat.toBitsLE_fromBitsLE (brouwerCellBits ruler bits)
  rw [brouwerCellBits_length, brouwerCellBits_value ruler bits h] at he
  exact he.symm

theorem brouwerOffsetBits_eq (ruler bits : List Bool)
    (h : Nat.fromBitsLE bits ≤ 6 * 2 ^ ruler.length) :
    brouwerOffsetBits ruler bits = Nat.toBitsLE 3
      (sixthOffset (2 ^ ruler.length) (Nat.fromBitsLE bits)) := by
  have he := Nat.toBitsLE_fromBitsLE (brouwerOffsetBits ruler bits)
  rw [brouwerOffsetBits_length, brouwerOffsetBits_value ruler bits h] at he
  exact he.symm

theorem brouwerLocateWord_eq {ruler word : List Bool} {p : ℕ × ℕ}
    (h : decodeBrouwerPoint ruler.length word = some p) :
    brouwerLocateWord ruler word =
      encodeGridNode ruler.length (some (sixthTriangle (2 ^ ruler.length) p.1 p.2)) := by
  obtain ⟨_, hx, hy, hvx, hvy⟩ := decodeBrouwerPoint_properties h
  have hxx : Nat.fromBitsLE (brouwerPointXBits ruler word) = p.1 := by
    simpa only [brouwerPointXBits, brouwerPointRuler_length] using hvx
  have hyy : Nat.fromBitsLE (brouwerPointYBits ruler word) = p.2 := by
    simpa only [brouwerPointYBits, brouwerPointRuler_length] using hvy
  unfold brouwerLocateWord
  dsimp only
  rw [routingLTFlag_value, brouwerOffsetBits_value _ _ (by simpa [hxx] using hx),
    brouwerOffsetBits_value _ _ (by simpa [hyy] using hy),
    brouwerCellBits_eq _ _ (by simpa [hxx] using hx),
    brouwerCellBits_eq _ _ (by simpa [hyy] using hy), hxx, hyy]
  rfl

/-- Integer numerators of a triangle's barycenter at sixth-grid resolution. -/
abbrev brouwerBarycenterNumerators (t : GridTriangle) : ℕ × ℕ := sixthBarycenterNumerators t

theorem brouwerBarycenterNumerators_bounds {b : ℕ} {t : GridTriangle}
    (h : ValidTriangle (2 ^ b) t) :
    (brouwerBarycenterNumerators t).1 ≤ 6 * 2 ^ b ∧
      (brouwerBarycenterNumerators t).2 ≤ 6 * 2 ^ b := by
  exact sixthBarycenterNumerators_bounds h

theorem brouwerBarycenterCoordinate_eq (ruler coordinate offset : List Bool) :
    brouwerBarycenterCoordinate ruler coordinate offset =
      Nat.toBitsLE (pointCoordinateWidth ruler.length)
        (6 * Nat.fromBitsLE coordinate + Nat.fromBitsLE offset) := by
  rw [brouwerBarycenterCoordinate, routingPadBits_eq_toBitsLE,
    brouwerPointRuler_length, routingAddBits_value, routingSixBits_value]

theorem brouwerBarycenterWord_eq {ruler word : List Bool} {t : GridTriangle}
    (h : decodeGridNode ruler.length word = some (some t)) :
    brouwerBarycenterWord ruler word =
      encodeBrouwerPoint ruler.length (brouwerBarycenterNumerators t) := by
  have hv := decodeGridNode_valid h t rfl
  rw [← encodeGridNode_decode h]
  unfold brouwerBarycenterWord
  rw [brouwerBarycenterCoordinate_eq, brouwerBarycenterCoordinate_eq]
  have hx : Nat.fromBitsLE (gridNodeXBits ruler (encodeGridNode ruler.length (some t))) = t.x := by
    simp [gridNodeXBits, encodeGridNode, Nat.fromBitsLE_toBitsLE hv.1]
  have hy : Nat.fromBitsLE (gridNodeYBits ruler (encodeGridNode ruler.length (some t))) = t.y := by
    simp [gridNodeYBits, encodeGridNode, Nat.fromBitsLE_toBitsLE hv.2]
  rw [hx, hy]
  cases ht : t.upper <;>
    simp [encodeBrouwerPoint, brouwerBarycenterNumerators, sixthBarycenterNumerators, gridNodeHalfFlag,
      encodeGridNode, bitAt, caseBit₀, ht, Nat.fromBitsLE, Nat.fromBits]

theorem brouwerPointRulerFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => brouwerPointRuler (ruler z)) ∈ FP :=
  appendFn_mem_FP hr (constFn_mem_FP _)

theorem brouwerPointBoundBitsFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => brouwerPointBoundBits (ruler z)) ∈ FP :=
  routingShiftBitsFn_mem_FP hr (constFn_mem_FP _)

theorem brouwerPointXBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => brouwerPointXBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.takeFn (FP_subset_CobhamFP (brouwerPointRulerFn_mem_FP hr))
    (FP_subset_CobhamFP hw)

theorem brouwerPointYBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => brouwerPointYBits (ruler z) (word z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.dropFn (FP_subset_CobhamFP (brouwerPointRulerFn_mem_FP hr))
    (FP_subset_CobhamFP hw)

theorem brouwerModSixBits_mem_FP : brouwerModSixBits ∈ FP := by
  apply CobhamFP_subset_FP
  have hr := FP_subset_CobhamFP routingModThreeBits_mem_FP
  have hq := FP_subset_CobhamFP routingDivThreeBits_mem_FP
  exact Cobham.iteFn hq
    (Cobham.iteFn (Cobham.tailFn hr) (Cobham.const _)
      (Cobham.iteFn hr (Cobham.const _) (Cobham.const _)))
    (Cobham.iteFn (Cobham.tailFn hr) (Cobham.const _)
      (Cobham.iteFn hr (Cobham.const _) (Cobham.const _)))

theorem brouwerCellBitsFn_mem_FP {ruler bits : List Bool → List Bool}
    (hr : ruler ∈ FP) (hb : bits ∈ FP) :
    (fun z => brouwerCellBits (ruler z) (bits z)) ∈ FP := by
  have hone : (fun z => List.replicate (ruler z).length true) ∈ FP := by
    apply CobhamFP_subset_FP
    exact (Cobham.comp₂ Cobham.smash (Cobham.const [true])
      (FP_subset_CobhamFP hr)).of_eq fun z => by simp [_root_.Complexity.smash]
  exact selectFn_mem_FP (routingEQFlagFn_mem_FP hb (brouwerPointBoundBitsFn_mem_FP hr))
    hone (routingPadBitsFn_mem_FP hr
      (mem_FP_comp (f := bits) (g := routingDivSixBits) hb routingDivSixBits_mem_FP))

theorem brouwerOffsetBitsFn_mem_FP {ruler bits : List Bool → List Bool}
    (hr : ruler ∈ FP) (hb : bits ∈ FP) :
    (fun z => brouwerOffsetBits (ruler z) (bits z)) ∈ FP :=
  selectFn_mem_FP (routingEQFlagFn_mem_FP hb (brouwerPointBoundBitsFn_mem_FP hr))
    (constFn_mem_FP _) (mem_FP_comp (f := bits) (g := brouwerModSixBits) hb brouwerModSixBits_mem_FP)

theorem brouwerLocateWordFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => brouwerLocateWord (ruler z) (word z)) ∈ FP := by
  have hx := brouwerPointXBitsFn_mem_FP hr hw
  have hy := brouwerPointYBitsFn_mem_FP hr hw
  exact appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP [true])
      (routingLTFlagFn_mem_FP (brouwerOffsetBitsFn_mem_FP hr hx)
        (brouwerOffsetBitsFn_mem_FP hr hy))) (brouwerCellBitsFn_mem_FP hr hx))
    (brouwerCellBitsFn_mem_FP hr hy)

theorem brouwerBarycenterCoordinateFn_mem_FP
    {ruler coordinate offset : List Bool → List Bool}
    (hr : ruler ∈ FP) (hc : coordinate ∈ FP) (ho : offset ∈ FP) :
    (fun z => brouwerBarycenterCoordinate (ruler z) (coordinate z) (offset z)) ∈ FP :=
  routingPadBitsFn_mem_FP (brouwerPointRulerFn_mem_FP hr)
    (routingAddBitsFn_mem_FP (routingSixBitsFn_mem_FP hc) ho)

theorem brouwerBarycenterWordFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => brouwerBarycenterWord (ruler z) (word z)) ∈ FP :=
  appendFn_mem_FP
    (brouwerBarycenterCoordinateFn_mem_FP hr (gridNodeXBitsFn_mem_FP hr hw)
      (selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw) (constFn_mem_FP _) (constFn_mem_FP _)))
    (brouwerBarycenterCoordinateFn_mem_FP hr (gridNodeYBitsFn_mem_FP hr hw)
      (selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw) (constFn_mem_FP _) (constFn_mem_FP _)))

theorem brouwerLocate_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => brouwerLocate (v 0) (v 1)) := by
  have h := brouwerLocateWordFn_mem_FP
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have hc := Cobham.comp (FP_subset_CobhamFP h)
    (fun _ => Cobham.comp₂ Cobham.pairing (.proj (0 : Fin 2)) (.proj 1))
  apply cobham_iff_FPn.mp
  exact hc.of_eq fun v => by simp [brouwerLocate]

theorem brouwerBarycenter_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => brouwerBarycenter (v 0) (v 1)) := by
  have h := brouwerBarycenterWordFn_mem_FP
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have hc := Cobham.comp (FP_subset_CobhamFP h)
    (fun _ => Cobham.comp₂ Cobham.pairing (.proj (0 : Fin 2)) (.proj 1))
  apply cobham_iff_FPn.mp
  exact hc.of_eq fun v => by simp [brouwerBarycenter]

end GameTheory.Complexity.Backend
