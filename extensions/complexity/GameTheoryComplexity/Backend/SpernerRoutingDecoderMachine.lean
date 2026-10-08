import GameTheoryComplexity.Backend.SpernerGridCodecMachine
import GameTheoryComplexity.Backend.GridRoutingBitFields
import GameTheoryComplexity.Backend.GridRoutingDivision
import GameTheoryComplexity.Backend.EndOfLineVerifier

/-! Routed endpoint triangles have vertical coordinate thirty-six times the
original label plus eight. Two binary divisions by six recover the label without
enumerating a path. Invalid source promises produce the required empty answer. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner

/-- The coordinate ruler for a square containing the translated routed graph. -/
def routingSpernerRuler (ruler : List Bool) : List Bool :=
  ruler ++ ruler ++ List.replicate 8 false

/-- The routed square uses twice the original label width plus eight bits. -/
@[simp] theorem routingSpernerRuler_length (ruler : List Bool) :
    (routingSpernerRuler ruler).length = 2 * ruler.length + 8 := by
  simp [routingSpernerRuler]; omega

/-- Constructing the larger coordinate ruler is uniformly polynomial time. -/
theorem routingSpernerRulerFn_mem_FP {ruler : List Bool → List Bool} (hr : ruler ∈ FP) :
    (fun z => routingSpernerRuler (ruler z)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP hr hr) (constFn_mem_FP (List.replicate 8 false))

/-- Decode the endpoint label from a target triangle's vertical coordinate. -/
def routingSpernerLabelBits (ruler word : List Bool) : List Bool :=
  routingPadBits ruler (routingDivSixBits
    (routingDivSixBits (gridNodeYBits (routingSpernerRuler ruler) word)))

/-- Every decoded label word has the original instance's label width. -/
@[simp] theorem routingSpernerLabelBits_length (ruler word : List Bool) :
    (routingSpernerLabelBits ruler word).length = ruler.length := by
  simp [routingSpernerLabelBits]

/-- Binary label decoding composes arbitrary polynomial-time word producers. -/
theorem routingSpernerLabelBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => routingSpernerLabelBits (ruler z) (word z)) ∈ FP := by
  have hy := gridNodeYBitsFn_mem_FP (routingSpernerRulerFn_mem_FP hr) hw
  have hq : (fun z => routingDivSixBits
      (gridNodeYBits (routingSpernerRuler (ruler z)) (word z))) ∈ FP :=
    mem_FP_comp (f := fun z => gridNodeYBits (routingSpernerRuler (ruler z)) (word z))
      (g := routingDivSixBits) hy routingDivSixBits_mem_FP
  have hqq : (fun z => routingDivSixBits (routingDivSixBits
      (gridNodeYBits (routingSpernerRuler (ruler z)) (word z)))) ∈ FP :=
    mem_FP_comp (f := fun z => routingDivSixBits
      (gridNodeYBits (routingSpernerRuler (ruler z)) (word z)))
      (g := routingDivSixBits) hq routingDivSixBits_mem_FP
  exact routingPadBitsFn_mem_FP hr hqq

/-- Every accepted triangle exposes its actual vertical coordinate in the second field. -/
theorem gridNodeYBits_decode_value {b : ℕ} {word : List Bool} {t : GridTriangle}
    (hd : decodeGridNode b word = some (some t)) :
    Nat.fromBitsLE (gridNodeYBits (List.replicate b false) word) = t.y := by
  have hw := decodeGridNode_length hd
  unfold decodeGridNode at hd
  rw [ite_eq_left hw] at hd
  split at hd
  · cases hd
    simp [gridNodeYBits]
  · split at hd <;> simp_all

/-- Every accepted triangle yields the canonical low-bit encoding of its row label. -/
theorem routingSpernerLabelBits_eq_div_bits {ruler word : List Bool} {t : GridTriangle}
    (hd : decodeGridNode (routingSpernerRuler ruler).length word = some (some t)) :
    routingSpernerLabelBits ruler word = Nat.toBitsLE ruler.length (t.y / 36) := by
  have hv := gridNodeYBits_decode_value hd
  have hv' : Nat.fromBitsLE (gridNodeYBits (routingSpernerRuler ruler) word) = t.y := by
    simpa only [gridNodeYBits, List.length_replicate] using hv
  have hq : Nat.fromBitsLE (routingDivSixBits
      (routingDivSixBits (gridNodeYBits (routingSpernerRuler ruler) word))) = t.y / 36 := by
    rw [routingDivSixBits_value, routingDivSixBits_value, hv', Nat.div_div_eq_div_mul]
  unfold routingSpernerLabelBits
  rw [routingPadBits_eq_toBitsLE, hq]

/-- Decoding any routed endpoint triangle returns the canonical original label. -/
theorem routingSpernerLabelBits_eq_bits {ruler word : List Bool} {t : GridTriangle} {i : ℕ}
    (hd : decodeGridNode (routingSpernerRuler ruler).length word = some (some t))
    (hy : t.y = 36 * i + 8) :
    routingSpernerLabelBits ruler word = Nat.toBitsLE ruler.length i := by
  rw [routingSpernerLabelBits_eq_div_bits hd]
  congr 1
  omega

/-- Decode a target answer, returning the source relation's empty fallback when needed. -/
def routingSpernerDecode (input word : List Bool) : List Bool :=
  caseBit₀ (endOfLineSourceFlag input) (routingSpernerLabelBits (pairFst input) word) []

/-- The source-aware answer decoder has an actual polynomial-time certificate. -/
theorem routingSpernerDecodeFn_mem_FP {input word : List Bool → List Bool}
    (hi : input ∈ FP) (hw : word ∈ FP) :
    (fun z => routingSpernerDecode (input z) (word z)) ∈ FP :=
  selectFn_mem_FP (endOfLineSourceFlagFn_mem_FP hi)
    (routingSpernerLabelBitsFn_mem_FP (mem_FP_comp hi pairFst_mem_FP) hw)
    (constFn_mem_FP [])

/-- The two-argument reduction decoder has a genuine FPn certificate. -/
theorem routingSpernerDecode_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => routingSpernerDecode (v 0) (v 1)) := by
  have h := routingSpernerDecodeFn_mem_FP pairFst_mem_FP pairSnd_mem_FP
  have hc := Cobham.comp (FP_subset_CobhamFP h)
    (fun _ => Cobham.comp₂ Cobham.pairing (.proj (0 : Fin 2)) (.proj 1))
  apply cobham_iff_FPn.mp
  exact hc.of_eq fun v => by simp

/-- Valid sources retain the recovered original label. -/
theorem routingSpernerDecode_valid {input : List Bool} (h : endOfLineSourceValid input)
    (word : List Bool) :
    routingSpernerDecode input word = routingSpernerLabelBits (pairFst input) word := by
  simp [routingSpernerDecode, (endOfLineSourceFlag_accept input).mpr h, caseBit₀]

/-- Invalid source promises decode every target witness to the required empty answer. -/
theorem routingSpernerDecode_invalid {input : List Bool} (h : ¬endOfLineSourceValid input)
    (word : List Bool) : routingSpernerDecode input word = [] := by
  have hf := (endOfLineSourceFlag_flag input).resolve_left
    (fun hf => h ((endOfLineSourceFlag_accept input).mp hf))
  simp [routingSpernerDecode, hf, caseBit₀]

end GameTheory.Complexity.Backend

