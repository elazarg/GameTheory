module

public import GameTheoryComplexity.Backend.SpernerGridCodecMachine
public import GameTheoryComplexity.Backend.GridRoutingBitFields
public import GameTheoryComplexity.Backend.GridRoutingDivision
public import GameTheoryComplexity.Backend.EndOfLineVerifier

@[expose] public section

/-! Routed endpoint triangles have vertical coordinate thirty-six times the
original label plus eight. Two binary divisions by six recover the label without
enumerating a path. Invalid source promises produce the required empty answer. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString
open GameTheory.Math.Sperner

/-- The coordinate ruler for a square containing the translated routed graph. -/
def routingSpernerRuler (ruler : List Bool) : List Bool :=
  ruler ++ ruler ++ List.replicate 8 false

/-- The routed square uses twice the original label width plus eight bits. -/
@[simp] theorem routingSpernerRuler_length (ruler : List Bool) :
    (routingSpernerRuler ruler).length = 2 * ruler.length + 8 := by
  simp [routingSpernerRuler]; omega

/-- The containing square's ruler charges both copies and its fixed margin. -/
@[fun_prop] theorem routingSpernerRuler_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) :
    ComputableInPolyTime (fun z => routingSpernerRuler (ruler z)) enc encBits :=
  bitsAppend (bitsAppend hr hr) (const (List.replicate 8 false))

/-- Decode the endpoint label from a target triangle's vertical coordinate. -/
def routingSpernerLabelBits (ruler word : List Bool) : List Bool :=
  routingPadBits ruler (routingDivSixBits
    (routingDivSixBits (gridNodeYBits (routingSpernerRuler ruler) word)))

/-- Every decoded label word has the original instance's label width. -/
@[simp] theorem routingSpernerLabelBits_length (ruler word : List Bool) :
    (routingSpernerLabelBits ruler word).length = ruler.length := by
  simp [routingSpernerLabelBits]

/-- Label recovery charges both binary divisions and complete fixed-width output. -/
@[fun_prop] theorem routingSpernerLabelBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => routingSpernerLabelBits (ruler z) (word z)) enc encBits :=
  routingPadBits_polyTime hr (routingDivSixBits_polyTime (routingDivSixBits_polyTime
    (gridNodeYBits_polyTime (routingSpernerRuler_polyTime hr) hw)))

/-- Every accepted triangle exposes its actual vertical coordinate in the second field. -/
theorem gridNodeYBits_decode_value {b : ℕ} {word : List Bool} {t : GridTriangle}
    (hd : decodeGridNode b word = some (some t)) :
    lsbValue (gridNodeYBits (List.replicate b false) word) = t.y := by
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
    routingSpernerLabelBits ruler word = lowBits ruler.length (t.y / 36) := by
  have hv := gridNodeYBits_decode_value hd
  have hv' : lsbValue (gridNodeYBits (routingSpernerRuler ruler) word) = t.y := by
    simpa only [gridNodeYBits, List.length_replicate] using hv
  have hq : lsbValue (routingDivSixBits
      (routingDivSixBits (gridNodeYBits (routingSpernerRuler ruler) word))) = t.y / 36 := by
    rw [routingDivSixBits_value, routingDivSixBits_value, hv', Nat.div_div_eq_div_mul]
  unfold routingSpernerLabelBits
  rw [routingPadBits_eq_lowBits, hq]

/-- Decoding any routed endpoint triangle returns the canonical original label. -/
theorem routingSpernerLabelBits_eq_bits {ruler word : List Bool} {t : GridTriangle} {i : ℕ}
    (hd : decodeGridNode (routingSpernerRuler ruler).length word = some (some t))
    (hy : t.y = 36 * i + 8) :
    routingSpernerLabelBits ruler word = lowBits ruler.length i := by
  rw [routingSpernerLabelBits_eq_div_bits hd]
  congr 1
  omega

/-- Decode any target answer with the source relation's prescribed invalid-source fallback. -/
def routingSpernerDecode (input word : List Bool) : List Bool :=
  if endOfLineSourceFlag input then routingSpernerLabelBits (CircuitWords.first input) word else []

/-- Source-aware decoding charges native source validation, binary division and output. -/
@[fun_prop] theorem routingSpernerDecode_polyTime
    {α : Type} {enc : α ↪ List Bool} {input word : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun z => routingSpernerDecode (input z) (word z)) enc encBits :=
  (endOfLineSourceFlag_polyTime hi).ite
    (routingSpernerLabelBits_polyTime (CircuitWords.first_polyTime.comp hi) hw) (const [])

/-- Valid sources retain the recovered original label. -/
theorem routingSpernerDecode_valid {input : List Bool} (h : endOfLineSourceValid input)
    (word : List Bool) :
    routingSpernerDecode input word = routingSpernerLabelBits (CircuitWords.first input) word := by
  simp [routingSpernerDecode, (endOfLineSourceFlag_accept input).mpr h]

/-- Invalid source promises send every target witness to the required empty answer. -/
theorem routingSpernerDecode_invalid {input : List Bool} (h : ¬endOfLineSourceValid input)
    (word : List Bool) : routingSpernerDecode input word = [] := by
  have hf : endOfLineSourceFlag input ≠ true := fun hf =>
    h ((endOfLineSourceFlag_accept input).mp hf)
  exact ite_eq_right hf

end GameTheory.Complexity.Backend
