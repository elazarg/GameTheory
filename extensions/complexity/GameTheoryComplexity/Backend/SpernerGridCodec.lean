import Complexitylib.Mathlib.NatBits
import GameTheory.Math.SpernerGridGeometry

/-! Fixed-width little-endian grid nodes reserve the all-zero word for the
boundary source. Triangle words carry a tag, an orientation bit, and two
coordinates. Other source-tagged words and incorrect lengths are rejected. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner

/-- Two coordinate blocks, an orientation bit, and a source tag. -/
def gridNodeWidth (b : ℕ) : ℕ := 2 * b + 2

/-- Serialize the boundary source or one grid triangle at fixed coordinate width. -/
def encodeGridNode (b : ℕ) : Option GridTriangle → List Bool
  | none => List.replicate (gridNodeWidth b) false
  | some t => [true, t.upper] ++ Nat.toBitsLE b t.x ++ Nat.toBitsLE b t.y

/-- Parse a node word, requiring the source representation to be exactly all zero. -/
def decodeGridNode (b : ℕ) (word : List Bool) : Option (Option GridTriangle) :=
  if word.length = gridNodeWidth b then
    if word.headD false then
      some (some ⟨Nat.fromBitsLE (word.tail.tail.take b),
        Nat.fromBitsLE (word.tail.tail.drop b), word.tail.headD false⟩)
    else if word = List.replicate (gridNodeWidth b) false then some none else none
  else none

/-- Encoded nodes have exactly the advertised word width. -/
@[simp] theorem encodeGridNode_length (b : ℕ) (node : Option GridTriangle) :
    (encodeGridNode b node).length = gridNodeWidth b := by
  cases node with
  | none => simp [encodeGridNode]
  | some t => simp [encodeGridNode, gridNodeWidth]; omega

/-- Source serialization round-trips at every coordinate width, including zero. -/
@[simp] theorem decodeGridNode_source (b : ℕ) :
    decodeGridNode b (encodeGridNode b none) = some none := by
  have hh : (List.replicate (gridNodeWidth b) false).headD false = false := by
    cases gridNodeWidth b <;> rfl
  simp only [decodeGridNode, encodeGridNode, List.length_replicate, ↓reduceIte]
  rw [hh]
  rfl

/-- Bounded triangles and the source round-trip through the node codec. -/
theorem decodeGridNode_encode (b : ℕ) (node : Option GridTriangle)
    (hv : ∀ t, node = some t → ValidTriangle (2 ^ b) t) :
    decodeGridNode b (encodeGridNode b node) = some node := by
  cases node with
  | none => exact decodeGridNode_source b
  | some t =>
    obtain ⟨hx, hy⟩ := hv t rfl
    simp only [decodeGridNode, encodeGridNode_length, ↓reduceIte]
    simp [encodeGridNode, Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hy]

/-- A successful parse always has the exact node width. -/
theorem decodeGridNode_length {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) : word.length = gridNodeWidth b := by
  by_contra hw
  simp [decodeGridNode, hw] at hd

private theorem coordinate_lengths {b : ℕ} {word : List Bool}
    (hw : word.length = gridNodeWidth b) :
    (word.tail.tail.take b).length = b ∧ (word.tail.tail.drop b).length = b := by
  have ht : word.tail.tail.length = 2 * b := by
    simp only [List.length_tail, gridNodeWidth] at hw ⊢
    omega
  simp only [List.length_take, List.length_drop, ht]
  omega

/-- Decoded triangle coordinates are bounded by the coordinate block's capacity. -/
theorem decodeGridNode_valid {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) :
    ∀ t, node = some t → ValidTriangle (2 ^ b) t := by
  have hw := decodeGridNode_length hd
  obtain ⟨hxlen, hylen⟩ := coordinate_lengths hw
  unfold decodeGridNode at hd
  rw [ite_eq_left hw] at hd
  split at hd
  · cases hd
    intro t he
    cases he
    constructor
    · simpa only [hxlen] using Nat.fromBitsLE_lt_pow_length (word.tail.tail.take b)
    · simpa only [hylen] using Nat.fromBitsLE_lt_pow_length (word.tail.tail.drop b)
  · split at hd
    · cases hd
      intro t he
      cases he
    · simp at hd

/-- Every accepted word is the canonical serialization of its decoded node. -/
theorem encodeGridNode_decode {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) : encodeGridNode b node = word := by
  have hw := decodeGridNode_length hd
  obtain ⟨hxlen, hylen⟩ := coordinate_lengths hw
  have hx := Nat.toBitsLE_fromBitsLE (word.tail.tail.take b)
  have hy := Nat.toBitsLE_fromBitsLE (word.tail.tail.drop b)
  rw [hxlen] at hx
  rw [hylen] at hy
  have hsplit : word = [word.headD false, word.tail.headD false] ++
      word.tail.tail.take b ++ word.tail.tail.drop b := by
    cases word with
    | nil => simp [gridNodeWidth] at hw
    | cons tag tail =>
      cases tail with
      | nil => simp [gridNodeWidth] at hw
      | cons upper bits => simp
  unfold decodeGridNode at hd
  rw [ite_eq_left hw] at hd
  split at hd
  · rename_i htag
    cases hd
    simp only [encodeGridNode, hx, hy]
    rw [← htag]
    exact hsplit.symm
  · split at hd
    · rename_i hzero
      cases hd
      exact hzero.symm
    · simp at hd

end GameTheory.Complexity.Backend
