import Complexitylib.Mathlib.NatBits
import Mathlib.Data.List.Basic

/-! Routed grid points use two fixed-width little-endian coordinate blocks.
Every word of the advertised length denotes a bounded point in the square;
no tag or orientation field is reserved. -/

namespace GameTheory.Complexity.Backend

/-- Coordinate width for routing a graph with `b` bits per original vertex. -/
def routingCoordinateWidth (b : ℕ) : ℕ := 2 * b + 3

/-- Two coordinate blocks fill the routed point word. -/
def routingPointWidth (b : ℕ) : ℕ := 2 * routingCoordinateWidth b

/-- Serialize a grid point in two fixed-width little-endian blocks. -/
def encodeRoutingPoint (b : ℕ) (point : ℕ × ℕ) : List Bool :=
  Nat.toBitsLE (routingCoordinateWidth b) point.1 ++
    Nat.toBitsLE (routingCoordinateWidth b) point.2

/-- Decode an exact-width word, rejecting every malformed length. -/
def decodeRoutingPoint (b : ℕ) (word : List Bool) : Option (ℕ × ℕ) :=
  if word.length = routingPointWidth b then
    some (Nat.fromBitsLE (word.take (routingCoordinateWidth b)),
      Nat.fromBitsLE (word.drop (routingCoordinateWidth b)))
  else none

/-- Every encoded point occupies exactly two coordinate blocks. -/
@[simp] theorem encodeRoutingPoint_length (b : ℕ) (point : ℕ × ℕ) :
    (encodeRoutingPoint b point).length = routingPointWidth b := by
  simp [encodeRoutingPoint, routingPointWidth, two_mul]

/-- Every point within the coordinate capacity round-trips exactly. -/
theorem decodeRoutingPoint_encode (b : ℕ) (point : ℕ × ℕ)
    (hx : point.1 < 2 ^ routingCoordinateWidth b)
    (hy : point.2 < 2 ^ routingCoordinateWidth b) :
    decodeRoutingPoint b (encodeRoutingPoint b point) = some point := by
  simp only [decodeRoutingPoint, encodeRoutingPoint_length, ↓reduceIte]
  simp [encodeRoutingPoint, Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hy]

/-- A successful decoder result certifies the exact serialized length. -/
theorem decodeRoutingPoint_length {b : ℕ} {word : List Bool} {point : ℕ × ℕ}
    (hd : decodeRoutingPoint b word = some point) : word.length = routingPointWidth b := by
  by_contra hw
  simp [decodeRoutingPoint, hw] at hd

private theorem coordinate_lengths {b : ℕ} {word : List Bool}
    (hw : word.length = routingPointWidth b) :
    (word.take (routingCoordinateWidth b)).length = routingCoordinateWidth b ∧
      (word.drop (routingCoordinateWidth b)).length = routingCoordinateWidth b := by
  simp only [List.length_take, List.length_drop, hw, routingPointWidth]
  omega

/-- Both decoded coordinates lie strictly within the binary block capacity. -/
theorem decodeRoutingPoint_bound {b : ℕ} {word : List Bool} {point : ℕ × ℕ}
    (hd : decodeRoutingPoint b word = some point) :
    point.1 < 2 ^ routingCoordinateWidth b ∧ point.2 < 2 ^ routingCoordinateWidth b := by
  have hw := decodeRoutingPoint_length hd
  obtain ⟨hxlen, hylen⟩ := coordinate_lengths hw
  unfold decodeRoutingPoint at hd
  rw [ite_eq_left hw] at hd
  cases hd
  constructor
  · simpa only [hxlen] using Nat.fromBitsLE_lt_pow_length (word.take (routingCoordinateWidth b))
  · simpa only [hylen] using Nat.fromBitsLE_lt_pow_length (word.drop (routingCoordinateWidth b))

/-- Every accepted word is exactly the encoding of its decoded point. -/
theorem encodeRoutingPoint_decode {b : ℕ} {word : List Bool} {point : ℕ × ℕ}
    (hd : decodeRoutingPoint b word = some point) : encodeRoutingPoint b point = word := by
  have hw := decodeRoutingPoint_length hd
  obtain ⟨hxlen, hylen⟩ := coordinate_lengths hw
  have hx := Nat.toBitsLE_fromBitsLE (word.take (routingCoordinateWidth b))
  have hy := Nat.toBitsLE_fromBitsLE (word.drop (routingCoordinateWidth b))
  rw [hxlen] at hx
  rw [hylen] at hy
  unfold decodeRoutingPoint at hd
  rw [ite_eq_left hw] at hd
  cases hd
  simp only [encodeRoutingPoint, hx, hy, List.take_append_drop]

/-- Bounded grid points with equal binary encodings are equal. -/
theorem encodeRoutingPoint_injective {b : ℕ} {p q : ℕ × ℕ}
    (hx : p.1 < 2 ^ routingCoordinateWidth b) (hy : p.2 < 2 ^ routingCoordinateWidth b)
    (hqx : q.1 < 2 ^ routingCoordinateWidth b) (hqy : q.2 < 2 ^ routingCoordinateWidth b)
    (h : encodeRoutingPoint b p = encodeRoutingPoint b q) : p = q := by
  have hd := congrArg (decodeRoutingPoint b) h
  rw [decodeRoutingPoint_encode b p hx hy, decodeRoutingPoint_encode b q hqx hqy] at hd
  exact Option.some.inj hd

private theorem zero_bits (width : ℕ) : Nat.toBitsLE width 0 = List.replicate width false := by
  have hz : ∀ m, Nat.toBits m 0 = List.replicate m false := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [Nat.toBits, ih, List.replicate_succ]
  simp [Nat.toBitsLE, hz]

/-- The grid origin has the all-zero routing word. -/
@[simp] theorem encodeRoutingPoint_origin (b : ℕ) :
    encodeRoutingPoint b (0, 0) = List.replicate (routingPointWidth b) false := by
  simp [encodeRoutingPoint, zero_bits, routingPointWidth, two_mul]

/-- Words of any incorrect length are rejected. -/
theorem decodeRoutingPoint_bad_length {b : ℕ} {word : List Bool}
    (hw : word.length ≠ routingPointWidth b) : decodeRoutingPoint b word = none := by
  simp [decodeRoutingPoint, hw]

end GameTheory.Complexity.Backend
