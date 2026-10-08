import GameTheoryComplexity.Backend.SpernerGridCodec
import GameTheory.Math.GridBrouwerSixthPoints

/-! Rational square points are encoded by two fixed-width integer numerators.
The common denominator is six times the grid size. Boundary points are assigned
to the last cell, so the locator works on the closed square. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Numerator fields leave three bits beyond the grid coordinate width. -/
def pointCoordinateWidth (b : ℕ) : ℕ := b + 3

/-- The two numerator fields have equal fixed width. -/
def pointWordWidth (b : ℕ) : ℕ := 2 * pointCoordinateWidth b

/-- Serialize the integer numerators of a normalized rational square point. -/
def encodeBrouwerPoint (b : ℕ) (p : ℕ × ℕ) : List Bool :=
  Nat.toBitsLE (pointCoordinateWidth b) p.1 ++ Nat.toBitsLE (pointCoordinateWidth b) p.2

/-- Reject wrong lengths and numerators outside the closed square. -/
def decodeBrouwerPoint (b : ℕ) (word : List Bool) : Option (ℕ × ℕ) :=
  let X := Nat.fromBitsLE (word.take (pointCoordinateWidth b))
  let Y := Nat.fromBitsLE (word.drop (pointCoordinateWidth b))
  if word.length = pointWordWidth b ∧ X ≤ 6 * 2 ^ b ∧ Y ≤ 6 * 2 ^ b
    then some (X, Y) else none

/-- Choose the cell immediately below an upper boundary coordinate. -/
abbrev brouwerCellIndex (b X : ℕ) : ℕ := sixthCellIndex (2 ^ b) X

/-- Locate a point using the rising diagonal of its cell. -/
abbrev locateBrouwerPoint (b X Y : ℕ) : GridTriangle := sixthTriangle (2 ^ b) X Y

@[simp] theorem encodeBrouwerPoint_length (b : ℕ) (p : ℕ × ℕ) :
    (encodeBrouwerPoint b p).length = pointWordWidth b := by
  simp [encodeBrouwerPoint, pointWordWidth, two_mul]

theorem brouwer_numerator_lt (b X : ℕ) (h : X ≤ 6 * 2 ^ b) :
    X < 2 ^ pointCoordinateWidth b := by
  have hp : 0 < 2 ^ b := by positivity
  rw [pointCoordinateWidth, pow_add]
  norm_num
  omega

@[simp] theorem decodeBrouwerPoint_encode (b : ℕ) (p : ℕ × ℕ)
    (hx : p.1 ≤ 6 * 2 ^ b) (hy : p.2 ≤ 6 * 2 ^ b) :
    decodeBrouwerPoint b (encodeBrouwerPoint b p) = some p := by
  simp [decodeBrouwerPoint, encodeBrouwerPoint, pointWordWidth, two_mul,
    Nat.fromBitsLE_toBitsLE (brouwer_numerator_lt b p.1 hx),
    Nat.fromBitsLE_toBitsLE (brouwer_numerator_lt b p.2 hy), hx, hy]

theorem decodeBrouwerPoint_properties {b : ℕ} {word : List Bool} {p : ℕ × ℕ}
    (h : decodeBrouwerPoint b word = some p) :
    word.length = pointWordWidth b ∧ p.1 ≤ 6 * 2 ^ b ∧ p.2 ≤ 6 * 2 ^ b ∧
      Nat.fromBitsLE (word.take (pointCoordinateWidth b)) = p.1 ∧
      Nat.fromBitsLE (word.drop (pointCoordinateWidth b)) = p.2 := by
  unfold decodeBrouwerPoint at h
  dsimp only at h
  split at h
  · rename_i hp
    cases h
    exact ⟨hp.1, hp.2.1, hp.2.2, rfl, rfl⟩
  · simp at h

theorem encodeBrouwerPoint_decode {b : ℕ} {word : List Bool} {p : ℕ × ℕ}
    (h : decodeBrouwerPoint b word = some p) : encodeBrouwerPoint b p = word := by
  obtain ⟨hlen, _, _, hx, hy⟩ := decodeBrouwerPoint_properties h
  have hxl : (word.take (pointCoordinateWidth b)).length = pointCoordinateWidth b := by
    simp only [List.length_take, hlen, pointWordWidth]; omega
  have hyl : (word.drop (pointCoordinateWidth b)).length = pointCoordinateWidth b := by
    simp only [List.length_drop, hlen, pointWordWidth]; omega
  have hxw := Nat.toBitsLE_fromBitsLE (word.take (pointCoordinateWidth b))
  have hyw := Nat.toBitsLE_fromBitsLE (word.drop (pointCoordinateWidth b))
  rw [hxl, hx] at hxw
  rw [hyl, hy] at hyw
  simp [encodeBrouwerPoint, hxw, hyw]

theorem brouwerCellIndex_bounds (b X : ℕ) (hx : X ≤ 6 * 2 ^ b) :
    brouwerCellIndex b X < 2 ^ b ∧
    6 * brouwerCellIndex b X ≤ X ∧ X ≤ 6 * brouwerCellIndex b X + 6 := by
  have hp : 0 < 2 ^ b := by positivity
  have hm := Nat.mod_lt X (by decide : 0 < 6)
  have he := Nat.mod_add_div X 6
  unfold brouwerCellIndex sixthCellIndex
  by_cases hq : X / 6 ≤ 2 ^ b - 1
  · rw [Nat.min_eq_left hq]
    omega
  · rw [Nat.min_eq_right (by omega)]
    omega

theorem locateBrouwerPoint_valid (b X Y : ℕ)
    (hx : X ≤ 6 * 2 ^ b) (hy : Y ≤ 6 * 2 ^ b) :
    ValidTriangle (2 ^ b) (locateBrouwerPoint b X Y) :=
  ⟨(brouwerCellIndex_bounds b X hx).1, (brouwerCellIndex_bounds b Y hy).1⟩

end GameTheory.Complexity.Backend
