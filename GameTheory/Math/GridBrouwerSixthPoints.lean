import GameTheory.Math.GridBrouwerMap
import Mathlib.Data.Fin.VecNotation

/-! Rational grid points at sixth-cell resolution. The last vertex of the
square belongs to its last cell, with local coordinate one. This convention
also covers zero-width binary grids without exceptional geometric encodings. -/

namespace GameTheory.Math.Brouwer

open Sperner

/-- The cell containing a sixth-grid coordinate, clipped at the far boundary. -/
def sixthCellIndex (n X : ℕ) : ℕ := min (X / 6) (n - 1)

/-- The local numerator inside the selected cell, including six at its far edge. -/
def sixthOffset (n X : ℕ) : ℕ := X - 6 * sixthCellIndex n X

/-- Locate a point in the rising-diagonal grid triangulation. -/
def sixthTriangle (n X Y : ℕ) : GridTriangle :=
  ⟨sixthCellIndex n X, sixthCellIndex n Y,
    decide (sixthOffset n X < sixthOffset n Y)⟩

/-- Bounded point numerators give a valid cell and a local offset from zero to six. -/
theorem sixthCellIndex_bounds {n X : ℕ} (hn : 0 < n) (hX : X ≤ 6 * n) :
    sixthCellIndex n X < n ∧ sixthOffset n X ≤ 6 ∧
      6 * sixthCellIndex n X + sixthOffset n X = X := by
  have hm := Nat.mod_lt X (show 0 < 6 by decide)
  have hd := Nat.mod_add_div X 6
  by_cases h : X / 6 ≤ n - 1
  · simp only [sixthCellIndex, Nat.min_eq_left h, sixthOffset]
    omega
  · have h' : n - 1 ≤ X / 6 := by omega
    simp only [sixthCellIndex, Nat.min_eq_right h', sixthOffset]
    omega

/-- Both decoded coordinates select a valid triangle, including boundary points. -/
theorem sixthTriangle_valid {n X Y : ℕ} (hn : 0 < n)
    (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) : ValidTriangle n (sixthTriangle n X Y) :=
  ⟨(sixthCellIndex_bounds hn hX).1, (sixthCellIndex_bounds hn hY).1⟩

/-- Barycentric coordinates computed from the two sixth-cell offsets. -/
def sixthWeights (n X Y : ℕ) : Fin 3 → ℚ :=
  let x : ℚ := sixthOffset n X
  let y : ℚ := sixthOffset n Y
  if sixthOffset n X < sixthOffset n Y then
    ![(6 - y) / 6, x / 6, (y - x) / 6]
  else ![(6 - x) / 6, (x - y) / 6, y / 6]

/-- The locator's affine weights always sum to one. -/
theorem sixthWeights_sum (n X Y : ℕ) :
    sixthWeights n X Y 0 + sixthWeights n X Y 1 + sixthWeights n X Y 2 = 1 := by
  unfold sixthWeights
  split_ifs <;> dsimp <;> ring

/-- Valid point numerators have nonnegative barycentric weights. -/
theorem sixthWeights_nonneg {n X Y : ℕ} (hn : 0 < n)
    (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) (p : Fin 3) :
    0 ≤ sixthWeights n X Y p := by
  have hx := (sixthCellIndex_bounds hn hX).2.1
  have hy := (sixthCellIndex_bounds hn hY).2.1
  have hx' : (sixthOffset n X : ℚ) ≤ 6 := by exact_mod_cast hx
  have hy' : (sixthOffset n Y : ℚ) ≤ 6 := by exact_mod_cast hy
  have hx0 : (0 : ℚ) ≤ sixthOffset n X := Nat.cast_nonneg _
  have hy0 : (0 : ℚ) ≤ sixthOffset n Y := Nat.cast_nonneg _
  unfold sixthWeights
  split_ifs with h
  · have h' : (sixthOffset n X : ℚ) < sixthOffset n Y := by exact_mod_cast h
    fin_cases p <;> dsimp <;> linarith
  · have h' : (sixthOffset n Y : ℚ) ≤ sixthOffset n X := by exact_mod_cast (show _ by omega)
    fin_cases p <;> dsimp <;> linarith

end GameTheory.Math.Brouwer
