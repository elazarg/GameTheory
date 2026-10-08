import GameTheoryComplexity.Backend.BinarySignedArithmetic
import Mathlib.Data.Rat.Cast.Order

/-! Polynomial-time signed cross-product comparisons for exact ratio scans.
All four operands are binary signed words, with no canonical-padding premise.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Compare `x*dy` and `y*dx` on four arbitrary signed binary fields. -/
def binarySignedCrossLT (v : Fin 4 → List Bool) : List Bool :=
  binarySignedLTFlag (binarySignedMul (v 0) (v 3)) (binarySignedMul (v 1) (v 2))

/-- The output is exactly the strict signed cross-product comparison. -/
theorem binarySignedCrossLT_value (x y dx dy : List Bool) :
    binarySignedCrossLT ![x, y, dx, dy] =
      [decide (binarySignedValue x * binarySignedValue dy <
        binarySignedValue y * binarySignedValue dx)] := by
  rw [binarySignedCrossLT, binarySignedLTFlag_value, binarySignedMul_value,
    binarySignedMul_value]
  rfl

@[simp] theorem binarySignedCrossLT_length (x y dx dy : List Bool) :
    (binarySignedCrossLT ![x, y, dx, dy]).length = 1 := by
  rw [binarySignedCrossLT_value]
  rfl

/-- Signed cross-product comparison composes four actual polynomial-time word machines. -/
theorem binarySignedCrossLT_cobham : Cobham binarySignedCrossLT :=
  (Cobham.comp₂ binarySignedLTFlag_cobham
    (Cobham.comp₂ binarySignedMul_cobham (.proj 0) (.proj 3))
    (Cobham.comp₂ binarySignedMul_cobham (.proj 1) (.proj 2))).of_eq fun _ => rfl

theorem binarySignedCrossLT_mem_FPn : FPn binarySignedCrossLT :=
  cobham_iff_FPn.mp binarySignedCrossLT_cobham

theorem binarySignedCrossLT_eq_true_iff (x y dx dy : List Bool) :
    binarySignedCrossLT ![x, y, dx, dy] = [true] ↔
      binarySignedValue x * binarySignedValue dy < binarySignedValue y * binarySignedValue dx := by
  rw [binarySignedCrossLT_value]
  simp

/-- Positive decoded denominators turn the integer comparison into exact rational ratio order. -/
theorem binarySignedCrossLT_ratio_lt_iff (x y dx dy : List Bool)
    (hdx : 0 < binarySignedValue dx) (hdy : 0 < binarySignedValue dy) :
    binarySignedCrossLT ![x, y, dx, dy] = [true] ↔
      (binarySignedValue x : ℚ) / (binarySignedValue dx : ℚ) <
        (binarySignedValue y : ℚ) / (binarySignedValue dy : ℚ) := by
  rw [binarySignedCrossLT_eq_true_iff]
  have hdxQ : (0 : ℚ) < (binarySignedValue dx : ℚ) := by exact_mod_cast hdx
  have hdyQ : (0 : ℚ) < (binarySignedValue dy : ℚ) := by exact_mod_cast hdy
  rw [div_lt_div_iff₀ hdxQ hdyQ]
  exact_mod_cast (Iff.rfl :
    binarySignedValue x * binarySignedValue dy < binarySignedValue y * binarySignedValue dx ↔
      binarySignedValue x * binarySignedValue dy < binarySignedValue y * binarySignedValue dx)

end GameTheory.Complexity.Backend
