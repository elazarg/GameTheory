import GameTheory.Math.RationalQuotientBounds

/-! Quotient bounds permit zero numerators and negative denominators. -/

namespace GameTheory.Tests.RationalQuotientBounds

open GameTheory.Math.RationalQuotientBounds

example : (((0 : ℚ) / 8).num).natAbs ≤ (0 : ℤ).natAbs :=
  num_natAbs_le 0 8 (by decide)

example : ((0 : ℚ) / 8).den = 1 := by decide +kernel

example : (((6 : ℚ) / -8).num).natAbs ≤ (6 : ℤ).natAbs :=
  num_natAbs_le 6 (-8) (by decide)

example : ((6 : ℚ) / -8).den ≤ (-8 : ℤ).natAbs :=
  den_le 6 (-8) (by decide)

example : (((6 : ℚ) / 8).num).natAbs < (6 : ℤ).natAbs ∧
    ((6 : ℚ) / 8).den < (8 : ℤ).natAbs := by decide +kernel

-- Nonzero input denominators are essential to the denominator bound.
example : ¬((6 : ℚ) / 0).den ≤ (0 : ℤ).natAbs := by decide +kernel

end GameTheory.Tests.RationalQuotientBounds
