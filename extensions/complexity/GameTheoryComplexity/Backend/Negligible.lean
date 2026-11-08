module

public import GameTheory.Math.Negligible
public import Complexity.Crypto.Negligible.Basic

@[expose] public section

/-! Native nonnegative negligible bounds agree with the canonical signed
real-valued advantage predicate after taking the nonnegative norm.
-/

namespace GameTheory.Complexity.Backend

/-- Bounding the magnitude identifies the native nonnegative predicate with
two-sided negligible decay of a real advantage. -/
theorem negligible_iff (f : ℕ → ℝ) :
    Cslib.Crypto.Negligible (fun κ => ‖f κ‖₊) ↔ GameTheory.Math.Negligible f := by
  rw [Cslib.Crypto.negligible_iff_coe]
  simpa only [coe_nnnorm, Real.norm_eq_abs, Nat.abs_cast] using
    (Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_abs
      Filter.atTop (fun κ : ℕ => (κ : ℝ)) f).symm

end GameTheory.Complexity.Backend
