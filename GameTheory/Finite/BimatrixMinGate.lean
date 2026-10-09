import GameTheory.Finite.BimatrixArithmeticGate
import GameTheory.Math.ClippedArithmetic

/-!
# Minimum evaluation through two affine game gates

Two subtraction gates in the canonical paired-action program compute a minimum after clipping.
The accepted certificate supplies both gate equations, and matching-block error bounds propagate
through the composition without assuming the approximate inputs lie in the unit interval.
-/

namespace GameTheory.Finite.BimatrixMinGate
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- Aggregated subtraction coefficients remain correct when the two inputs coincide. -/
def subtractionCoefficients (C : ℤ) (w z : Fin k) (j : Fin k) : ℤ :=
  (if j = w then C else 0) - (if j = z then C else 0)

/-- Subtraction is a transparent specialization of the canonical affine gate factory. -/
abbrev subtractionGate (C : ℤ) (w z : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (subtractionCoefficients C w z) 0

private theorem subtraction_signal (C : ℤ) (hC : 0 < C)
    (c : BimatrixCertificate (k * 2) (k * 2)) (w z : Fin k) :
    (∑ j, ((subtractionCoefficients C w z j : ℤ) : ℚ) / C * ((k : ℚ) * value c j)) +
      (k : ℚ) * (0 : ℤ) / C = (k : ℚ) * value c w - (k : ℚ) * value c z := by
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  simp [subtractionCoefficients, sub_div, sub_mul, Finset.sum_sub_distrib,
    ite_div, ite_mul, hCq]

/-- Every accepted subtraction block approximates the intended unit-clipped difference. -/
theorem subtraction_error (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 < C) (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (w z out : Fin k)
    (hout : g out = subtractionGate C w z) :
    |(k : ℚ) * value c out -
      max 0 (min 1 ((k : ℚ) * value c w - (k : ℚ) * value c z))| ≤
        (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
  have h := BimatrixArithmeticGate.normalized_value_error H C M
    (subtractionCoefficients C w z) 0 g c hc hC hM hg hscale out hout
  rw [subtraction_signal C hC c w z] at h
  exact h

/-- Two actual subtraction blocks propagate input and game errors to the exact minimum. -/
theorem min_error (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 < C) (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (iw iz it out : Fin k)
    (ht : g it = subtractionGate C iw iz) (hout : g out = subtractionGate C iw it)
    (w z η ε : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hz0 : 0 ≤ z)
    (hw : |(k : ℚ) * value c iw - w| ≤ η)
    (hz : |(k : ℚ) * value c iz - z| ≤ ε) :
    |(k : ℚ) * value c out - min w z| ≤
      2 * ((k : ℚ) * (((M + C : ℤ) : ℚ) / H)) + 2 * η + ε := by
  exact GameTheory.Math.clippedSub_min_error w z
    ((k : ℚ) * value c iw) ((k : ℚ) * value c iz)
    ((k : ℚ) * value c it) ((k : ℚ) * value c out)
    η ε ((k : ℚ) * (((M + C : ℤ) : ℚ) / H)) hw0 hw1 hz0 hw hz
    (subtraction_error H C M g c hc hC hM hg hscale iw iz it ht)
    (subtraction_error H C M g c hc hC hM hg hscale iw it out hout)

/-- The same two blocks approximate a weighted Boolean indicator without multiplication. -/
theorem min_weight_error (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 < C) (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (iw iz it out : Fin k)
    (ht : g it = subtractionGate C iw iz) (hout : g out = subtractionGate C iw it)
    (bit : Bool) (w η ε : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hw : |(k : ℚ) * value c iw - w| ≤ η)
    (hz : |(k : ℚ) * value c iz - (if bit then 1 else 0)| ≤ ε) :
    |(k : ℚ) * value c out - (if bit then w else 0)| ≤
      2 * ((k : ℚ) * (((M + C : ℤ) : ℚ) / H)) + 2 * η + ε := by
  have hz0 : (0 : ℚ) ≤ (if bit then 1 else 0) := by cases bit <;> norm_num
  have h := min_error H C M g c hc hC hM hg hscale iw iz it out ht hout
    w (if bit then 1 else 0) η ε hw0 hw1 hz0 hw hz
  cases bit
  · simpa only [Bool.false_eq_true, ite_false, min_eq_right hw0] using h
  · simpa only [ite_true, min_eq_left hw1] using h

end GameTheory.Finite.BimatrixMinGate
