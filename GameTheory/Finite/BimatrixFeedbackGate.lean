import GameTheory.Finite.BimatrixArithmeticGate
import GameTheory.Finite.BimatrixGateProgramBounds
import GameTheory.Math.ClippedFeedbackComposition

/-!
# Projected signed feedback in a cyclic affine game program

Three canonical affine blocks add at half scale, subtract at half scale, and double back into
the original coordinate wire. Clipping that wire yields an approximately stationary projected
update. All gate equations follow from the accepted certificate, including aliased inputs and
cyclic outputs; no source computation or program generator is assumed.
-/

namespace GameTheory.Finite.BimatrixFeedbackGate
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- Half-scale addition retains both contributions when inputs coincide. -/
def halfAddCoefficients (q p : Fin k) (j : Fin k) : ℤ :=
  (if j = q then (k : ℤ) else 0) + (if j = p then (k : ℤ) else 0)

/-- Half-scale addition uses the canonical affine gate factory. -/
abbrev halfAddGate (q p : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (halfAddCoefficients q p) 0

/-- Aggregate coefficients for one input minus half of a second input. -/
def subtractHalfCoefficients (h m : Fin k) (j : Fin k) : ℤ :=
  (if j = h then 2 * (k : ℤ) else 0) - (if j = m then (k : ℤ) else 0)

/-- Half-scale subtraction uses the shared affine factory. -/
abbrev subtractHalfGate (h m : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (subtractHalfCoefficients h m) 0

/-- Doubling uses twice the shared affine coefficient scale. -/
def doubleCoefficients (s : Fin k) (j : Fin k) : ℤ :=
  if j = s then 4 * (k : ℤ) else 0

/-- Doubling specializes the canonical affine factory. -/
abbrev doubleGate (s : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (doubleCoefficients s) 0

private theorem halfAdd_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (q p : Fin k) :
    (∑ j, ((halfAddCoefficients q p j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      ((k : ℚ) * value c q) / 2 + ((k : ℚ) * value c p) / 2 := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [halfAddCoefficients, add_div, add_mul, Finset.sum_add_distrib, ite_div, ite_mul]
  field_simp

private theorem subtractHalf_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (h m : Fin k) :
    (∑ j, ((subtractHalfCoefficients h m j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      (k : ℚ) * value c h - ((k : ℚ) * value c m) / 2 := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [subtractHalfCoefficients, sub_div, sub_mul, Finset.sum_sub_distrib, ite_div, ite_mul]
  field_simp

private theorem double_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (s : Fin k) :
    (∑ j, ((doubleCoefficients s j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      2 * ((k : ℚ) * value c s) := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [doubleCoefficients, ite_div, ite_mul]
  field_simp
  norm_num

/-- Every accepted cyclic program approximately fixes its clipped coordinate under feedback. -/
theorem cyclic_feedback_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (iq ip im ih is : Fin k)
    (hh : g ih = halfAddGate iq ip) (hs : g is = subtractHalfGate ih im)
    (hq : g iq = doubleGate is) (p m ηp ηm δ : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm0 : 0 ≤ m)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hp : |(k : ℚ) * value c ip - p| ≤ ηp)
    (hm : |(k : ℚ) * value c im - m| ≤ ηm) :
    let x := max 0 (min 1 ((k : ℚ) * value c iq))
    |x - max 0 (min 1 (x + p - m))| ≤ 7 * δ + ηp + ηm := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have hh' := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (halfAddCoefficients iq ip) 0 g c hc hC hM hg hscale ih hh
  rw [halfAdd_signal hk c iq ip] at hh'
  have hs' := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (subtractHalfCoefficients ih im) 0 g c hc hC hM hg hscale is hs
  rw [subtractHalf_signal hk c ih im] at hs'
  have hq' := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (doubleCoefficients is) 0 g c hc hC hM hg hscale iq hq
  rw [double_signal hk c is] at hq'
  have hclip := (BimatrixGateProgramBounds.normalized_value_clipping_error H (2 * (k : ℤ))
    M g c hc hC.le hM hg hscale iq).trans hδ
  let x := max 0 (min 1 ((k : ℚ) * value c iq))
  have hx0 : 0 ≤ x := le_max_left _ _
  have hx1 : x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have he := GameTheory.Math.clippedFeedback_three_steps_error x 1 p m
    ((k : ℚ) * value c iq) ((k : ℚ) * value c ip) ((k : ℚ) * value c im)
    ((k : ℚ) * value c ih) ((k : ℚ) * value c is) ((k : ℚ) * value c iq)
    δ ηp ηm δ hx0 hx1 (by norm_num) (by norm_num) hp0 hp1 hm0
    hclip hp hm
    (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh'.trans hδ)
    (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hs'.trans hδ)
    (hq'.trans hδ)
  simp only [one_mul] at he
  have ht := abs_sub_le x ((k : ℚ) * value c iq) (max 0 (min 1 (x + p - m)))
  have hexpr' : x + (p - m) = x + p - m := by ring
  rw [hexpr'] at he
  change |x - max 0 (min 1 (x + p - m))| ≤ _
  have hclip' : |x - (k : ℚ) * value c iq| ≤ δ := by
    simpa only [abs_sub_comm] using hclip
  linarith

end GameTheory.Finite.BimatrixFeedbackGate
