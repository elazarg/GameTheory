import GameTheory.Finite.BimatrixMinGate
import GameTheory.Math.GridBrouwerFourCorners

/-!
# Canonical four-corner interpolation weights from affine game gates

Complement, subtraction and two-step minimum gates compute the four weights of the existing
rising-diagonal interpolant. Every accepted certificate approximates all four weights uniformly,
with explicit input and matching-block errors. The shared affine factory aggregates aliases.
-/

namespace GameTheory.Finite.BimatrixInterpolationGate
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- A normalized complement subtracts one input at the shared coefficient scale. -/
def complementCoefficients (a : Fin k) (j : Fin k) : ℤ :=
  if j = a then -2 * (k : ℤ) else 0

/-- Complement uses the canonical affine factory with constant offset two. -/
abbrev complementGate (a : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (complementCoefficients a) 2

private theorem complement_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (a : Fin k) :
    (∑ j, ((complementCoefficients a j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (2 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      1 - (k : ℚ) * value c a := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [complementCoefficients, ite_div, ite_mul]
  field_simp
  ring

/-- Every accepted complement block adds only its game error to the input error. -/
theorem complement_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (a out : Fin k)
    (hi : g out = complementGate a) (x E : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (herr : |(k : ℚ) * value c a - x| ≤ E) :
    |(k : ℚ) * value c out - (1 - x)| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) + E := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have ha := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (complementCoefficients a) 2 g c hc hC hM hg hscale out hi
  rw [complement_signal hk c a] at ha
  have hcl := GameTheory.Math.unitClamp_nonexpansive (1 - (k : ℚ) * value c a) (1 - x)
  rw [GameTheory.Math.unitClamp_eq_self (sub_nonneg.mpr hx1) (by linarith)] at hcl
  have he : (1 - (k : ℚ) * value c a) - (1 - x) = -((k : ℚ) * value c a - x) := by ring
  rw [he, abs_neg] at hcl
  have ht := abs_sub_le ((k : ℚ) * value c out)
    (max 0 (min 1 (1 - (k : ℚ) * value c a))) (1 - x)
  linarith

private theorem subtraction_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ia ib out : Fin k)
    (hi : g out = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) ia ib)
    (a b E : ℚ) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (ha : |(k : ℚ) * value c ia - a| ≤ E)
    (hb : |(k : ℚ) * value c ib - b| ≤ E) :
    |(k : ℚ) * value c out - max (a - b) 0| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) + 2 * E := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have hs := BimatrixMinGate.subtraction_error H (2 * (k : ℤ)) M g c hc
    hC hM hg hscale ia ib out hi
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    ((k : ℚ) * value c ia - (k : ℚ) * value c ib) (a - b)
  rw [min_eq_right (by linarith : a - b ≤ 1), max_comm 0 (a - b)] at hcl
  have he : ((k : ℚ) * value c ia - (k : ℚ) * value c ib) - (a - b) =
      ((k : ℚ) * value c ia - a) - ((k : ℚ) * value c ib - b) := by ring
  rw [he] at hcl
  have hab := abs_sub_le ((k : ℚ) * value c ia - a) (0 : ℚ)
    ((k : ℚ) * value c ib - b)
  simp only [sub_zero, zero_sub, abs_neg] at hab
  have ht := abs_sub_le ((k : ℚ) * value c out)
    (max 0 (min 1 ((k : ℚ) * value c ia - (k : ℚ) * value c ib))) (max (a - b) 0)
  linarith

/-- Eight canonical affine blocks approximate the existing four-corner interpolation weights. -/
theorem fourCornerWeights_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (iu iv cu cv t00 w00 t11 w11 w10 w01 : Fin k)
    (hcu : g cu = complementGate iu) (hcv : g cv = complementGate iv)
    (ht00 : g t00 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) cu cv)
    (hw00 : g w00 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) cu t00)
    (ht11 : g t11 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu iv)
    (hw11 : g w11 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu t11)
    (hw10 : g w10 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iu iv)
    (hw01 : g w01 = BimatrixMinGate.subtractionGate (2 * (k : ℤ)) iv iu)
    (u v E δ : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hu : |(k : ℚ) * value c iu - u| ≤ E)
    (hv : |(k : ℚ) * value c iv - v| ≤ E) :
    ∀ i : Fin 4, |(((k : ℚ) * value c (![w00, w11, w10, w01] i) : ℚ) : ℝ) -
      GameTheory.Math.Brouwer.fourCornerWeights (u : ℝ) (v : ℝ) i| ≤
      ((5 * δ + 3 * E : ℚ) : ℝ) := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hu
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have hcu' := complement_error H M hk g c hc hM hg hscale iu cu hcu u E hu0 hu1 hu
  have hcv' := complement_error H M hk g c hc hM hg hscale iv cv hcv v E hv0 hv1 hv
  have hcuE : |(k : ℚ) * value c cu - (1 - u)| ≤ δ + E :=
    hcu'.trans (add_le_add hδ le_rfl)
  have hcvE : |(k : ℚ) * value c cv - (1 - v)| ≤ δ + E :=
    hcv'.trans (add_le_add hδ le_rfl)
  have h00 := BimatrixMinGate.min_error H (2 * (k : ℤ)) M g c hc hC hM hg hscale
    cu cv t00 w00 ht00 hw00 (1 - u) (1 - v) (δ + E) (δ + E)
    (by linarith) (by linarith) (by linarith) hcuE hcvE
  rw [min_sub_sub_left] at h00
  have h00' : |(k : ℚ) * value c w00 - (1 - max u v)| ≤ 5 * δ + 3 * E := by
    linarith only [h00, hδ]
  have h11 := BimatrixMinGate.min_error H (2 * (k : ℤ)) M g c hc hC hM hg hscale
    iu iv t11 w11 ht11 hw11 u v E E hu0 hu1 hv0 hu hv
  have h11' : |(k : ℚ) * value c w11 - min u v| ≤ 5 * δ + 3 * E := by
    linarith only [h11, hδ, hδ0]
  have h10 := subtraction_error H M hk g c hc hM hg hscale iu iv w10 hw10
    u v E hu1 hv0 hu hv
  have h10' : |(k : ℚ) * value c w10 - max (u - v) 0| ≤ 5 * δ + 3 * E := by
    linarith only [h10, hδ, hδ0, hE]
  have h01 := subtraction_error H M hk g c hc hM hg hscale iv iu w01 hw01
    v u E hv1 hu0 hv hu
  have h01' : |(k : ℚ) * value c w01 - max (v - u) 0| ≤ 5 * δ + 3 * E := by
    linarith only [h01, hδ, hδ0, hE]
  intro i
  fin_cases i
  · dsimp [GameTheory.Math.Brouwer.fourCornerWeights]
    exact_mod_cast h00'
  · dsimp [GameTheory.Math.Brouwer.fourCornerWeights]
    exact_mod_cast h11'
  · dsimp [GameTheory.Math.Brouwer.fourCornerWeights]
    exact_mod_cast h10'
  · dsimp [GameTheory.Math.Brouwer.fourCornerWeights]
    exact_mod_cast h01'

end GameTheory.Finite.BimatrixInterpolationGate
