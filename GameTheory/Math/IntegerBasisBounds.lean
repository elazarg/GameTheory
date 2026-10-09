import GameTheory.Math.IntegerDeterminantBound
import GameTheory.Math.RationalQuotientBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-! # Binary bounds for inverse integer bases

Cramer's rule bounds reduced rational solution coordinates by determinants.
The permutation expansion supplies polynomial binary widths even when integer
matrix entries are exponentially large in their advertised coefficient width.
-/

namespace GameTheory.Math.IntegerBasisBounds

variable {n : ℕ}

/-- Uniform binary width for reduced numerators and denominators. -/
def width (n h : ℕ) : ℕ := n * (n + h) + 1

/-- The factorial determinant estimate has a quadratic binary-width bound. -/
theorem factorial_mul_pow_lt (n h : ℕ) : n.factorial * (2 ^ h) ^ n < 2 ^ width n h := by
  have hf : n.factorial ≤ (2 ^ n) ^ n :=
    n.factorial_le_pow.trans (Nat.pow_le_pow_left n.lt_two_pow_self.le n)
  have hbound := Nat.mul_le_mul_right ((2 ^ h) ^ n) hf
  have he : (2 ^ n) ^ n * (2 ^ h) ^ n = 2 ^ (n * (n + h)) := by
    rw [← mul_pow, ← pow_add, ← pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [he] at hbound
  exact hbound.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Bounded integer entries give a polynomial binary width for the determinant. -/
theorem determinant_natAbs_lt (M : Matrix (Fin n) (Fin n) ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) : M.det.natAbs < 2 ^ width n h := by
  have hd := GameTheory.Math.natAbs_det_le M (2 ^ h) hM
  simp only [Fintype.card_fin] at hd
  exact hd.trans_lt (factorial_mul_pow_lt n h)

/-- Each rational solution coordinate is the Cramer determinant quotient. -/
theorem inv_mulVec_eq (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hdet : M.det ≠ 0) (i : Fin n) :
    (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i =
      ((M.updateCol i b).det : ℚ) / (M.det : ℚ) := by
  have hd : (M.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  have hdQ : (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0 := by
    rwa [← Int.cast_det]
  have hc := congrFun ((M.map (fun z : ℤ => (z : ℚ))).det_smul_inv_mulVec_eq_cramer
    (fun j => (b j : ℚ)) (isUnit_iff_ne_zero.mpr hdQ)) i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at hc
  apply (eq_div_iff hd).mpr
  calc
    _ = (M.map (fun z : ℤ => (z : ℚ))).det *
        (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i := by
      rw [← Int.cast_det]
      exact mul_comm _ _
    _ = ((M.map (fun z : ℤ => (z : ℚ))).updateCol i (fun j => (b j : ℚ))).det := hc
    _ = ((M.updateCol i b).det : ℚ) := by
      rw [Int.cast_det, Matrix.map_updateCol]
      rfl

/-- Reduced rational inverse-system coordinates have uniformly bounded binary fields. -/
theorem inv_mulVec_bounds (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hb : ∀ i, (b i).natAbs ≤ 2 ^ h)
    (hdet : M.det ≠ 0) (i : Fin n) :
    ((M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i).num.natAbs <
        2 ^ width n h ∧
      ((M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i).den <
        2 ^ width n h := by
  rw [inv_mulVec_eq M b hdet i]
  have hu : ∀ j k, ((M.updateCol i b) j k).natAbs ≤ 2 ^ h := by
    intro j k
    simp only [Matrix.updateCol_apply]
    split
    · exact hb j
    · exact hM j k
  exact ⟨(RationalQuotientBounds.num_natAbs_le _ _ hdet).trans_lt
      (determinant_natAbs_lt (M.updateCol i b) h hu),
    (RationalQuotientBounds.den_le _ _ hdet).trans_lt (determinant_natAbs_lt M h hM)⟩

/-- Inverse entries share the solution-coordinate bound by using a unit-vector right-hand side. -/
theorem inv_entry_bounds (M : Matrix (Fin n) (Fin n) ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hdet : M.det ≠ 0) (i j : Fin n) :
    ((M.map (fun z : ℤ => (z : ℚ)))⁻¹ i j).num.natAbs < 2 ^ width n h ∧
      ((M.map (fun z : ℤ => (z : ℚ)))⁻¹ i j).den < 2 ^ width n h := by
  have hb : ∀ k, ((Pi.single j (1 : ℤ) : Fin n → ℤ) k).natAbs ≤ 2 ^ h := by
    intro k
    simp only [Pi.single_apply]
    split
    · exact Nat.one_le_pow h 2 (by decide)
    · exact Nat.zero_le _
  have hc : (fun k => ((Pi.single j (1 : ℤ) : Fin n → ℤ) k : ℚ)) =
      (Pi.single j (1 : ℚ) : Fin n → ℚ) := by
    funext k
    simp only [Pi.single_apply]
    split <;> rfl
  have hh := inv_mulVec_bounds M (Pi.single j 1) h hM hb hdet i
  rw [hc, Matrix.mulVec_single_one] at hh
  exact hh

end GameTheory.Math.IntegerBasisBounds
