import GameTheory.Math.IntegerBasisBounds
import Mathlib.Tactic.Ring

/-! # Common-denominator encoding of nonnegative integer-system solutions

The absolute determinant supplies one positive denominator for every coordinate.
Multiplying Cramer determinants by the determinant's sign gives nonnegative
integer numerators whenever the inverse-system solution is nonnegative.
-/

namespace GameTheory.Math.IntegerCramerEncoding

variable {n : ℕ}

/-- The absolute determinant is a common denominator. -/
def denominator (M : Matrix (Fin n) (Fin n) ℤ) : ℕ := M.det.natAbs

/-- Sign-adjusted Cramer numerators, represented as naturals. -/
def numerator (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) : ℕ :=
  (Int.sign M.det * (M.updateCol i b).det).toNat

theorem denominator_pos (M : Matrix (Fin n) (Fin n) ℤ) (hdet : M.det ≠ 0) :
    0 < denominator M := Int.natAbs_pos.mpr hdet

private theorem signed_numerator_eq (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hdet : M.det ≠ 0) (i : Fin n) :
    ((Int.sign M.det * (M.updateCol i b).det : ℤ) : ℚ) =
      (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i *
        (denominator M : ℚ) := by
  have hs : ((Int.sign M.det : ℤ) : ℚ) * (M.det : ℚ) = (denominator M : ℚ) := by
    have he := congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs M.det)
    simpa only [Int.cast_mul, Int.cast_natCast, denominator] using he
  have hd : (M.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  have hc := ((eq_div_iff hd).mp (IntegerBasisBounds.inv_mulVec_eq M b hdet i)).symm
  rw [Int.cast_mul, hc, ← hs]
  ring

/-- Decoding natural Cramer fields recovers the nonnegative rational solution. -/
theorem decode (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (hdet : M.det ≠ 0)
    (hz : ∀ i, 0 ≤ (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i)
    (i : Fin n) :
    (numerator M b i : ℚ) / (denominator M : ℚ) =
      (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i := by
  have hnQ : (0 : ℚ) ≤ ((Int.sign M.det * (M.updateCol i b).det : ℤ) : ℚ) := by
    rw [signed_numerator_eq M b hdet i]
    exact mul_nonneg (hz i) (Nat.cast_nonneg _)
  have hn : 0 ≤ Int.sign M.det * (M.updateCol i b).det := by exact_mod_cast hnQ
  have hcast : (numerator M b i : ℚ) =
      ((Int.sign M.det * (M.updateCol i b).det : ℤ) : ℚ) := by
    unfold numerator
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hcast, signed_numerator_eq M b hdet i]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (denominator_pos M hdet).ne')

theorem denominator_lt (M : Matrix (Fin n) (Fin n) ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) :
    denominator M < 2 ^ IntegerBasisBounds.width n h :=
  IntegerBasisBounds.determinant_natAbs_lt M h hM

/-- Even before checking nonnegativity, the stored numerator has the advertised width. -/
theorem numerator_lt (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hb : ∀ i, (b i).natAbs ≤ 2 ^ h)
    (hdet : M.det ≠ 0) (i : Fin n) :
    numerator M b i < 2 ^ IntegerBasisBounds.width n h := by
  have hu : ∀ j k, ((M.updateCol i b) j k).natAbs ≤ 2 ^ h := by
    intro j k
    simp only [Matrix.updateCol_apply]
    split
    · exact hb j
    · exact hM j k
  have hs : (Int.sign M.det * (M.updateCol i b).det).natAbs = (M.updateCol i b).det.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hdet, one_mul]
  have hn : numerator M b i ≤ (Int.sign M.det * (M.updateCol i b).det).natAbs :=
    Int.toNat_le.mpr Int.le_natAbs
  rw [hs] at hn
  exact hn.trans_lt (IntegerBasisBounds.determinant_natAbs_lt (M.updateCol i b) h hu)

end GameTheory.Math.IntegerCramerEncoding
