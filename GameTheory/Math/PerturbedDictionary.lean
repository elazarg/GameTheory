import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Coefficient vectors for a linear system with symbolic right-hand-side perturbations.

The constant coefficient solves the original system; the remaining coefficients
are the inverse basis matrix. Distinct inverse rows remain distinct after division
by nonzero directional coefficients, so symbolic ratio tests cannot tie.
-/

namespace GameTheory.Math.PerturbedDictionary

variable {K : Type*} [Field K] {n : ℕ}

/-- Coefficients of `B⁻¹ (q + (ε, ε², …))`, with the constant term first. -/
noncomputable def dictionaryCoefficients (B : Matrix (Fin n) (Fin n) K)
    (q : Fin n → K) (i : Fin n) : Fin (n + 1) → K :=
  Fin.cons (B⁻¹.mulVec q i) (fun j => B⁻¹ i j)

@[simp] theorem coefficient_zero (B : Matrix (Fin n) (Fin n) K)
    (q : Fin n → K) (i : Fin n) :
    dictionaryCoefficients B q i 0 = B⁻¹.mulVec q i := rfl

@[simp] theorem coefficient_succ (B : Matrix (Fin n) (Fin n) K)
    (q : Fin n → K) (i j : Fin n) :
    dictionaryCoefficients B q i j.succ = B⁻¹ i j := rfl

/-- Multiplying the constant coefficients by the basis recovers the original vector. -/
theorem constant_mul (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0)
    (q : Fin n → K) :
    B.mulVec (fun i => dictionaryCoefficients B q i 0) = q := by
  simp only [coefficient_zero, Matrix.mulVec_mulVec,
    B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

/-- Each perturbation coefficient solves the corresponding unit-vector system. -/
theorem perturbation_mul (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0)
    (q : Fin n → K) (i k : Fin n) :
    ∑ j, B i j * dictionaryCoefficients B q j k.succ = if i = k then 1 else 0 := by
  simpa only [coefficient_succ, ← Matrix.mul_apply, Matrix.one_apply] using
    congrArg (fun M : Matrix (Fin n) (Fin n) K => M i k)
      (B.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hB))

/-- Right multiplication cancels a scaled inverse row. -/
theorem divided_row_mul (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0)
    (i k : Fin n) (d : K) :
    ∑ j, (B⁻¹ i j / d) * B j k = (if i = k then 1 else 0) / d := by
  simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Matrix.mul_apply, B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB)]
  rfl

/-- Distinct candidate rows cannot tie after division by nonzero directions. -/
theorem divided_coefficients_ne (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) (q : Fin n → K) (d : Fin n → K)
    {i j : Fin n} (hne : i ≠ j) (hi : d i ≠ 0) :
    (fun k => dictionaryCoefficients B q i k / d i) ≠
      (fun k => dictionaryCoefficients B q j k / d j) := by
  intro hij
  have hrows : (fun k => B⁻¹ i k / d i) = (fun k => B⁻¹ j k / d j) := by
    funext k
    exact congrFun hij k.succ
  have hs := congrArg (fun row : Fin n → K => ∑ k, row k * B k i) hrows
  rw [divided_row_mul B hB, divided_row_mul B hB] at hs
  simp only [ite_eq_right (Ne.symm hne), zero_div] at hs
  exact (div_ne_zero one_ne_zero hi) hs

/-- Symbolic ratio vectors are distinct even when their constant terms coincide. -/
theorem divided_coefficients_injective (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) (q : Fin n → K) (d : Fin n → K)
    (hd : ∀ i, d i ≠ 0) :
    Function.Injective (fun i => fun k => dictionaryCoefficients B q i k / d i) := by
  intro i j hij
  by_contra hne
  exact divided_coefficients_ne B hB q d hne (hd i) hij

/-- An invertible basis cannot produce an identically zero perturbation row. -/
theorem coefficients_ne_zero (B : Matrix (Fin n) (Fin n) K) (hB : B.det ≠ 0)
    (q : Fin n → K) (i : Fin n) : dictionaryCoefficients B q i ≠ 0 := by
  intro hz
  have hrow : ∀ k, B⁻¹ i k = 0 := fun k => congrFun hz k.succ
  have hs := divided_row_mul B hB i i (1 : K)
  simp only [hrow, zero_mul, Finset.sum_const_zero, div_one] at hs
  exact zero_ne_one hs

end GameTheory.Math.PerturbedDictionary
