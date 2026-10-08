import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Coordinates after a dictionary pivot

Replacing a basis column changes solution coordinates by a single pivot. The
determinant identity supplies the precise nonzero-pivot condition, without any
ordering or feasibility assumptions.
-/

namespace GameTheory.Math

variable {K : Type*} [Field K] {n : ℕ}

/-- Coordinates after replacing column `l` by a vector with coordinates `d`. -/
def pivotVector (d : Fin n → K) (l : Fin n) (x : Fin n → K) : Fin n → K :=
  fun i => if i = l then x l / d l else x i - d i * (x l / d l)

@[simp] theorem pivotVector_apply_self (d : Fin n → K) (l : Fin n) (x : Fin n → K) :
    pivotVector d l x l = x l / d l := by
  simp [pivotVector]

theorem pivotVector_apply_of_ne (d : Fin n → K) (l : Fin n) (x : Fin n → K)
    {i : Fin n} (hi : i ≠ l) : pivotVector d l x i = x i - d i * (x l / d l) := by
  simp [pivotVector, hi]

theorem updated_det (B : Matrix (Fin n) (Fin n) K) (c : Fin n → K)
    (l : Fin n) (hB : B.det ≠ 0) :
    (B.updateCol l c).det = (B⁻¹.mulVec c l) * B.det := by
  have hc : B.mulVec (B⁻¹.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
      Matrix.one_mulVec]
  calc
    (B.updateCol l c).det = (B.updateCol l (B.mulVec (B⁻¹.mulVec c))).det := by
      rw [hc]
    _ = (B⁻¹.mulVec c l) * B.det := by
      convert B.det_updateCol_sum l (B⁻¹.mulVec c) using 1
      congr 2
      funext i
      simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
      congr 1
      funext j
      exact mul_comm _ _

theorem updated_det_ne_zero (B : Matrix (Fin n) (Fin n) K) (c : Fin n → K)
    (l : Fin n) (hB : B.det ≠ 0) (hd : B⁻¹.mulVec c l ≠ 0) :
    (B.updateCol l c).det ≠ 0 := by
  rw [updated_det B c l hB]
  exact mul_ne_zero hd hB

/-- A pivot transports solutions of the old system to the updated system. -/
theorem updated_mulVec_pivotVector (B : Matrix (Fin n) (Fin n) K)
    (c d x : Fin n → K) (l : Fin n) (hc : B.mulVec d = c) (hd : d l ≠ 0) :
    (B.updateCol l c).mulVec (pivotVector d l x) = B.mulVec x := by
  funext i
  have hterm (j : Fin n) :
      B.updateCol l c i j * pivotVector d l x j =
        B i j * x j - B i j * d j * (x l / d l) +
          if j = l then c i * (x l / d l) else 0 := by
    by_cases hj : j = l
    · subst j
      simp only [Matrix.updateCol_apply, ↓reduceIte, pivotVector_apply_self]
      field_simp
      ring
    · simp only [Matrix.updateCol_apply, hj, ↓reduceIte, pivotVector_apply_of_ne d l x hj]
      ring
  simp only [Matrix.mulVec, dotProduct] at hc ⊢
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hci := congrFun hc i
  change (∑ j, B i j * d j) = c i at hci
  rw [hci]
  ring

/-- The inverse of the updated basis implements the coordinate pivot. -/
theorem updated_inverse_mulVec (B : Matrix (Fin n) (Fin n) K)
    (c : Fin n → K) (l : Fin n) (b : Fin n → K)
    (hB : B.det ≠ 0) (hd : B⁻¹.mulVec c l ≠ 0) :
    (B.updateCol l c)⁻¹.mulVec b = pivotVector (B⁻¹.mulVec c) l (B⁻¹.mulVec b) := by
  have hc : B.mulVec (B⁻¹.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
      Matrix.one_mulVec]
  have hs := updated_mulVec_pivotVector B c (B⁻¹.mulVec c) (B⁻¹.mulVec b) l hc hd
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
    Matrix.one_mulVec] at hs
  have hi := congrArg (fun v => (B.updateCol l c)⁻¹.mulVec v) hs
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (updated_det_ne_zero B c l hB hd)),
    Matrix.one_mulVec] at hi
  exact hi.symm

/-- The leaving column has reciprocal pivot coordinate in the new basis. -/
theorem updated_inverse_oldColumn (B : Matrix (Fin n) (Fin n) K)
    (c : Fin n → K) (l : Fin n) (hB : B.det ≠ 0) (hd : B⁻¹.mulVec c l ≠ 0) :
    (B.updateCol l c)⁻¹.mulVec (fun i => B i l) =
      pivotVector (B⁻¹.mulVec c) l (Pi.single l 1) := by
  rw [updated_inverse_mulVec B c l _ hB hd]
  have he : B⁻¹.mulVec (fun i => B i l) = Pi.single l 1 := by
    change B⁻¹.mulVec (B.col l) = Pi.single l 1
    rw [← Matrix.mulVec_single_one B l, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]
  rw [he]

theorem reverse_pivot_entry (d : Fin n → K) (l : Fin n) :
    pivotVector d l (Pi.single l 1) l = 1 / d l := by
  simp

/-- Replacing the entering column by the old leaving column reverses the pivot. -/
theorem pivotVector_reverse (d : Fin n → K) (l : Fin n) (x : Fin n → K)
    (hd : d l ≠ 0) :
    pivotVector (pivotVector d l (Pi.single l 1)) l (pivotVector d l x) = x := by
  funext i
  by_cases hi : i = l
  · subst i
    simp only [pivotVector_apply_self, Pi.single_eq_same]
    field_simp
  · simp only [pivotVector_apply_of_ne _ _ _ hi, pivotVector_apply_self,
      Pi.single_eq_of_ne hi, Pi.single_eq_same]
    field_simp
    ring

theorem reverse_pivot_entry_ne_zero (d : Fin n → K) (l : Fin n) (hd : d l ≠ 0) :
    pivotVector d l (Pi.single l 1) l ≠ 0 := by
  rw [reverse_pivot_entry]
  exact div_ne_zero one_ne_zero hd

end GameTheory.Math
