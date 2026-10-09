import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Determinant magnitude bounds for finite integer matrices.
The permutation expansion bounds a determinant by the number of terms times
an entry bound raised to the matrix dimension.
-/
namespace GameTheory.Math
open scoped BigOperators

/-- A determinant is bounded by the number of its permutation terms times their bounds. -/
theorem natAbs_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (K : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ K) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * K ^ Fintype.card ι := by
  classical
  rw [Matrix.det_apply]
  calc
    (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i).natAbs ≤
        ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, K ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [Units.smul_def, zsmul_eq_mul, Int.cast_id, Int.natAbs_mul,
        Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, A (σ i) i) ≤ _
      rw [map_prod]
      simpa using Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hA (σ i) i)
    _ = (Fintype.card ι).factorial * K ^ Fintype.card ι := by simp [Fintype.card_perm]

end GameTheory.Math
