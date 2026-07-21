/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Finite Coordinate-Sum Subspaces

The coordinate-sum linear map on a finite function space, its kernel, and the
codimension-one formula for that kernel over a division ring.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace LinearAlgebra

/-- Sum of the coordinates of a finite vector, as a linear map. -/
def coordinateSumLinearMap (R : Type*) [Semiring R]
    (S : Type*) [Fintype S] : (S → R) →ₗ[R] R :=
  { toFun := fun v => ∑ s, v s
    map_add' := fun v w => by
      change (∑ s, (v s + w s)) = (∑ s, v s) + ∑ s, w s
      exact Finset.sum_add_distrib
    map_smul' := fun c v => by
      change (∑ s, c * v s) = c * ∑ s, v s
      simpa using
        (Finset.mul_sum Finset.univ (fun s => v s) c).symm }

/-- Finite vectors whose coordinates sum to zero. -/
def zeroSumSubspace (R : Type*) [Semiring R]
    (S : Type*) [Fintype S] : Submodule R (S → R) :=
  LinearMap.ker (coordinateSumLinearMap R S)

@[simp]
theorem mem_zeroSumSubspace_iff
    {R S : Type*} [Semiring R] [Fintype S] (v : S → R) :
    v ∈ zeroSumSubspace R S ↔ ∑ s, v s = 0 := by
  simp [zeroSumSubspace, coordinateSumLinearMap]

/-- Over a division ring, the zero-sum subspace on a nonempty finite carrier
has codimension one. -/
theorem finrank_zeroSumSubspace
    (K : Type*) [DivisionRing K] (S : Type*) [Fintype S] [Nonempty S] :
    Module.finrank K (zeroSumSubspace K S) = Fintype.card S - 1 := by
  classical
  let L : (S → K) →ₗ[K] K := coordinateSumLinearMap K S
  have hrange : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro x
    let s : S := Classical.choice inferInstance
    refine ⟨Pi.single s x, ?_⟩
    simp [L, coordinateSumLinearMap]
  have hdim := L.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hdim
  change Module.finrank K (LinearMap.ker L) = Fintype.card S - 1
  omega

end LinearAlgebra
end Math
