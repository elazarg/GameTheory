/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Linear Algebra on Function Spaces

Project-local generic lemmas for linear equivalences between coordinate
function spaces.
-/

namespace Math
namespace LinearAlgebra

/-- A nonzero function points in a coordinate direction when exactly one
coordinate can be nonzero.  No finiteness or decidable equality is needed for
this support-based notion. -/
def IsCoordinateDirection {I R : Type*} [Zero R] (x : I → R) : Prop :=
  ∃ i, x i ≠ 0 ∧ ∀ j, j ≠ i → x j = 0

/-- A function has genuinely multidimensional support when two distinct
coordinates are nonzero. -/
def HasTwoNonzeroCoordinates {I R : Type*} [Zero R] (x : I → R) : Prop :=
  ∃ i j, i ≠ j ∧ x i ≠ 0 ∧ x j ≠ 0

/-- Every nonzero function is either a coordinate direction or has two
distinct nonzero coordinates. -/
theorem isCoordinateDirection_or_hasTwoNonzeroCoordinates
    {I R : Type*} [Zero R] {x : I → R} (hx : x ≠ 0) :
    IsCoordinateDirection x ∨ HasTwoNonzeroCoordinates x := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  by_cases hcoordinate : ∀ j, j ≠ i → x j = 0
  · exact Or.inl ⟨i, hi, hcoordinate⟩
  · push Not at hcoordinate
    obtain ⟨j, hji, hj⟩ := hcoordinate
    exact Or.inr ⟨i, j, hji.symm, hi, hj⟩

/-- Coordinate directions and functions with two nonzero coordinates are
disjoint. -/
theorem HasTwoNonzeroCoordinates.not_isCoordinateDirection
    {I R : Type*} [Zero R] {x : I → R}
    (h : HasTwoNonzeroCoordinates x) : ¬ IsCoordinateDirection x := by
  rintro ⟨k, hk, hzero⟩
  obtain ⟨i, j, hij, hi, hj⟩ := h
  by_cases hik : i = k
  · subst i
    exact hj (hzero j hij.symm)
  · exact hi (hzero i hik)

/-- For a nonzero function, failure to be a coordinate direction is exactly
the existence of two distinct nonzero coordinates. -/
theorem hasTwoNonzeroCoordinates_iff_not_isCoordinateDirection
    {I R : Type*} [Zero R] {x : I → R} (hx : x ≠ 0) :
    HasTwoNonzeroCoordinates x ↔ ¬ IsCoordinateDirection x := by
  constructor
  · exact HasTwoNonzeroCoordinates.not_isCoordinateDirection
  · intro hnot
    exact (isCoordinateDirection_or_hasTwoNonzeroCoordinates hx).resolve_left hnot

/-- The linear functional obtained by pairing a finite coordinate vector with
a fixed normal. -/
noncomputable def normalLinearMap {I R : Type*} [Fintype I] [CommSemiring R]
    (normal : I → R) : (I → R) →ₗ[R] R where
  toFun v := ∑ i, normal i * v i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

@[simp]
theorem normalLinearMap_apply {I R : Type*} [Fintype I] [CommSemiring R]
    (normal v : I → R) :
    normalLinearMap normal v = ∑ i, normal i * v i :=
  rfl

/-- The codimension-at-most-one linear hyperplane tangent to a fixed normal. -/
noncomputable def normalHyperplane {I R : Type*} [Fintype I] [CommSemiring R]
    (normal : I → R) : Submodule R (I → R) :=
  LinearMap.ker (normalLinearMap normal)

@[simp]
theorem mem_normalHyperplane_iff
    {I R : Type*} [Fintype I] [CommSemiring R]
    (normal v : I → R) :
    v ∈ normalHyperplane normal ↔ ∑ i, normal i * v i = 0 :=
  Iff.rfl

/-- Relabeling the coordinates of a family of vectors by an equivalence
preserves and reflects linear independence. -/
theorem linearIndependent_piCongrLeft_iff
    {Y S R I : Type*} [Ring R] {v : I → Y → R} (e : Y ≃ S) :
    LinearIndependent R (fun i =>
      LinearEquiv.piCongrLeft R (fun _ : S => R) e (v i)) ↔
      LinearIndependent R v := by
  let E : (Y → R) ≃ₗ[R] (S → R) :=
    LinearEquiv.piCongrLeft R (fun _ : S => R) e
  constructor
  · intro h
    change LinearIndependent R (E.toLinearMap ∘ v) at h
    exact LinearIndependent.of_comp E.toLinearMap h
  · intro h
    change LinearIndependent R (E.toLinearMap ∘ v)
    exact h.map' E.toLinearMap E.ker

end LinearAlgebra
end Math
