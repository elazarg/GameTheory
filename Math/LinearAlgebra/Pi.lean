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

/-- Two distinct coordinates have absolute value at least a prescribed
margin.  This quantitative support condition is independent of finiteness. -/
def HasTwoCoordinatesWithAbsAtLeast
    {I R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    (margin : R) (x : I → R) : Prop :=
  ∃ i j, i ≠ j ∧ margin ≤ |x i| ∧ margin ≤ |x j|

/-- A positive quantitative support margin supplies two nonzero
coordinates. -/
theorem HasTwoCoordinatesWithAbsAtLeast.hasTwoNonzeroCoordinates
    {I R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    {margin : R} {x : I → R}
    (h : HasTwoCoordinatesWithAbsAtLeast margin x) (hmargin : 0 < margin) :
    HasTwoNonzeroCoordinates x := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  refine ⟨i, j, hij, ?_, ?_⟩
  · intro hzero
    rw [hzero, abs_zero] at hi
    exact (not_le_of_gt hmargin) hi
  · intro hzero
    rw [hzero, abs_zero] at hj
    exact (not_le_of_gt hmargin) hj

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

/-- The affine level set of the linear functional determined by `normal`. -/
noncomputable def normalAffineHyperplane
    {I R : Type*} [Fintype I] [CommSemiring R]
    (normal : I → R) (level : R) : Set (I → R) :=
  {v | normalLinearMap normal v = level}

@[simp]
theorem mem_normalAffineHyperplane_iff
    {I R : Type*} [Fintype I] [CommSemiring R]
    (normal v : I → R) (level : R) :
    v ∈ normalAffineHyperplane normal level ↔
      ∑ i, normal i * v i = level :=
  Iff.rfl

/-- Over a field, pairing with a nonzero finite normal is a surjective linear
functional. -/
theorem normalLinearMap_surjective_of_ne_zero
    {I R : Type*} [Fintype I] [Field R]
    {normal : I → R} (hnormal : normal ≠ 0) :
    Function.Surjective (normalLinearMap normal) := by
  classical
  have hex : ∃ i, normal i ≠ 0 := by
    by_contra h
    apply hnormal
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  intro level
  refine ⟨Pi.single i (level / normal i), ?_⟩
  rw [normalLinearMap_apply, Finset.sum_eq_single i]
  · simp [mul_div_cancel₀ level hi]
  · intro j _ hji
    simp [hji]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

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
