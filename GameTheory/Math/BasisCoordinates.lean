import GameTheory.Math.CanonicalDictionary
import GameTheory.Math.FiniteLexicographic

/-! Coordinates on a basis lifted to the full variable universe.

Nonbasic variables are zero. Canonically enumerated basis coordinates retain
their values, and an invertible basis gives a solution of the ambient equations.
-/

namespace GameTheory.Math.BasisCoordinates
open scoped BigOperators
open GameTheory.Math.CanonicalDictionary

variable {α K : Type*} [LinearOrder α] [Field K] {n : ℕ}

/-- Extend basis coordinates by zero on nonbasic variables. -/
def lift (s : Finset α) (hs : s.card = n) (x : Fin n → K) (v : α) : K :=
  if hv : v ∈ s then x ((s.orderIsoOfFin hs).symm ⟨v, hv⟩) else 0

@[simp] theorem lift_on_enumeration (s : Finset α) (hs : s.card = n)
    (x : Fin n → K) (j : Fin n) : lift s hs x (s.orderEmbOfFin hs j) = x j := by
  unfold lift
  rw [dite_eq_left (Finset.orderEmbOfFin_mem s hs j)]
  have hh : (⟨s.orderEmbOfFin hs j, Finset.orderEmbOfFin_mem s hs j⟩ : s) =
      s.orderIsoOfFin hs j := rfl
  rw [hh, OrderIso.symm_apply_apply]

theorem lift_outside (s : Finset α) (hs : s.card = n) (x : Fin n → K)
    (v : α) (hv : v ∉ s) : lift s hs x v = 0 := by
  simp only [lift, dite_eq_right hv]

/-- Weighted sums of lifted coordinates are the basis matrix product. -/
theorem sum_columns_lift [Fintype α] (columns : Matrix (Fin n) α K)
    (s : Finset α) (hs : s.card = n) (x : Fin n → K) (i : Fin n) :
    ∑ v, columns i v * lift s hs x v = (basisMatrix columns s hs).mulVec x i := by
  have hsum : ∑ v, columns i v * lift s hs x v =
      ∑ v ∈ s, columns i v * lift s hs x v := by
    exact (Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => by
      rw [lift_outside s hs x v hv, mul_zero])).symm
  rw [hsum]
  have himage := congrArg (fun t : Finset α => ∑ v ∈ t, columns i v * lift s hs x v)
    (Finset.image_orderEmbOfFin_univ s hs)
  rw [← himage]
  have hmap := Finset.sum_image (s := Finset.univ) (g := s.orderEmbOfFin hs)
    (f := fun v : α => columns i v * lift s hs x v)
    (fun _ _ _ _ h => (s.orderEmbOfFin hs).injective h)
  refine hmap.trans ?_
  simp only [lift_on_enumeration, basisMatrix, Matrix.mulVec, dotProduct]

/-- The inverse-basis solution, with all nonbasic variables set to zero. -/
noncomputable def inverseCoordinates (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) : α → K :=
  lift s hs ((basisMatrix columns s hs)⁻¹.mulVec q)

@[simp] theorem inverseCoordinates_on_enumeration (columns : Matrix (Fin n) α K)
    (q : Fin n → K) (s : Finset α) (hs : s.card = n) (j : Fin n) :
    inverseCoordinates columns q s hs (s.orderEmbOfFin hs j) =
      (basisMatrix columns s hs)⁻¹.mulVec q j :=
  lift_on_enumeration _ _ _ _

theorem inverseCoordinates_outside (columns : Matrix (Fin n) α K) (q : Fin n → K)
    (s : Finset α) (hs : s.card = n) (v : α) (hv : v ∉ s) :
    inverseCoordinates columns q s hs v = 0 :=
  lift_outside _ _ _ _ hv

/-- Lifted inverse coordinates solve the original ambient linear system. -/
theorem inverseCoordinates_equation [Fintype α] (columns : Matrix (Fin n) α K)
    (q : Fin n → K) (s : Finset α) (hs : s.card = n)
    (hdet : (basisMatrix columns s hs).det ≠ 0) (i : Fin n) :
    ∑ v, columns i v * inverseCoordinates columns q s hs v = q i := by
  rw [inverseCoordinates, sum_columns_lift, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- Nonnegative basis coordinates stay nonnegative after lifting. -/
theorem lift_nonneg (s : Finset α) (hs : s.card = n) (x : Fin n → K)
    (hx : ∀ j, 0 ≤ x j) : ∀ v, 0 ≤ lift s hs x v := by
  intro v
  unfold lift
  split
  · exact hx _
  · exact le_rfl

omit [IsStrictOrderedRing K] in
/-- Symbolic feasibility yields a nonnegative solution of the original system. -/
theorem inverseCoordinates_nonneg_of_feasible (columns : Matrix (Fin n) α K)
    (q : Fin n → K) (s : Finset α) (hs : s.card = n)
    (h : IsFeasible columns q s hs) : ∀ v, 0 ≤ inverseCoordinates columns q s hs v := by
  apply lift_nonneg
  intro j
  exact FiniteLexicographic.constant_nonneg (h.2 j).le

end Ordered
end GameTheory.Math.BasisCoordinates
