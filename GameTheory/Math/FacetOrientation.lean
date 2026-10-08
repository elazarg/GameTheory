import GameTheory.Math.CanonicalDictionary
import Mathlib.Tactic.LinearCombination

/-! # Orientations of adjacent basis facets

Signed maximal minors of an augmented column matrix form a kernel vector.
When a basis column is replaced, the entering and leaving facets consequently
have opposite orientations, scaled by the entering direction's pivot coordinate.
-/

namespace GameTheory.Math.FacetOrientation

variable {K : Type*} [Field K] {n : ℕ}

/-- Delete one column from an augmented basis matrix. -/
def facetMatrix (C : Matrix (Fin n) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) K := C.submatrix id k.succAbove

/-- The signed maximal minor for a facet of an ordered augmented basis. -/
noncomputable def orientation (C : Matrix (Fin n) (Fin (n + 1)) K)
    (k : Fin (n + 1)) : K := (-1) ^ (k : ℕ) * (facetMatrix C k).det

theorem orientation_ne_zero_iff (C : Matrix (Fin n) (Fin (n + 1)) K)
    (k : Fin (n + 1)) : orientation C k ≠ 0 ↔ (facetMatrix C k).det ≠ 0 := by
  have hsign : (-1 : K) ^ (k : ℕ) ≠ 0 := pow_ne_zero _
    (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero hsign h

/-- Signed maximal minors form a kernel vector. -/
theorem mulVec_orientation (C : Matrix (Fin n) (Fin (n + 1)) K) :
    C.mulVec (orientation C) = 0 := by
  funext i
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Fin.cons (C i) C
  have hz : D.det = 0 := Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm
    ((Fin.cons_zero (α := fun _ => Fin (n + 1) → K) (C i) C).trans
      (Fin.cons_succ (α := fun _ => Fin (n + 1) → K) (C i) C i).symm)
  have he := Matrix.det_succ_row_zero D
  have hm (j : Fin (n + 1)) : D.submatrix Fin.succ j.succAbove = facetMatrix C j := by
    ext a b
    exact congrFun (Fin.cons_succ (α := fun _ => Fin (n + 1) → K) (C i) C a)
      (j.succAbove b)
  simp only [hm] at he
  rw [hz] at he
  change (∑ j, C i j * orientation C j) = 0
  calc
    (∑ j, C i j * orientation C j) =
        ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * D 0 j * (facetMatrix C j).det := by
      apply Finset.sum_congr rfl
      intro j _
      have hzj : D 0 j = C i j :=
        congrFun (Fin.cons_zero (α := fun _ => Fin (n + 1) → K) (C i) C) j
      rw [hzj]
      unfold orientation
      ring
    _ = 0 := he.symm

/-- The facet reached by a pivot has the opposite signed orientation. -/
theorem exchange_orientation (C : Matrix (Fin n) (Fin (n + 1)) K)
    (k : Fin (n + 1)) (l : Fin n) (hB : (facetMatrix C k).det ≠ 0) :
    orientation C (k.succAbove l) =
      -((facetMatrix C k)⁻¹.mulVec (fun i => C i k) l) * orientation C k := by
  let B := facetMatrix C k
  let d := B⁻¹.mulVec (fun i => C i k)
  have hc : B.mulVec d = fun i => C i k := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
      Matrix.one_mulVec]
  have hs : B.mulVec (fun j => orientation C (k.succAbove j)) =
      B.mulVec (fun j => -d j * orientation C k) := by
    funext i
    have hh := congrFun (mulVec_orientation C) i
    change (∑ j, C i j * orientation C j) = 0 at hh
    rw [Fin.sum_univ_succAbove _ k] at hh
    change (∑ j, C i (k.succAbove j) * orientation C (k.succAbove j)) =
      ∑ j, C i (k.succAbove j) * (-d j * orientation C k)
    have hd := congrFun hc i
    change (∑ j, C i (k.succAbove j) * d j) = C i k at hd
    calc
      (∑ j, C i (k.succAbove j) * orientation C (k.succAbove j)) =
          C i k * (-orientation C k) := by linear_combination hh
      _ = (∑ j, C i (k.succAbove j) * d j) * (-orientation C k) := by rw [hd]
      _ = ∑ j, C i (k.succAbove j) * (-d j * orientation C k) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hv := congrArg (fun v => B⁻¹.mulVec v) hs
  simp only [Matrix.mulVec_mulVec,
    B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec] at hv
  change orientation C (k.succAbove l) = -d l * orientation C k
  exact congrFun hv l

section Canonical

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- The augmented columns in increasing label order. -/
def augmentedMatrix (columns : Matrix (Fin n) α K) (S : Finset α) (hS : S.card = n + 1) :
    Matrix (Fin n) (Fin (n + 1)) K := fun i j => columns i (S.orderEmbOfFin hS j)

/-- The position of a selected label in the augmented columns. -/
def labelIndex (S : Finset α) (hS : S.card = n + 1) (a : α) (ha : a ∈ S) : Fin (n + 1) :=
  (S.orderIsoOfFin hS).symm ⟨a, ha⟩

omit [DecidableEq α] in
@[simp] theorem enumeration_labelIndex (S : Finset α) (hS : S.card = n + 1)
    (a : α) (ha : a ∈ S) : S.orderEmbOfFin hS (labelIndex S hS a ha) = a := by
  exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨a, ha⟩)

/-- Signed determinant of the facet omitting the selected label. -/
noncomputable def canonicalOrientation (columns : Matrix (Fin n) α K)
    (S : Finset α) (hS : S.card = n + 1) (a : α) (ha : a ∈ S) : K :=
  orientation (augmentedMatrix columns S hS) (labelIndex S hS a ha)

omit [Field K] in
/-- Deleting an augmented position gives the canonically sorted erased-label basis. -/
theorem facetMatrix_augmented (columns : Matrix (Fin n) α K) (S : Finset α)
    (hS : S.card = n + 1) (k : Fin (n + 1))
    (hE : (S.erase (S.orderEmbOfFin hS k)).card = n) :
    facetMatrix (augmentedMatrix columns S hS) k =
      CanonicalDictionary.basisMatrix columns (S.erase (S.orderEmbOfFin hS k)) hE := by
  have he : (fun j => S.orderEmbOfFin hS (k.succAbove j)) =
      (S.erase (S.orderEmbOfFin hS k)).orderEmbOfFin hE := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr
        ⟨fun hh => Fin.succAbove_ne k j ((S.orderEmbOfFin hS).injective hh),
          Finset.orderEmbOfFin_mem S hS _⟩
    · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove k)
  ext i j
  exact congrArg (columns i) (congrFun he j)

omit [Field K] in
theorem inserted_facet_enumeration (s : Finset α)
    (hs : s.card = n) (a : α) (ha : a ∉ s) :
    (fun j => (insert a s).orderEmbOfFin
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs))
      ((labelIndex (insert a s)
        ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
        (Finset.mem_insert_self _ _)).succAbove j)) = s.orderEmbOfFin hs := by
  let hS : (insert a s).card = n + 1 :=
    (Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)
  let k := labelIndex (insert a s) hS a (Finset.mem_insert_self _ _)
  have hk : (insert a s).orderEmbOfFin hS k = a := enumeration_labelIndex _ _ _ _
  apply Finset.orderEmbOfFin_unique
  · intro j
    have hj : (insert a s).orderEmbOfFin hS (k.succAbove j) ≠ a := by
      exact fun h => Fin.succAbove_ne k j
        (((insert a s).orderEmbOfFin hS).injective (h.trans hk.symm))
    exact (Finset.mem_insert.mp (Finset.orderEmbOfFin_mem (insert a s) hS _)).resolve_left hj
  · exact ((insert a s).orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove k)

omit [Field K] in
theorem inserted_facet (columns : Matrix (Fin n) α K) (s : Finset α)
    (hs : s.card = n) (a : α) (ha : a ∉ s) :
    facetMatrix (augmentedMatrix columns (insert a s)
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)))
      (labelIndex (insert a s)
        ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
        (Finset.mem_insert_self _ _)) = CanonicalDictionary.basisMatrix columns s hs := by
  ext i j
  exact congrArg (columns i) (congrFun (inserted_facet_enumeration s hs a ha) j)

theorem canonicalOrientation_insert (columns : Matrix (Fin n) α K) (s : Finset α)
    (hs : s.card = n) (a : α) (ha : a ∉ s) :
    canonicalOrientation columns (insert a s)
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
      (Finset.mem_insert_self _ _) =
    (-1) ^ (labelIndex (insert a s)
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
      (Finset.mem_insert_self _ _) : ℕ) * (CanonicalDictionary.basisMatrix columns s hs).det := by
  unfold canonicalOrientation orientation
  rw [inserted_facet columns s hs a ha]

theorem canonicalOrientation_insert_ne_zero_iff (columns : Matrix (Fin n) α K)
    (s : Finset α) (hs : s.card = n) (a : α) (ha : a ∉ s) :
    canonicalOrientation columns (insert a s)
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
      (Finset.mem_insert_self _ _) ≠ 0 ↔
      (CanonicalDictionary.basisMatrix columns s hs).det ≠ 0 := by
  rw [canonicalOrientation, orientation_ne_zero_iff, inserted_facet columns s hs a ha]

/-- The entering and leaving canonical facets have opposite orientation at a positive pivot. -/
theorem canonical_exchange_orientation (columns : Matrix (Fin n) α K) (s : Finset α)
    (hs : s.card = n) (a : α) (ha : a ∉ s) (l : Fin n)
    (hB : (CanonicalDictionary.basisMatrix columns s hs).det ≠ 0) :
    canonicalOrientation columns (insert a s)
      ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs))
      (s.orderEmbOfFin hs l) (Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem s hs l)) =
      -((CanonicalDictionary.basisMatrix columns s hs)⁻¹.mulVec (fun i => columns i a) l) *
      canonicalOrientation columns (insert a s)
        ((Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)) a
        (Finset.mem_insert_self _ _) := by
  let hS : (insert a s).card = n + 1 :=
    (Finset.card_insert_of_notMem ha).trans (congrArg (· + 1) hs)
  let k := labelIndex (insert a s) hS a (Finset.mem_insert_self _ _)
  have hslot : labelIndex (insert a s) hS (s.orderEmbOfFin hs l)
      (Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem s hs l)) = k.succAbove l := by
    apply ((insert a s).orderEmbOfFin hS).injective
    exact (enumeration_labelIndex _ _ _ _).trans
      (congrFun (inserted_facet_enumeration s hs a ha) l).symm
  unfold canonicalOrientation
  rw [hslot]
  have hfacet := inserted_facet columns s hs a ha
  have hc : (fun i => augmentedMatrix columns (insert a s) hS i k) =
      fun i => columns i a := by
    funext i
    exact congrArg (columns i) (enumeration_labelIndex _ _ _ _)
  have h := exchange_orientation (augmentedMatrix columns (insert a s) hS) k l
    (by rw [hfacet]; exact hB)
  rw [hfacet, hc] at h
  exact h

end Canonical

end GameTheory.Math.FacetOrientation
