/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support

/-!
# Independent products with finitely many random coordinates

An independent product of PMFs over an arbitrary index is again a PMF when all
but finitely many factors are point masses; a product of infinitely many
nondegenerate factors is not. `finitaryProduct laws moving` draws the
coordinates in the finite set `moving` independently and fixes every other
coordinate at a point of its law's support. It is the independent product
whenever the laws outside `moving` are point masses, and for a finite index it
agrees with `independentProduct`.
-/

open scoped BigOperators

namespace GameTheory.Math.Probability

universe uι uA uB

variable {ι : Type uι} {A : ι → Type uA}

/-- A point of a law's support. For a point mass it is the atom. -/
noncomputable def supportPoint {α : Type*} (μ : PMF α) : α :=
  μ.support_nonempty.some

theorem supportPoint_mem_support {α : Type*} (μ : PMF α) :
    supportPoint μ ∈ μ.support :=
  μ.support_nonempty.some_mem

@[simp]
theorem supportPoint_pure {α : Type*} (a : α) : supportPoint (PMF.pure a) = a :=
  (PMF.mem_support_pure_iff _ _).1 (supportPoint_mem_support _)

/-- A law is a point mass. -/
def IsPointMass {α : Type*} (μ : PMF α) : Prop :=
  ∃ a, μ = PMF.pure a

theorem IsPointMass.eq_pure_supportPoint {α : Type*} {μ : PMF α}
    (h : IsPointMass μ) : μ = PMF.pure (supportPoint μ) := by
  obtain ⟨a, rfl⟩ := h
  rw [supportPoint_pure]

theorem isPointMass_of_subsingleton {α : Type*} [Subsingleton α] (μ : PMF α) :
    IsPointMass μ :=
  ⟨supportPoint μ, eq_pure_of_subsingleton μ _⟩

/-- Extend an assignment of the coordinates in `moving` by `fill` elsewhere. -/
noncomputable def extendFrom (moving : Finset ι) (fill : ∀ i, A i)
    (draw : ∀ i : moving, A i) : ∀ i, A i := by
  classical
  exact fun i => if h : i ∈ moving then draw ⟨i, h⟩ else fill i

theorem extendFrom_of_mem {moving : Finset ι} (fill : ∀ i, A i)
    (draw : ∀ i : moving, A i) {i : ι} (h : i ∈ moving) :
    extendFrom moving fill draw i = draw ⟨i, h⟩ := by
  simp [extendFrom, h]

theorem extendFrom_of_not_mem {moving : Finset ι} (fill : ∀ i, A i)
    (draw : ∀ i : moving, A i) {i : ι} (h : i ∉ moving) :
    extendFrom moving fill draw i = fill i := by
  simp [extendFrom, h]

/-- Draw the coordinates in `moving` independently and fix every other
coordinate at a point of its law's support. -/
noncomputable def finitaryProduct (laws : ∀ i, PMF (A i)) (moving : Finset ι) :
    PMF (∀ i, A i) :=
  (independentProduct fun i : moving => laws i).map
    (extendFrom moving fun i => supportPoint (laws i))

open Classical in
theorem finitaryProduct_apply (laws : ∀ i, PMF (A i)) (moving : Finset ι)
    (assignment : ∀ i, A i) :
    finitaryProduct laws moving assignment =
      if ∀ i ∉ moving, assignment i = supportPoint (laws i) then
        ∏ i ∈ moving, laws i (assignment i)
      else 0 := by
  classical
  rw [finitaryProduct, PMF.map_apply]
  split_ifs with hfixed
  · let restricted : ∀ i : moving, A i := fun i => assignment i
    have hextend : extendFrom moving (fun i => supportPoint (laws i)) restricted =
        assignment := by
      funext i
      by_cases hi : i ∈ moving
      · rw [extendFrom_of_mem _ _ hi]
      · rw [extendFrom_of_not_mem _ _ hi, hfixed i hi]
    rw [tsum_eq_single restricted]
    · simp only [hextend, independentProduct_apply, ite_true]
      exact Finset.prod_coe_sort moving fun i => laws i (assignment i)
    · intro other hother
      refine ite_eq_right_iff.mpr fun heq => absurd ?_ hother
      funext i
      show other i = assignment i
      rw [heq, extendFrom_of_mem _ _ i.2]
  · rw [ENNReal.tsum_eq_zero]
    intro draw
    refine ite_eq_right_iff.mpr fun heq => absurd ?_ hfixed
    intro i hi
    rw [heq]
    exact extendFrom_of_not_mem _ _ hi

/-- Enlarging the set of drawn coordinates by point-mass coordinates does not
change the product. -/
theorem finitaryProduct_eq_of_subset (laws : ∀ i, PMF (A i))
    {moving larger : Finset ι} (hsubset : moving ⊆ larger)
    (hpoint : ∀ i ∉ moving, IsPointMass (laws i)) :
    finitaryProduct laws larger = finitaryProduct laws moving := by
  classical
  ext assignment
  rw [finitaryProduct_apply, finitaryProduct_apply]
  by_cases hfixed : ∀ i ∉ moving, assignment i = supportPoint (laws i)
  · have hlarger : ∀ i ∉ larger, assignment i = supportPoint (laws i) :=
      fun i hi => hfixed i fun hm => hi (hsubset hm)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlarger), ite_eq_left_of_eq_true _ _ (eq_true hfixed),
      ← Finset.prod_sdiff hsubset]
    have hone : ∏ i ∈ larger \ moving, laws i (assignment i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hnot : i ∉ moving := (Finset.mem_sdiff.1 hi).2
      rw [hfixed i hnot, (hpoint i hnot).eq_pure_supportPoint]
      simp
    rw [hone, one_mul]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hfixed)]
    push Not at hfixed
    obtain ⟨i, hi, hne⟩ := hfixed
    split_ifs with hlarger
    · have hin : i ∈ larger := by
        by_contra hout
        exact hne (hlarger i hout)
      apply Finset.prod_eq_zero hin
      rw [(hpoint i hi).eq_pure_supportPoint]
      simp [hne]
    · rfl

/-- Over a finite index with every coordinate drawn, the finitary product is
the independent product. -/
theorem finitaryProduct_univ [Fintype ι] (laws : ∀ i, PMF (A i)) :
    finitaryProduct laws Finset.univ = independentProduct laws := by
  ext assignment
  have hfixed : ∀ i ∉ (Finset.univ : Finset ι), assignment i = supportPoint (laws i) :=
    fun i hi => absurd (Finset.mem_univ i) hi
  rw [finitaryProduct_apply, ite_eq_left_of_eq_true _ _ (eq_true hfixed),
    independentProduct_apply]

/-- Over a finite index, the finitary product is the independent product when
the undrawn coordinates are point masses. -/
theorem finitaryProduct_eq_independentProduct [Fintype ι]
    (laws : ∀ i, PMF (A i)) {moving : Finset ι}
    (hpoint : ∀ i ∉ moving, IsPointMass (laws i)) :
    finitaryProduct laws moving = independentProduct laws := by
  rw [← finitaryProduct_eq_of_subset laws (Finset.subset_univ moving) hpoint,
    finitaryProduct_univ]

/-- An assignment is drawable exactly when its drawn coordinates are drawable
and its other coordinates sit at their support points. -/
theorem mem_support_finitaryProduct_iff (laws : ∀ i, PMF (A i))
    (moving : Finset ι) (assignment : ∀ i, A i) :
    assignment ∈ (finitaryProduct laws moving).support ↔
      (∀ i ∉ moving, assignment i = supportPoint (laws i)) ∧
        ∀ i ∈ moving, assignment i ∈ (laws i).support := by
  rw [PMF.mem_support_iff, finitaryProduct_apply]
  split_ifs with hfixed
  · simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and,
      PMF.mem_support_iff]
    exact ⟨fun h => ⟨hfixed, h⟩, fun h => h.2⟩
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h => absurd h hfixed

/-- With point masses outside the drawn coordinates, drawable assignments are
exactly the coordinatewise drawable ones. -/
theorem mem_support_finitaryProduct_iff_of_isPointMass
    (laws : ∀ i, PMF (A i)) {moving : Finset ι}
    (hpoint : ∀ i ∉ moving, IsPointMass (laws i)) (assignment : ∀ i, A i) :
    assignment ∈ (finitaryProduct laws moving).support ↔
      ∀ i, assignment i ∈ (laws i).support := by
  rw [mem_support_finitaryProduct_iff]
  constructor
  · rintro ⟨hfixed, hdrawn⟩ i
    by_cases hi : i ∈ moving
    · exact hdrawn i hi
    · rw [hfixed i hi]
      exact supportPoint_mem_support _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    have := h i
    rw [(hpoint i hi).eq_pure_supportPoint, PMF.mem_support_pure_iff] at this
    exact this

/-- Point masses give the point mass at their atoms. -/
theorem finitaryProduct_pure (assignment : ∀ i, A i) (moving : Finset ι) :
    finitaryProduct (fun i => PMF.pure (assignment i)) moving =
      PMF.pure assignment := by
  classical
  ext other
  rw [finitaryProduct_apply, PMF.pure_apply]
  simp only [supportPoint_pure, PMF.pure_apply]
  by_cases h : other = assignment
  · subst h
    simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    split_ifs with hfixed
    · have hcoord : ∃ i ∈ moving, other i ≠ assignment i := by
        by_contra hall
        push Not at hall
        apply h
        funext i
        by_cases hi : i ∈ moving
        · exact hall i hi
        · exact hfixed i hi
      obtain ⟨i, hi, hne⟩ := hcoord
      exact Finset.prod_eq_zero hi (by simp [hne])
    · rfl

/-- Mapping every coordinate commutes with the finitary product when the
undrawn coordinates are point masses. -/
theorem finitaryProduct_map {B : ι → Type uB} (laws : ∀ i, PMF (A i))
    (f : ∀ i, A i → B i) {moving : Finset ι}
    (hpoint : ∀ i ∉ moving, IsPointMass (laws i)) :
    (finitaryProduct laws moving).map (fun assignment i => f i (assignment i)) =
      finitaryProduct (fun i => (laws i).map (f i)) moving := by
  classical
  rw [finitaryProduct, finitaryProduct, PMF.map_comp,
    ← independentProduct_map (fun i : moving => laws i) (fun i => f i), PMF.map_comp]
  congr 1
  funext draw
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i ∈ moving
  · rw [extendFrom_of_mem _ _ hi, extendFrom_of_mem _ _ hi]
  · rw [extendFrom_of_not_mem _ _ hi, extendFrom_of_not_mem _ _ hi,
      (hpoint i hi).eq_pure_supportPoint, PMF.pure_map, supportPoint_pure,
      supportPoint_pure]

/-- Drawing one coordinate first and fixing it as a point mass gives the same
product, when that coordinate is drawn or its law is a point mass. -/
theorem finitaryProduct_update_bind [DecidableEq ι] (laws : ∀ i, PMF (A i))
    {moving : Finset ι} {who : ι} (law : PMF (A who))
    (hwho : who ∈ moving ∨ IsPointMass law) :
    finitaryProduct (Function.update laws who law) moving =
      law.bind fun choice =>
        finitaryProduct (Function.update laws who (PMF.pure choice)) moving := by
  classical
  rcases hwho with hwho | ⟨atom, rfl⟩
  · ext assignment
    rw [PMF.bind_apply]
    have hfixed (μ : PMF (A who)) :
        (∀ i ∉ moving, assignment i = supportPoint (Function.update laws who μ i)) ↔
          ∀ i ∉ moving, assignment i = supportPoint (laws i) := by
      refine forall₂_congr fun i hi => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hwho hi).symm]
    have hproduct (μ : PMF (A who)) :
        ∏ i ∈ moving, Function.update laws who μ i (assignment i) =
          μ (assignment who) * ∏ i ∈ moving.erase who, laws i (assignment i) := by
      rw [← Finset.mul_prod_erase moving _ hwho, Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    simp only [finitaryProduct_apply, hfixed, hproduct]
    split_ifs
    · rw [tsum_eq_single (assignment who)]
      · simp [PMF.pure_apply]
      · intro choice hchoice
        simp [PMF.pure_apply, Ne.symm hchoice]
    · simp
  · rw [PMF.pure_bind]

/-- A drawn coordinate, or a point-mass one, keeps its own law as marginal. -/
theorem finitaryProduct_map_eval (laws : ∀ i, PMF (A i)) (moving : Finset ι)
    (j : ι) (hj : j ∈ moving ∨ IsPointMass (laws j)) :
    (finitaryProduct laws moving).map (fun assignment => assignment j) = laws j := by
  classical
  rw [finitaryProduct, PMF.map_comp]
  by_cases hmem : j ∈ moving
  · have hread : (fun assignment => assignment j) ∘
        extendFrom moving (fun i => supportPoint (laws i)) =
          fun draw : (∀ i : moving, A i) => draw ⟨j, hmem⟩ := by
      funext draw
      exact extendFrom_of_mem (fun i => supportPoint (laws i)) draw hmem
    rw [hread]
    exact independentProduct_map_eval (fun i : moving => laws i) ⟨j, hmem⟩
  · have hpoint := hj.resolve_left hmem
    have hread : (fun assignment => assignment j) ∘
        extendFrom moving (fun i => supportPoint (laws i)) =
          fun _ => supportPoint (laws j) := by
      funext draw
      exact extendFrom_of_not_mem (fun i => supportPoint (laws i)) draw hmem
    rw [hread, show (fun _ => supportPoint (laws j)) =
        Function.const _ (supportPoint (laws j)) from rfl,
      PMF.map_const, ← hpoint.eq_pure_supportPoint]

end GameTheory.Math.Probability
