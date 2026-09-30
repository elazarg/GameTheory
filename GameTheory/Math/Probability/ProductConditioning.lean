/-
# Conditioning independent choices on coordinate restrictions

Conditioning an independent product on a rectangle leaves a coordinate whose
restriction is the whole carrier with its own law. When the coordinate laws are
themselves drawn from a latent law, and so correlated, a floor that every
latent value gives one unrestricted coordinate survives the conditioning.
-/

import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Product

noncomputable section

namespace GameTheory.Math.Probability

variable {Index : Type*} [Fintype Index] {A : Index → Type*}

/-- Conditioning independent choices on coordinate restrictions does not
change a coordinate whose restriction is the whole carrier. -/
theorem map_filter_independentProduct_of_unrestricted (laws : (index : Index) → PMF (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (independentProduct laws).support) :
    ((independentProduct laws).filter {values | ∀ index, values index ∈ restriction index}
        positive).map (fun values => values selected) = laws selected := by
  classical
  have coordinate (index : Index) : ∃ value ∈ restriction index,
      value ∈ (laws index).support := by
    obtain ⟨values, permitted, supported⟩ := positive
    exact ⟨values index, permitted index,
      (independentProduct_support_iff laws values).mp supported index⟩
  have event : {values : (index : Index) → A index | ∀ index, values index ∈ restriction index} =
      Set.pi Set.univ restriction := by
    ext values
    simp
  have product := filter_independentProduct laws restriction coordinate
  simp only [← event] at product
  rw [product, independentProduct_map_eval]
  apply filter_of_support_subset
  rw [unrestricted]
  exact Set.subset_univ _

/-- Correlating the prescribed coordinate laws does not lower a common action
floor after conditioning on restrictions of other coordinates. -/
theorem le_prob_filter_mixture_independentProduct {Latent : Type*} (law : PMF Latent)
    (kernel : Latent → (index : Index) → PMF (A index))
    (restriction : (index : Index) → Set (A index)) (selected : Index)
    (unrestricted : restriction selected = Set.univ) (action : A selected) (floor : ℝ)
    (bounded : ∀ latent ∈ law.support, floor ≤ ((kernel latent selected) action).toReal)
    (positive : ∃ values ∈ {values | ∀ index, values index ∈ restriction index},
      values ∈ (law.bind fun latent => independentProduct (kernel latent)).support) :
    floor ≤ ((((law.bind fun latent => independentProduct (kernel latent)).filter
      {values | ∀ index, values index ∈ restriction index} positive).map
        (fun values => values selected)) action).toReal := by
  classical
  let event : Set ((index : Index) → A index) :=
    {values | ∀ index, values index ∈ restriction index}
  let answer : Set ((index : Index) → A index) :=
    (fun values => values selected) ⁻¹' {action}
  have filtered (law : PMF ((index : Index) → A index))
      (meets : ∃ values ∈ event, values ∈ law.support) :
      (((law.filter event meets).map fun values => values selected) action).toReal *
          (law.toOuterMeasure event).toReal =
        (law.toOuterMeasure (event ∩ answer)).toReal := by
    rw [← ENNReal.toReal_mul, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      toOuterMeasure_filter_apply, Set.inter_comm, ENNReal.div_mul_cancel
        ((toOuterMeasure_ne_zero_iff _ _).mpr meets) (outerMeasure_ne_top _ _)]
  have positiveMass (law : PMF ((index : Index) → A index))
      (meets : ∃ values ∈ event, values ∈ law.support) :
      0 < (law.toOuterMeasure event).toReal := by
    exact ENNReal.toReal_pos ((toOuterMeasure_ne_zero_iff _ _).mpr meets)
      (outerMeasure_ne_top _ _)
  have branch (latent : Latent) (supported : latent ∈ law.support) :
      floor * ((independentProduct (kernel latent)).toOuterMeasure event).toReal ≤
        ((independentProduct (kernel latent)).toOuterMeasure (event ∩ answer)).toReal := by
    by_cases reached : ∃ values ∈ event, values ∈ (independentProduct (kernel latent)).support
    · have marginal := map_filter_independentProduct_of_unrestricted (kernel latent)
        restriction selected unrestricted reached
      have lower := bounded latent supported
      rw [← marginal] at lower
      rw [← filtered _ reached]
      exact mul_le_mul_of_nonneg_right lower ENNReal.toReal_nonneg
    · have zero : (independentProduct (kernel latent)).toOuterMeasure event = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        exact Set.disjoint_left.mpr fun values supported member =>
          reached ⟨values, member, supported⟩
      rw [zero, ENNReal.toReal_zero, mul_zero]
      exact ENNReal.toReal_nonneg
  have combined := filtered _ positive
  apply le_of_mul_le_mul_right _ (positiveMass _ positive)
  rw [combined, toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind, ← expect_const_mul]
  have bounds (target : Set ((index : Index) → A index)) :
      PayoffIntegrable law fun latent =>
        ((independentProduct (kernel latent)).toOuterMeasure target).toReal :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun latent => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one _ _)
  exact expect_mono branch
    (payoffIntegrable_of_bounded _ _ (C := |floor|) fun latent => by
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using outerMeasure_le_one _ _))
    (bounds _)

end GameTheory.Math.Probability
