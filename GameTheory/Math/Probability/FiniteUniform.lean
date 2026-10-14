module

/-
# Uniform probability mass on a finite carrier

A uniform discrete law is a specialization of `PMF.ofFintype`. Its atoms have
mass equal to the inverse cardinality, and every point belongs to its support.
No measurable structure is needed to construct or use the law.
-/

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- Equal probability mass at every point of a nonempty finite carrier. -/
def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ => (Fintype.card α : ENNReal)⁻¹) (by
    simp [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel,
      Fintype.card_ne_zero])

/-- Every atom of the uniform law has the inverse-cardinality mass. -/
@[simp]
theorem uniformLaw_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformLaw α a = (Fintype.card α : ENNReal)⁻¹ := rfl

/-- Every point belongs to the support of the finite uniform law. -/
theorem mem_support_uniformLaw {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    a ∈ (uniformLaw α).support := by
  simp [PMF.mem_support_iff]

/-- Uniform event mass is the fraction of carrier points belonging to the event. -/
theorem uniformLaw_toOuterMeasure_apply {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [DecidablePred (· ∈ s)] :
    (uniformLaw α).toOuterMeasure s =
      ((Finset.univ.filter (· ∈ s)).card : ENNReal) / Fintype.card α := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, uniformLaw_apply]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

end GameTheory.Math.Probability
