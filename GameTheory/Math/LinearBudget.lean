module

/-
# Lower hemicontinuity of positive linear budgets

Radially shrinking a feasible bundle toward zero recovers feasibility at
nearby parameters. Positive wealth makes the shrinking factor continuous,
including when the cost of some bundle or coordinate is zero or negative.
-/

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section

namespace GameTheory.Math

open Set Filter Topology

/-- A positive continuous wealth bound on linear costs gives a lower
hemicontinuous budget correspondence inside a fixed convex set containing
zero. Cost continuity is required only for each fixed bundle. -/
theorem lowerHemicontinuous_linearBudget
    {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E]
    (allowed : Set E) (convex : Convex ℝ allowed) (zero_mem : (0 : E) ∈ allowed)
    (cost : X → E →ₗ[ℝ] ℝ)
    (continuous_cost : ∀ bundle, Continuous (fun x => cost x bundle))
    (wealth : X → ℝ) (continuous_wealth : Continuous wealth)
    (wealth_positive : ∀ x, 0 < wealth x) :
    LowerHemicontinuous (fun x => {bundle | bundle ∈ allowed ∧ cost x bundle ≤ wealth x}) := by
  intro reference
  apply lowerHemicontinuousAt_iff.mpr
  rintro openSet isOpenSet ⟨bundle, feasible, offered⟩
  let denominator (x : X) : ℝ := max (wealth x) (cost x bundle)
  let factor (x : X) : ℝ := wealth x / denominator x
  have denominator_positive (x : X) : 0 < denominator x :=
    (wealth_positive x).trans_le (le_max_left _ _)
  have factor_positive (x : X) : 0 < factor x :=
    div_pos (wealth_positive x) (denominator_positive x)
  have factor_le_one (x : X) : factor x ≤ 1 :=
    (div_le_one (denominator_positive x)).mpr (le_max_left _ _)
  have factor_continuous : Continuous factor :=
    continuous_wealth.div (continuous_wealth.max (continuous_cost bundle))
      (fun x => (denominator_positive x).ne')
  have recovery_continuous : Continuous (fun x => factor x • bundle) :=
    factor_continuous.smul continuous_const
  have recovery_reference : factor reference • bundle = bundle := by
    have denominator_reference : denominator reference = wealth reference :=
      max_eq_left feasible.2
    change (wealth reference / denominator reference) • bundle = bundle
    rw [denominator_reference, div_self (wealth_positive reference).ne', one_smul]
  have recovery_allowed (x : X) : factor x • bundle ∈ allowed :=
    convex.smul_mem_of_zero_mem zero_mem feasible.1
      ⟨(factor_positive x).le, factor_le_one x⟩
  have recovery_affordable (x : X) : cost x (factor x • bundle) ≤ wealth x := by
    calc
      cost x (factor x • bundle) = factor x * cost x bundle := by
        simp only [map_smul, smul_eq_mul]
      _ ≤ factor x * denominator x :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (factor_positive x).le
      _ = wealth x := div_mul_cancel₀ _ (denominator_positive x).ne'
  have recovery_offered : factor reference • bundle ∈ openSet := by
    rw [recovery_reference]
    exact offered
  filter_upwards [(recovery_continuous.tendsto reference).eventually
    (isOpenSet.mem_nhds recovery_offered)] with next recovered
  exact ⟨factor next • bundle, ⟨recovery_allowed next, recovery_affordable next⟩, recovered⟩

end GameTheory.Math
