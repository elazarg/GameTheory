module

/-
# Maximality from scalar maximization

A feasible maximizer is maximal in a preorder if every strict improvement of
that point would increase the objective. Strict increase is needed only at the
incumbent, not between arbitrary feasible points. The objective's codomain can
itself be a preorder, and no finite or topological structure is required.
-/

public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Minimal

@[expose] public section

namespace GameTheory.Math

/-- Local strict increase converts scalar maximization into maximality.
Feasibility is explicit because `IsMaxOn` does not include it. -/
theorem maximal_of_isMaxOn {α β : Type*} [Preorder α] [Preorder β]
    {feasible : Set α} {objective : α → β} {chosen : α}
    (maximizes : IsMaxOn objective feasible chosen) (member : chosen ∈ feasible)
    (increases : ∀ alternative ∈ feasible,
      chosen < alternative → objective chosen < objective alternative) :
    Maximal (· ∈ feasible) chosen := by
  refine ⟨member, fun alternative offered weak => ?_⟩
  by_contra reverse
  exact (not_lt_of_ge ((isMaxOn_iff.mp maximizes) alternative offered))
    (increases alternative offered (lt_iff_le_not_ge.mpr ⟨weak, reverse⟩))

end GameTheory.Math
