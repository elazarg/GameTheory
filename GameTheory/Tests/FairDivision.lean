/-
# Hostile finite fair-division fixture

Two agents disagree on the best of three goods.  The complete disjoint
allocation below is not envy-free: agent one envies a two-good bundle, and EF1
is witnessed only after removing a positively valued good.  The same values
also specialize the general canonical round-robin completeness and EF1
theorems.
-/

import GameTheory.Mechanism.FairDivision
import Mathlib.Tactic.Linarith

noncomputable section

namespace GameTheory.Tests.FairDivision

open GameTheory.Mechanism.FairDivision

/-- Agent zero most values good zero; agent one most values good one. -/
def values (agent : Fin 2) (good : Fin 3) : ℝ :=
  if agent = 0 then
    if good = 0 then 10 else if good = 1 then 3 else 2
  else
    if good = 0 then 7 else if good = 1 then 8 else 3

private theorem two_ne_zero : (2 : Fin 3) ≠ 0 := by decide

theorem values_nonnegative : Nonnegative values := by
  intro agent good
  fin_cases agent <;> fin_cases good <;> simp [values, two_ne_zero]

theorem rankings_conflict :
    values 0 1 < values 0 0 ∧ values 1 0 < values 1 1 := by
  constructor <;> simp [values] <;> linarith

/-- Agent zero receives goods zero and two; agent one receives good one. -/
def allocation : Allocation (Fin 2) (Fin 3) where
  bundle agent := if agent = 0 then {0, 2} else {1}
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem allocation_complete : IsComplete allocation := by
  intro good
  fin_cases good
  · exact ⟨0, by simp [allocation]⟩
  · exact ⟨1, by simp [allocation]⟩
  · exact ⟨0, by simp [allocation]⟩

theorem agent_one_strictly_envies :
    value values 1 (allocation 1) < value values 1 (allocation 0) := by
  simp [value, allocation, values, two_ne_zero]
  linarith

theorem allocation_not_envyFree : ¬ IsEnvyFree values allocation := by
  intro hef
  exact (not_le_of_gt agent_one_strictly_envies) (hef 1 0)

/-- The envy is genuine but disappears after removing good zero, which agent
one values positively. -/
theorem agent_one_ef1_witness :
    0 ∈ allocation 0 ∧ 0 < values 1 0 ∧
      value values 1 ((allocation 0).erase 0) ≤ value values 1 (allocation 1) := by
  simp [value, allocation, values, two_ne_zero]
  linarith

theorem allocation_isEF1 : IsEF1 values allocation := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Or.inl le_rfl
  · exact Or.inl (by
      simp [value, allocation, values, two_ne_zero]
      linarith)
  · exact Or.inr ⟨0, by simp [allocation], by
      simp [value, allocation, values, two_ne_zero]
      linarith⟩
  · exact Or.inl le_rfl

/-- The generic algorithm produces a complete canonical allocation on the
same conflicting-value instance. -/
theorem roundRobin_complete : IsComplete (roundRobinAllocation values) :=
  roundRobinAllocation_isComplete values

/-- The release flagship specializes to the hostile value profile. -/
theorem roundRobin_isEF1 : IsEF1 values (roundRobinAllocation values) :=
  roundRobinAllocation_isEF1 values values_nonnegative

end GameTheory.Tests.FairDivision
