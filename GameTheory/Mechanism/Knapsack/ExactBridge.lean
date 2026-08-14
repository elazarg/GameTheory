/-
# Exact knapsack execution/semantics bridge

The executable natural-number solver and the proof-level real-valued selector
may choose different maximizers when there are ties.  Their achieved welfare
is nevertheless identical after the canonical natural-to-real embedding.
-/

import GameTheory.Mechanism.Knapsack.Basic
import GameTheory.Mechanism.Knapsack.Correctness

noncomputable section

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

/-- Natural weights and capacity viewed by the real-valued mechanism layer. -/
def natData (weight : Agent → ℕ) (capacity : ℕ) : Data Agent where
  weight who := weight who
  capacity := capacity

omit [DecidableEq Agent] in
@[simp]
theorem load_natCast (weight : Agent → ℕ) (selected : Finset Agent) :
    load (fun who => (weight who : ℝ)) selected =
      ((aggregate weight selected : ℕ) : ℝ) := by
  simp [load, aggregate]

omit [DecidableEq Agent] in
@[simp]
theorem welfare_natCast (value : Agent → ℕ) (selected : Finset Agent) :
    welfare (fun who => (value who : ℝ)) selected =
      ((aggregate value selected : ℕ) : ℝ) := by
  simp [welfare, aggregate]

/-- Exact execution and noncomputable selection attain the same welfare. -/
theorem solveList_welfare_eq_welfareMaximizer
    (weight value : Agent → ℕ) {agents : List Agent}
    (hnodup : agents.Nodup) (capacity : ℕ) :
    welfare (fun who => (value who : ℝ))
        (solveList weight value agents capacity) =
      welfare (fun who => (value who : ℝ))
        (welfareMaximizer (natData weight capacity)
          (fun who => (value who : ℝ)) agents.toFinset (by
            simp [natData])) := by
  classical
  let A := natData weight capacity
  let bids : Agent → ℝ := fun who => value who
  have hcap : 0 ≤ A.capacity := by simp [A, natData]
  let semantic := welfareMaximizer A bids agents.toFinset hcap
  let computed := solveList weight value agents capacity
  have hcomputedMem : computed ∈ feasibleAllocations A agents.toFinset := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr
        (solveList_subset_toFinset weight value agents capacity)
    · show load (fun who => (weight who : ℝ)) computed ≤ (capacity : ℝ)
      rw [load_natCast]
      exact_mod_cast solveList_feasible weight value hnodup capacity
  have hsemanticMem : semantic ∈ feasibleAllocations A agents.toFinset :=
    welfareMaximizer_mem A bids agents.toFinset hcap
  have hcomputedLe : welfare bids computed ≤ welfare bids semantic := by
    exact welfareMaximizer_ge A bids agents.toFinset hcap hcomputedMem
  have hsemanticSupport : semantic ⊆ agents.toFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hsemanticMem).1
  have hsemanticFeasibleNat : load weight semantic ≤ capacity := by
    have hreal := (Finset.mem_filter.mp hsemanticMem).2
    have hreal' :
        load (fun who => (weight who : ℝ)) semantic ≤ (capacity : ℝ) := hreal
    rw [load_natCast] at hreal'
    exact_mod_cast hreal'
  have hsemanticLeNat : welfare value semantic ≤ welfare value computed :=
    solveList_optimal weight value hnodup capacity
      hsemanticSupport hsemanticFeasibleNat
  have hsemanticLe : welfare bids semantic ≤ welfare bids computed := by
    show welfare (fun who => (value who : ℝ)) semantic ≤
      welfare (fun who => (value who : ℝ)) computed
    rw [welfare_natCast, welfare_natCast]
    exact_mod_cast hsemanticLeNat
  exact le_antisymm hcomputedLe hsemanticLe

end GameTheory.Mechanism.Knapsack
