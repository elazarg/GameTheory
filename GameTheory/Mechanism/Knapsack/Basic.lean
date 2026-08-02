/-
# Real finite-set knapsack semantics

This module adapts the finite allocation and welfare mathematics from
`reference/GameTheory-v1/GameTheory/Auctions/Knapsack/Basic.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.  Boolean allocations are
replaced by `Finset`; the finite universe is explicit until a mechanism needs
the full player universe.
-/

import GameTheory.Mechanism.Knapsack.Aggregate
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

noncomputable section

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

/-- Public real-valued weights and capacity. -/
structure Data (Agent : Type) where
  weight : Agent → ℝ
  capacity : ℝ

/-- Interpret finite-set selection as a real zero/one allocation coordinate. -/
def indicator (selected : Finset Agent) (who : Agent) : ℝ :=
  if who ∈ selected then 1 else 0

/-- A finite-set allocation respects the public capacity. -/
def Feasible (A : Data Agent) (selected : Finset Agent) : Prop :=
  load A.weight selected ≤ A.capacity

/-- Feasible allocations supported by an explicit finite universe. -/
noncomputable def feasibleAllocations (A : Data Agent) (items : Finset Agent) :
    Finset (Finset Agent) := by
  classical
  exact items.powerset.filter (Feasible A)

omit [DecidableEq Agent] in
/-- The empty allocation is feasible whenever capacity is nonnegative. -/
theorem empty_feasible (A : Data Agent) (hcap : 0 ≤ A.capacity) :
    Feasible A ∅ := by
  simpa [Feasible, load, aggregate] using hcap

omit [DecidableEq Agent] in
/-- The explicitly supported feasible-allocation set is nonempty. -/
theorem feasibleAllocations_nonempty (A : Data Agent) (items : Finset Agent)
    (hcap : 0 ≤ A.capacity) : (feasibleAllocations A items).Nonempty := by
  exact ⟨∅, by simp [feasibleAllocations, empty_feasible A hcap]⟩

omit [DecidableEq Agent] in
/-- A finite supported universe has a feasible welfare maximizer. -/
theorem exists_welfareMaximizer (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) :
    ∃ selected ∈ feasibleAllocations A items,
      ∀ alternative ∈ feasibleAllocations A items,
        welfare bids alternative ≤ welfare bids selected :=
  Finset.exists_max_image (feasibleAllocations A items) (welfare bids)
    (feasibleAllocations_nonempty A items hcap)

/-- A chosen feasible welfare maximizer over the explicit universe. -/
noncomputable def welfareMaximizer (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) : Finset Agent :=
  Classical.choose (exists_welfareMaximizer A bids items hcap)

omit [DecidableEq Agent] in
/-- The chosen maximizer belongs to the finite feasible set. -/
theorem welfareMaximizer_mem (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) :
    welfareMaximizer A bids items hcap ∈ feasibleAllocations A items :=
  (Classical.choose_spec (exists_welfareMaximizer A bids items hcap)).1

omit [DecidableEq Agent] in
/-- The chosen allocation weakly dominates every feasible alternative. -/
theorem welfareMaximizer_ge (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) {alternative : Finset Agent}
    (halternative : alternative ∈ feasibleAllocations A items) :
    welfare bids alternative ≤ welfare bids (welfareMaximizer A bids items hcap) :=
  (Classical.choose_spec (exists_welfareMaximizer A bids items hcap)).2
    alternative halternative

omit [DecidableEq Agent] in
/-- The chosen welfare maximizer respects capacity. -/
theorem welfareMaximizer_feasible (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) :
    Feasible A (welfareMaximizer A bids items hcap) := by
  classical
  have hmem := welfareMaximizer_mem A bids items hcap
  simpa [feasibleAllocations] using (Finset.mem_filter.mp hmem).2

/-- Reported welfare achieved by the chosen maximizer. -/
noncomputable def maximalWelfare (A : Data Agent) (bids : Agent → ℝ)
    (items : Finset Agent) (hcap : 0 ≤ A.capacity) : ℝ :=
  welfare bids (welfareMaximizer A bids items hcap)

omit [DecidableEq Agent] in
/-- Membership in `feasibleAllocations` eliminates to capacity feasibility. -/
theorem feasible_of_mem_feasibleAllocations (A : Data Agent)
    (items : Finset Agent) {selected : Finset Agent}
    (hselected : selected ∈ feasibleAllocations A items) : Feasible A selected := by
  classical
  simpa [feasibleAllocations] using (Finset.mem_filter.mp hselected).2

/-- A feasible allocation carries its capacity certificate in the outcome
type consumed by VCG efficiency. -/
abbrev FeasibleAllocation (A : Data Agent) :=
  {selected : Finset Agent // Feasible A selected}

end GameTheory.Mechanism.Knapsack
