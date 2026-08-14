/-
Correctness guarantees for the explicit-list knapsack solver.
-/

import GameTheory.Mechanism.Knapsack.Algorithm

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

/-- The solver selects only agents from its explicit input list. -/
theorem solveList_subset_toFinset (weight value : Agent → ℕ)
    (agents : List Agent) (capacity : ℕ) :
    solveList weight value agents capacity ⊆ agents.toFinset := by
  induction agents generalizing capacity with
  | nil => simp [solveList]
  | cons agent agents ih =>
      by_cases hfit : weight agent ≤ capacity
      · by_cases htake :
          welfare value (solveList weight value agents capacity) ≤
            welfare value
              (insert agent
                (solveList weight value agents (capacity - weight agent)))
        · simpa [solveList, hfit, htake] using
            Finset.insert_subset_insert agent
              (ih (capacity - weight agent))
        · simpa [solveList, hfit, htake] using
            (ih capacity).trans (Finset.subset_insert agent agents.toFinset)
      · simpa [solveList, hfit] using
          (ih capacity).trans (Finset.subset_insert agent agents.toFinset)

/-- Every duplicate-free run returns a capacity-feasible allocation. -/
theorem solveList_feasible (weight value : Agent → ℕ)
    {agents : List Agent} (hnodup : agents.Nodup) (capacity : ℕ) :
    load weight (solveList weight value agents capacity) ≤ capacity := by
  induction hnodup generalizing capacity with
  | nil => simp [solveList, load, aggregate]
  | @cons agent agents hnotmem _ ih =>
      have hagentNotMem : agent ∉ agents := by
        intro hmem
        exact hnotmem agent hmem rfl
      by_cases hfit : weight agent ≤ capacity
      · let skip := solveList weight value agents capacity
        let tail := solveList weight value agents (capacity - weight agent)
        let take := insert agent tail
        have hagentTail : agent ∉ tail := by
          intro hmem
          have hsub := solveList_subset_toFinset weight value agents
            (capacity - weight agent) hmem
          exact hagentNotMem (List.mem_toFinset.mp hsub)
        have htakeFeasible : load weight take ≤ capacity := by
          have htail : load weight tail ≤ capacity - weight agent := by
            simpa [tail] using ih (capacity - weight agent)
          calc
            load weight take = weight agent + load weight tail := by
              simp [take, load, aggregate, hagentTail]
            _ ≤ capacity := by omega
        by_cases htake : welfare value skip ≤ welfare value take
        · simpa [solveList, hfit, skip, tail, take, htake] using htakeFeasible
        · simpa [solveList, hfit, skip, tail, take, htake] using ih capacity
      · simpa [solveList, hfit] using ih capacity

/-- The solver maximizes value among all feasible selections supported by its
explicit duplicate-free list. -/
theorem solveList_optimal (weight value : Agent → ℕ)
    {agents : List Agent} (hnodup : agents.Nodup) (capacity : ℕ)
    {selected : Finset Agent} (hsupport : selected ⊆ agents.toFinset)
    (hfeasible : load weight selected ≤ capacity) :
    welfare value selected ≤
      welfare value (solveList weight value agents capacity) := by
  induction hnodup generalizing capacity selected with
  | nil =>
      have hempty : selected = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro agent hmem
        simpa using hsupport hmem
      simp [hempty, solveList, welfare]
  | @cons agent agents hnotmem _ ih =>
      have hagentNotMem : agent ∉ agents := by
        intro hmem
        exact hnotmem agent hmem rfl
      by_cases hfit : weight agent ≤ capacity
      · let skip := solveList weight value agents capacity
        let tail := solveList weight value agents (capacity - weight agent)
        let take := insert agent tail
        have hagentTail : agent ∉ tail := by
          intro hmem
          have hsub := solveList_subset_toFinset weight value agents
            (capacity - weight agent) hmem
          exact hagentNotMem (List.mem_toFinset.mp hsub)
        have hskipOptimal :
            ∀ {selection : Finset Agent}, selection ⊆ agents.toFinset →
              load weight selection ≤ capacity →
                welfare value selection ≤ welfare value skip := by
          intro selection hsub hload
          exact ih capacity hsub hload
        have htailOptimal :
            ∀ {selection : Finset Agent}, selection ⊆ agents.toFinset →
              load weight selection ≤ capacity - weight agent →
                welfare value selection ≤ welfare value tail := by
          intro selection hsub hload
          exact ih (capacity - weight agent) hsub hload
        have hselected : selected ⊆ insert agent agents.toFinset := by
          simpa using hsupport
        have hbound : welfare value selected ≤ max (welfare value skip)
            (welfare value take) := by
          by_cases hmem : agent ∈ selected
          · have htailSupport : selected.erase agent ⊆ agents.toFinset := by
              intro other hother
              have hotherNe : other ≠ agent := (Finset.mem_erase.mp hother).1
              have hotherSelected : other ∈ selected := Finset.mem_of_mem_erase hother
              simpa [hotherNe] using hselected hotherSelected
            have hloadSplit :
                load weight selected =
                  load weight (selected.erase agent) + weight agent := by
              unfold load
              exact (Finset.sum_erase_add _ _ hmem).symm
            have htailFeasible :
                load weight (selected.erase agent) ≤ capacity - weight agent := by
              omega
            have htailBound := htailOptimal htailSupport htailFeasible
            have hwelfareSplit :
                welfare value selected =
                  welfare value (selected.erase agent) + value agent := by
              unfold welfare
              exact (Finset.sum_erase_add _ _ hmem).symm
            have htakeValue :
                welfare value take = welfare value tail + value agent := by
              simp [take, welfare, aggregate, hagentTail, Nat.add_comm]
            rw [hwelfareSplit, htakeValue]
            exact le_trans (Nat.add_le_add_right htailBound _)
              (le_max_right _ _)
          · have hskipSupport : selected ⊆ agents.toFinset := by
              intro other hother
              have hotherNe : other ≠ agent := by
                intro heq
                subst other
                exact hmem hother
              simpa [hotherNe] using hselected hother
            exact le_trans (hskipOptimal hskipSupport hfeasible)
              (le_max_left _ _)
        by_cases htake : welfare value skip ≤ welfare value take
        · have hmax : max (welfare value skip) (welfare value take) =
              welfare value take := max_eq_right htake
          simpa [solveList, hfit, skip, tail, take, htake, hmax] using hbound
        · have hmax : max (welfare value skip) (welfare value take) =
              welfare value skip := max_eq_left (Nat.le_of_lt (lt_of_not_ge htake))
          simpa [solveList, hfit, skip, tail, take, htake, hmax] using hbound
      · have hnotSelected : agent ∉ selected := by
          intro hmem
          have hloadSplit :
              load weight selected =
                load weight (selected.erase agent) + weight agent := by
            unfold load
            exact (Finset.sum_erase_add _ _ hmem).symm
          have : weight agent ≤ capacity := by omega
          exact hfit this
        have htailSupport : selected ⊆ agents.toFinset := by
          intro other hother
          have hotherNe : other ≠ agent := by
            intro heq
            subst other
            exact hnotSelected hother
          have hselected : selected ⊆ insert agent agents.toFinset := by
            simpa using hsupport
          simpa [hotherNe] using hselected hother
        simpa [solveList, hfit] using ih capacity htailSupport hfeasible

end GameTheory.Mechanism.Knapsack
