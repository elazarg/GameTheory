/-
# Correctness of the executable knapsack approximation frontend

This module proves the checked-input, sorting, support, feasibility, and
attainment properties of `ApproximationAlgorithm`.  The approximation-ratio
proof is built on this structural boundary.
-/

import GameTheory.Mechanism.Knapsack.ApproximationAlgorithm

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type}

/-- On positive weights, the executable comparison is exactly the
cross-multiplied nonincreasing-density relation. -/
theorem densityLE_eq_true_iff_of_pos (weight value : Agent → ℕ)
    {left right : Agent} (hleft : 0 < weight left) (hright : 0 < weight right) :
    densityLE weight value left right = true ↔
      value right * weight left ≤ value left * weight right := by
  simp [densityLE, Nat.ne_of_gt hleft, Nat.ne_of_gt hright]

private theorem densityLE_total (weight value : Agent → ℕ) (left right : Agent) :
    (densityLE weight value left right ||
      densityLE weight value right left) = true := by
  by_cases hleft : weight left = 0
  · simp [densityLE, hleft]
  · by_cases hright : weight right = 0
    · simp [densityLE, hright]
    · simp only [densityLE, hleft, hright, if_false, Bool.or_eq_true,
        decide_eq_true_eq]
      exact le_total _ _

private theorem densityLE_trans (weight value : Agent → ℕ)
    (first second third : Agent)
    (hfirstSecond : densityLE weight value first second = true)
    (hsecondThird : densityLE weight value second third = true) :
    densityLE weight value first third = true := by
  by_cases hfirst : weight first = 0
  · simp [densityLE, hfirst]
  · by_cases hsecond : weight second = 0
    · simp [densityLE, hfirst, hsecond] at hfirstSecond
    · by_cases hthird : weight third = 0
      · simp [densityLE, hsecond, hthird] at hsecondThird
      · have h12 :
            value second * weight first ≤ value first * weight second := by
          simpa [densityLE, hfirst, hsecond] using hfirstSecond
        have h23 :
            value third * weight second ≤ value second * weight third := by
          simpa [densityLE, hsecond, hthird] using hsecondThird
        have hmul :
            (value third * weight first) * weight second ≤
              (value first * weight third) * weight second := by
          calc
            (value third * weight first) * weight second =
                (value third * weight second) * weight first := by ac_rfl
            _ ≤ (value second * weight third) * weight first :=
              Nat.mul_le_mul_right _ h23
            _ = (value second * weight first) * weight third := by ac_rfl
            _ ≤ (value first * weight second) * weight third :=
              Nat.mul_le_mul_right _ h12
            _ = (value first * weight third) * weight second := by ac_rfl
        have h13 :
            value third * weight first ≤ value first * weight third :=
          Nat.le_of_mul_le_mul_right hmul (Nat.pos_of_ne_zero hsecond)
        simpa [densityLE, hfirst, hthird] using h13

/-- Density sorting is a permutation of the explicit input list. -/
theorem sortByDensity_perm (weight value : Agent → ℕ) (items : List Agent) :
    List.Perm (sortByDensity weight value items) items :=
  List.mergeSort_perm _ _

/-- Density sorting preserves duplicate freedom. -/
theorem sortByDensity_nodup (weight value : Agent → ℕ)
    {items : List Agent} (hitems : items.Nodup) :
    (sortByDensity weight value items).Nodup :=
  (List.nodup_mergeSort.mpr hitems)

/-- The executable sorter certifies its own comparison order. -/
theorem sortByDensity_pairwise (weight value : Agent → ℕ) (items : List Agent) :
    (sortByDensity weight value items).Pairwise
      (fun left right => densityLE weight value left right = true) := by
  exact List.pairwise_mergeSort (densityLE_trans weight value)
    (densityLE_total weight value) items

variable [DecidableEq Agent]

omit [DecidableEq Agent] in
/-- Membership in the prefilter is exactly supported membership plus
individual feasibility. -/
@[simp]
theorem mem_feasibleItems (weight : Agent → ℕ) (capacity : ℕ)
    (items : List Agent) (item : Agent) :
    item ∈ feasibleItems weight capacity items ↔
      item ∈ items ∧ weight item ≤ capacity := by
  simp [feasibleItems]

/-- A successful input check reflects duplicate freedom. -/
theorem approximationInputValid_eq_true_iff (items : List Agent) :
    approximationInputValid items = true ↔ items.Nodup := by
  simp [approximationInputValid]

omit [DecidableEq Agent] in
/-- The split data reconstructs the entire scanned list. -/
theorem greedySplit_decomposition (weight : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) :
    items = (greedySplit weight items capacity).taken ++
      (greedySplit weight items capacity).rejected.toList ++
      (greedySplit weight items capacity).rest := by
  induction items generalizing capacity with
  | nil => simp [greedySplit]
  | cons item items ih =>
      by_cases hfit : weight item ≤ capacity
      · simpa only [greedySplit, hfit, if_true, List.cons_append] using
          congrArg (List.cons item) (ih (capacity - weight item))
      · simp [greedySplit, hfit]

omit [DecidableEq Agent] in
/-- The taken-prefix load plus recorded remaining capacity is the input
capacity. -/
theorem greedySplit_sum_weight_add_remaining (weight : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) :
    ((greedySplit weight items capacity).taken.map weight).sum +
        (greedySplit weight items capacity).remaining = capacity := by
  induction items generalizing capacity with
  | nil => simp [greedySplit]
  | cons item items ih =>
      by_cases hfit : weight item ≤ capacity
      · simp only [greedySplit, hfit, if_true, List.map_cons, List.sum_cons]
        have htail := ih (capacity - weight item)
        omega
      · simp [greedySplit, hfit]

omit [DecidableEq Agent] in
/-- The taken list is a sublist of the scanned list. -/
theorem greedySplit_taken_sublist (weight : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) :
    List.Sublist (greedySplit weight items capacity).taken items := by
  induction items generalizing capacity with
  | nil => simp [greedySplit]
  | cons item items ih =>
      by_cases hfit : weight item ≤ capacity
      · simp only [greedySplit, hfit, if_true]
        exact List.Sublist.cons_cons _ (ih (capacity - weight item))
      · simp [greedySplit, hfit]

/-- The greedy prefix is supported by the scanned list. -/
theorem greedyPrefix_subset (weight : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) :
    greedyPrefix weight items capacity ⊆ items.toFinset := by
  intro item hitem
  have htaken : item ∈ (greedySplit weight items capacity).taken := by
    simpa [greedyPrefix] using hitem
  exact List.mem_toFinset.mpr
    ((greedySplit_taken_sublist weight items capacity).mem htaken)

/-- A duplicate-free scan produces a feasible greedy prefix. -/
theorem greedyPrefix_feasible (weight : Agent → ℕ) {items : List Agent}
    (hitems : items.Nodup) (capacity : ℕ) :
    load weight (greedyPrefix weight items capacity) ≤ capacity := by
  have htakenNodup : (greedySplit weight items capacity).taken.Nodup :=
    hitems.sublist (greedySplit_taken_sublist weight items capacity)
  have hsum := greedySplit_sum_weight_add_remaining weight items capacity
  have hload :
      load weight (greedyPrefix weight items capacity) =
        ((greedySplit weight items capacity).taken.map weight).sum := by
    simp [greedyPrefix, load, aggregate, List.sum_toFinset weight htakenNodup]
  rw [hload]
  omega

omit [DecidableEq Agent] in
/-- A reported rejected item is heavier than the recorded remainder. -/
theorem greedySplit_rejected_tooHeavy (weight : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) {rejected : Agent}
    (hrejected : (greedySplit weight items capacity).rejected = some rejected) :
    (greedySplit weight items capacity).remaining < weight rejected := by
  induction items generalizing capacity with
  | nil => simp [greedySplit] at hrejected
  | cons item items ih =>
      by_cases hfit : weight item ≤ capacity
      · simp only [greedySplit, hfit, if_true] at hrejected ⊢
        exact ih (capacity - weight item) hrejected
      · simp only [greedySplit, hfit, if_false] at hrejected ⊢
        cases hrejected
        omega

omit [DecidableEq Agent] in
/-- Every item returned by `bestItem?` came from the input list. -/
theorem bestItem?_mem (value : Agent → ℕ) {items : List Agent} {best : Agent}
    (hbest : bestItem? value items = some best) : best ∈ items := by
  induction items generalizing best with
  | nil => simp [bestItem?] at hbest
  | cons item items ih =>
      simp only [bestItem?] at hbest
      cases htail : bestItem? value items with
      | none =>
          simp [htail] at hbest
          subst best
          exact List.mem_cons_self
      | some tailBest =>
          simp only [htail] at hbest
          by_cases hle : value tailBest ≤ value item
          · simp [hle] at hbest
            subst best
            exact List.mem_cons_self
          · simp [hle] at hbest
            subst best
            exact List.mem_cons_of_mem _ (ih htail)

omit [DecidableEq Agent] in
/-- `bestItem?` returns no item exactly on the empty list. -/
theorem bestItem?_eq_none_iff (value : Agent → ℕ) (items : List Agent) :
    bestItem? value items = none ↔ items = [] := by
  cases items with
  | nil => simp [bestItem?]
  | cons item items =>
      cases htail : bestItem? value items with
      | none => simp [bestItem?, htail]
      | some tailBest =>
          by_cases hle : value tailBest ≤ value item <;>
            simp [bestItem?, htail, hle]

omit [DecidableEq Agent] in
/-- The selected best item weakly dominates every input item by value. -/
theorem le_bestItem? (value : Agent → ℕ) {items : List Agent} {best : Agent}
    (hbest : bestItem? value items = some best) {item : Agent}
    (hitem : item ∈ items) : value item ≤ value best := by
  induction items generalizing best item with
  | nil => simp at hitem
  | cons head items ih =>
      simp only [bestItem?] at hbest
      cases htail : bestItem? value items with
      | none =>
          simp [htail] at hbest
          have hempty : items = [] :=
            (bestItem?_eq_none_iff value items).mp htail
          subst items
          subst best
          simp at hitem
          subst item
          exact le_rfl
      | some tailBest =>
          simp only [htail] at hbest
          by_cases hle : value tailBest ≤ value head
          · simp [hle] at hbest
            subst best
            rcases List.mem_cons.mp hitem with rfl | hitem
            · exact le_rfl
            · exact (ih htail hitem).trans hle
          · simp [hle] at hbest
            subst best
            rcases List.mem_cons.mp hitem with rfl | hitem
            · exact Nat.le_of_not_ge hle
            · exact ih htail hitem

/-- The feasible-singleton candidate is supported by the original list. -/
theorem singletonAllocation_bestItem?_subset (weight value : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) :
    singletonAllocation (bestItem? value (feasibleItems weight capacity items)) ⊆
      items.toFinset := by
  intro item hitem
  cases hbest : bestItem? value (feasibleItems weight capacity items) with
  | none =>
      rw [hbest] at hitem
      simp [singletonAllocation] at hitem
  | some best =>
      have heq : item = best := by simpa [singletonAllocation, hbest] using hitem
      subst item
      exact List.mem_toFinset.mpr
        ((mem_feasibleItems weight capacity items best).mp
          (bestItem?_mem value hbest)).1

omit [DecidableEq Agent] in
/-- The feasible-singleton candidate respects capacity. -/
theorem singletonAllocation_bestItem?_feasible (weight value : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) :
    load weight
        (singletonAllocation (bestItem? value (feasibleItems weight capacity items))) ≤
      capacity := by
  cases hbest : bestItem? value (feasibleItems weight capacity items) with
  | none => simp [singletonAllocation, load, aggregate]
  | some best =>
      have hfeasible :=
        ((mem_feasibleItems weight capacity items best).mp
          (bestItem?_mem value hbest)).2
      simpa [singletonAllocation, hbest, load, aggregate] using hfeasible

omit [DecidableEq Agent] in
/-- `betterAllocation` is supported whenever both candidates are. -/
theorem betterAllocation_subset (value : Agent → ℕ)
    {left right support : Finset Agent} (hleft : left ⊆ support)
    (hright : right ⊆ support) :
    betterAllocation value left right ⊆ support := by
  simp only [betterAllocation]
  split <;> assumption

omit [DecidableEq Agent] in
/-- `betterAllocation` preserves feasibility of both candidates. -/
theorem betterAllocation_feasible (weight value : Agent → ℕ)
    {left right : Finset Agent} {capacity : ℕ}
    (hleft : load weight left ≤ capacity) (hright : load weight right ≤ capacity) :
    load weight (betterAllocation value left right) ≤ capacity := by
  simp only [betterAllocation]
  split <;> assumption

omit [DecidableEq Agent] in
/-- The chosen concrete candidate weakly dominates both inputs by welfare. -/
theorem welfare_le_betterAllocation (value : Agent → ℕ)
    (left right : Finset Agent) :
    welfare value left ≤ welfare value (betterAllocation value left right) ∧
      welfare value right ≤ welfare value (betterAllocation value left right) := by
  simp only [betterAllocation]
  split
  · exact ⟨le_rfl, by assumption⟩
  · exact ⟨Nat.le_of_not_ge (by assumption), le_rfl⟩

/-- The unchecked candidate is supported on the explicit raw item list. -/
theorem approximate_subset (weight value : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) :
    approximate weight value items capacity ⊆ items.toFinset := by
  let eligible := feasibleItems weight capacity items
  let ordered := sortByDensity weight value eligible
  let greedy := greedyPrefix weight ordered capacity
  let singleton := singletonAllocation (bestItem? value eligible)
  have heligible : eligible.toFinset ⊆ items.toFinset := by
    intro item hitem
    exact List.mem_toFinset.mpr
      ((mem_feasibleItems weight capacity items item).mp
        (List.mem_toFinset.mp hitem)).1
  have hordered : ordered.toFinset = eligible.toFinset := by
    exact List.toFinset_eq_of_perm _ _ (sortByDensity_perm weight value eligible)
  apply betterAllocation_subset value
  · exact (greedyPrefix_subset weight ordered capacity).trans
      (by simpa [hordered] using heligible)
  · exact singletonAllocation_bestItem?_subset weight value items capacity

/-- Duplicate-free raw input gives a feasible unchecked candidate. -/
theorem approximate_feasible (weight value : Agent → ℕ) {items : List Agent}
    (hitems : items.Nodup) (capacity : ℕ) :
    load weight (approximate weight value items capacity) ≤ capacity := by
  let eligible := feasibleItems weight capacity items
  let ordered := sortByDensity weight value eligible
  let greedy := greedyPrefix weight ordered capacity
  let singleton := singletonAllocation (bestItem? value eligible)
  have heligibleNodup : eligible.Nodup := hitems.filter _
  have horderedNodup : ordered.Nodup :=
    sortByDensity_nodup weight value heligibleNodup
  exact betterAllocation_feasible weight value
    (greedyPrefix_feasible weight horderedNodup capacity)
    (singletonAllocation_bestItem?_feasible weight value items capacity)

/-- Every successful checked call returns a supported feasible allocation. -/
theorem approximate?_supported_feasible (weight value : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) {selected : Finset Agent}
    (hselected : approximate? weight value items capacity = some selected) :
    selected ⊆ items.toFinset ∧ load weight selected ≤ capacity := by
  unfold approximate? at hselected
  split at hselected <;> rename_i hvalid
  · have hraw : approximate weight value items capacity = selected := by
      simpa using hselected
    subst selected
    have hvalidTrue : approximationInputValid items = true := by
      simpa using hvalid
    exact ⟨approximate_subset weight value items capacity,
      approximate_feasible weight value
        ((approximationInputValid_eq_true_iff items).mp hvalidTrue) capacity⟩
  · simp at hselected

end GameTheory.Mechanism.Knapsack
