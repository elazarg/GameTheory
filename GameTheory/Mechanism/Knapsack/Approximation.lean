/-
# Executable knapsack half approximation

This module proves a division-free finite exchange bound and connects it to
the actual feasible allocation returned by the checked executable frontend.

For the monotone half-approximation underlying this construction, see
A. Mu'alem and N. Nisan, “Truthful Approximation Mechanisms for Restricted
Combinatorial Auctions,” *Games and Economic Behavior* 64 (2008).
-/

import GameTheory.Mechanism.Knapsack.ApproximationCorrectness
import GameTheory.Mechanism.Knapsack.Correctness
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

private def DensityOrdered (weight value : Agent → ℕ)
    (items : List Agent) : Prop :=
  items.Pairwise fun earlier later =>
    value later * weight earlier ≤ value earlier * weight later

omit [DecidableEq Agent] in
private theorem densityLE_sound (weight value : Agent → ℕ)
    {left right : Agent} (hcompare : densityLE weight value left right = true) :
    value right * weight left ≤ value left * weight right := by
  by_cases hleft : weight left = 0
  · simp [hleft]
  · by_cases hright : weight right = 0
    · simp [densityLE, hleft, hright] at hcompare
    · simpa [densityLE, hleft, hright] using hcompare

omit [DecidableEq Agent] in
private theorem greedySplit_taken_eq_of_rejected_eq_none (weight : Agent → ℕ)
    (items : List Agent) (capacity : ℕ)
    (hrejected : (greedySplit weight items capacity).rejected = none) :
    (greedySplit weight items capacity).taken = items := by
  induction items generalizing capacity with
  | nil => simp [greedySplit]
  | cons item items ih =>
      by_cases hfit : weight item ≤ capacity
      · simp only [greedySplit, hfit, if_true] at hrejected ⊢
        exact congrArg (List.cons item)
          (ih (capacity - weight item) hrejected)
      · simp [greedySplit, hfit] at hrejected

omit [DecidableEq Agent] in
private theorem welfare_mono_of_subset (value : Agent → ℕ)
    {left right : Finset Agent} (hsubset : left ⊆ right) :
    welfare value left ≤ welfare value right := by
  unfold welfare aggregate
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => Nat.zero_le _

/-- Division-free exchange bound at the first rejected density-ordered item. -/
private theorem welfare_le_greedy_add_rejected
    (weight value : Agent → ℕ) {items taken rest : List Agent}
    {rejected : Agent} {remaining capacity : ℕ}
    (hitemsNodup : items.Nodup)
    (hdecomposition : items = taken ++ rejected :: rest)
    (hordered : DensityOrdered weight value items)
    (hrejectedPos : 0 < weight rejected)
    (hcapacity : (taken.map weight).sum + remaining = capacity)
    (htooHeavy : remaining < weight rejected)
    {selected : Finset Agent} (hselected : selected ⊆ items.toFinset)
    (hfeasible : load weight selected ≤ capacity) :
    welfare value selected ≤ welfare value taken.toFinset + value rejected := by
  let prefixSet : Finset Agent := taken.toFinset
  let common : Finset Agent := selected ∩ prefixSet
  let after : Finset Agent := selected \ prefixSet
  let missing : Finset Agent := prefixSet \ selected
  have htakenNodup : taken.Nodup := by
    rw [hdecomposition] at hitemsNodup
    exact (List.nodup_append.mp hitemsNodup).1
  have hordered' : DensityOrdered weight value (taken ++ rejected :: rest) := by
    simpa only [hdecomposition] using hordered
  have hprefixToRejected :
      ∀ item ∈ taken,
        value rejected * weight item ≤ value item * weight rejected := by
    intro item hitem
    exact (List.pairwise_append.mp hordered').2.2 item hitem rejected (by simp)
  have hrejectedToRest :
      ∀ item ∈ rest,
        value item * weight rejected ≤ value rejected * weight item := by
    intro item hitem
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hordered').2.1).1 item hitem
  have hafterInSuffix : ∀ item ∈ after, item ∈ rejected :: rest := by
    intro item hitem
    have hitemSelected : item ∈ selected := (Finset.mem_sdiff.mp hitem).1
    have hitemNotPrefix : item ∉ prefixSet := (Finset.mem_sdiff.mp hitem).2
    have hitemItems : item ∈ items :=
      List.mem_toFinset.mp (hselected hitemSelected)
    rw [hdecomposition] at hitemItems
    rcases List.mem_append.mp hitemItems with hitemTaken | hitemSuffix
    · exact False.elim (hitemNotPrefix (List.mem_toFinset.mpr hitemTaken))
    · exact hitemSuffix
  have hafterRatio : ∀ item ∈ after,
      value item * weight rejected ≤ value rejected * weight item := by
    intro item hitem
    rcases List.mem_cons.mp (hafterInSuffix item hitem) with rfl | hrest
    · exact le_rfl
    · exact hrejectedToRest item hrest
  have hmissingRatio : ∀ item ∈ missing,
      value rejected * weight item ≤ value item * weight rejected := by
    intro item hitem
    have hitemPrefix : item ∈ prefixSet := (Finset.mem_sdiff.mp hitem).1
    exact hprefixToRejected item (List.mem_toFinset.mp hitemPrefix)
  have hafterWeighted :
      weight rejected * welfare value after ≤
        value rejected * load weight after := by
    unfold welfare load aggregate
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro item hitem
    simpa [Nat.mul_comm, Nat.mul_left_comm] using hafterRatio item hitem
  have hmissingWeighted :
      value rejected * load weight missing ≤
        weight rejected * welfare value missing := by
    unfold welfare load aggregate
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro item hitem
    simpa [Nat.mul_comm, Nat.mul_left_comm] using hmissingRatio item hitem
  have hselectedSplit :
      load weight common + load weight after = load weight selected := by
    simpa [common, after, prefixSet, load, aggregate] using
      selected.sum_inter_add_sum_sdiff prefixSet weight
  have hprefixSplit :
      load weight common + load weight missing = load weight prefixSet := by
    simpa [common, missing, prefixSet, load, aggregate, Finset.inter_comm] using
      prefixSet.sum_inter_add_sum_sdiff selected weight
  have hprefixLoad : load weight prefixSet = (taken.map weight).sum := by
    simp [prefixSet, load, aggregate, List.sum_toFinset weight htakenNodup]
  have hafterLoad : load weight after ≤ load weight missing + remaining := by
    omega
  have hafterBound :
      weight rejected * welfare value after ≤
        weight rejected * welfare value missing + value rejected * weight rejected := by
    calc
      weight rejected * welfare value after ≤ value rejected * load weight after :=
        hafterWeighted
      _ ≤ value rejected * (load weight missing + remaining) :=
        Nat.mul_le_mul_left _ hafterLoad
      _ = value rejected * load weight missing + value rejected * remaining := by
        exact Nat.mul_add _ _ _
      _ ≤ weight rejected * welfare value missing + value rejected * remaining :=
        Nat.add_le_add_right hmissingWeighted _
      _ ≤ weight rejected * welfare value missing +
          value rejected * weight rejected := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left _ (Nat.le_of_lt htooHeavy)) _
  have hwelfareSelectedSplit :
      welfare value common + welfare value after = welfare value selected := by
    simpa [common, after, prefixSet, welfare, aggregate] using
      selected.sum_inter_add_sum_sdiff prefixSet value
  have hwelfarePrefixSplit :
      welfare value common + welfare value missing = welfare value prefixSet := by
    simpa [common, missing, prefixSet, welfare, aggregate, Finset.inter_comm] using
      prefixSet.sum_inter_add_sum_sdiff selected value
  apply Nat.le_of_mul_le_mul_left _ hrejectedPos
  calc
    weight rejected * welfare value selected =
        weight rejected * welfare value common +
          weight rejected * welfare value after := by
      rw [← hwelfareSelectedSplit]
      exact Nat.mul_add _ _ _
    _ ≤ weight rejected * welfare value common +
        (weight rejected * welfare value missing +
          value rejected * weight rejected) :=
      Nat.add_le_add_left hafterBound _
    _ = weight rejected * (welfare value prefixSet + value rejected) := by
      rw [← hwelfarePrefixSplit]
      simp only [Nat.mul_add, Nat.add_assoc, Nat.mul_comm]
    _ = weight rejected * (welfare value taken.toFinset + value rejected) := rfl

/-- Every supported feasible allocation has at most twice the welfare of the
actual allocation returned by the repaired approximation algorithm. -/
theorem welfare_le_two_mul_approximate (weight value : Agent → ℕ)
    {items : List Agent} (hitems : items.Nodup)
    (capacity : ℕ)
    {selected : Finset Agent} (hsupport : selected ⊆ items.toFinset)
    (hfeasible : load weight selected ≤ capacity) :
    welfare value selected ≤
      2 * welfare value (approximate weight value items capacity) := by
  let eligible := feasibleItems weight capacity items
  let ordered := sortByDensity weight value eligible
  let split := greedySplit weight ordered capacity
  let greedy := split.taken.toFinset
  let singleton := singletonAllocation (bestItem? value eligible)
  have heligibleNodup : eligible.Nodup := hitems.filter _
  have horderedNodup : ordered.Nodup :=
    sortByDensity_nodup weight value heligibleNodup
  have horderedPerm : List.Perm ordered eligible :=
    sortByDensity_perm weight value eligible
  have horderedDensity : DensityOrdered weight value ordered :=
    (sortByDensity_pairwise weight value eligible).imp fun hcompare =>
      densityLE_sound weight value hcompare
  have hselectedEligible : selected ⊆ eligible.toFinset := by
    intro item hitem
    have hsingle : ({item} : Finset Agent) ⊆ selected := by
      simpa using hitem
    have hitemCapacity : weight item ≤ capacity := by
      calc
        weight item = load weight ({item} : Finset Agent) := by
          simp [load, aggregate]
        _ ≤ load weight selected := welfare_mono_of_subset weight hsingle
        _ ≤ capacity := hfeasible
    exact List.mem_toFinset.mpr
      ((mem_feasibleItems weight capacity items item).mpr
        ⟨List.mem_toFinset.mp (hsupport hitem), hitemCapacity⟩)
  have horderedSet : ordered.toFinset = eligible.toFinset :=
    List.toFinset_eq_of_perm _ _ horderedPerm
  have hselectedOrdered : selected ⊆ ordered.toFinset := by
    simpa only [horderedSet] using hselectedEligible
  have hgreedyValue :
      welfare value greedy ≤
        welfare value (approximate weight value items capacity) := by
    have hdom := (welfare_le_betterAllocation value greedy singleton).1
    simpa [approximate, eligible, ordered, greedyPrefix, split, greedy, singleton]
      using hdom
  have hsingletonValue :
      welfare value singleton ≤
        welfare value (approximate weight value items capacity) := by
    have hdom := (welfare_le_betterAllocation value greedy singleton).2
    simpa [approximate, eligible, ordered, greedyPrefix, split, greedy, singleton]
      using hdom
  cases hrejected : split.rejected with
  | none =>
      have htaken : split.taken = ordered := by
        apply greedySplit_taken_eq_of_rejected_eq_none weight ordered capacity
        simpa [split] using hrejected
      have hselectedGreedy : selected ⊆ greedy := by
        simpa [greedy, htaken] using hselectedOrdered
      calc
        welfare value selected ≤ welfare value greedy :=
          welfare_mono_of_subset value hselectedGreedy
        _ ≤ welfare value (approximate weight value items capacity) := hgreedyValue
        _ ≤ 2 * welfare value (approximate weight value items capacity) := by omega
  | some rejected =>
      have hdecomposition : ordered = split.taken ++ rejected :: split.rest := by
        have hfull := greedySplit_decomposition weight ordered capacity
        simpa [split, hrejected] using hfull
      have hrejectedOrdered : rejected ∈ ordered := by
        rw [hdecomposition]
        simp
      have hrejectedEligible : rejected ∈ eligible :=
        horderedPerm.mem_iff.mp hrejectedOrdered
      have hcapacity : (split.taken.map weight).sum + split.remaining = capacity := by
        simpa [split] using
          greedySplit_sum_weight_add_remaining weight ordered capacity
      have htooHeavy : split.remaining < weight rejected := by
        apply greedySplit_rejected_tooHeavy weight ordered capacity
        simpa [split] using hrejected
      have hrejectedPos : 0 < weight rejected :=
        lt_of_le_of_lt (Nat.zero_le split.remaining) htooHeavy
      have hexchange :
          welfare value selected ≤ welfare value greedy + value rejected := by
        simpa [greedy] using
          welfare_le_greedy_add_rejected weight value horderedNodup
            hdecomposition horderedDensity hrejectedPos hcapacity htooHeavy
            hselectedOrdered hfeasible
      cases hbest : bestItem? value eligible with
      | none =>
          have hempty : eligible = [] :=
            (bestItem?_eq_none_iff value eligible).mp hbest
          simp [hempty] at hrejectedEligible
      | some best =>
          have hrejectedBest : value rejected ≤ value best :=
            le_bestItem? value hbest hrejectedEligible
          have hbestSingleton : welfare value singleton = value best := by
            simp [singleton, hbest, singletonAllocation, welfare, aggregate]
          calc
            welfare value selected ≤ welfare value greedy + value rejected := hexchange
            _ ≤ welfare value greedy + value best :=
              Nat.add_le_add_left hrejectedBest _
            _ = welfare value greedy + welfare value singleton := by
              rw [hbestSingleton]
            _ ≤ welfare value (approximate weight value items capacity) +
                welfare value (approximate weight value items capacity) :=
              Nat.add_le_add hgreedyValue hsingletonValue
            _ = 2 * welfare value (approximate weight value items capacity) := by omega

/-- A successful checked approximation call returns a supported feasible
allocation satisfying the half-approximation guarantee. -/
theorem approximate?_half (weight value : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) {result : Finset Agent}
    (hresult : approximate? weight value items capacity = some result) :
    result ⊆ items.toFinset ∧ load weight result ≤ capacity ∧
      ∀ selected : Finset Agent, selected ⊆ items.toFinset →
        load weight selected ≤ capacity →
          welfare value selected ≤ 2 * welfare value result := by
  have hvalid : approximationInputValid items = true := by
    unfold approximate? at hresult
    split at hresult <;> rename_i hcheck
    · simpa using hcheck
    · simp at hresult
  have hinput := (approximationInputValid_eq_true_iff items).mp hvalid
  have hraw : approximate weight value items capacity = result := by
    unfold approximate? at hresult
    rw [hvalid] at hresult
    simpa using hresult
  subst result
  exact ⟨approximate_subset weight value items capacity,
    approximate_feasible weight value hinput capacity,
    fun selected hsupport hfeasible =>
      welfare_le_two_mul_approximate weight value hinput capacity
        hsupport hfeasible⟩

/-- The checked half approximation is within a factor of two of the exact
finite solver on the same explicit item list. -/
theorem solveList_welfare_le_two_mul_approximate? (weight value : Agent → ℕ)
    (items : List Agent) (capacity : ℕ) {result : Finset Agent}
    (hresult : approximate? weight value items capacity = some result) :
    welfare value (solveList weight value items capacity) ≤
      2 * welfare value result := by
  have hguarantee := (approximate?_half weight value items capacity hresult).2.2
  have hvalid : approximationInputValid items = true := by
    unfold approximate? at hresult
    split at hresult <;> rename_i hcheck
    · simpa using hcheck
    · simp at hresult
  have hitems := (approximationInputValid_eq_true_iff items).mp hvalid
  exact hguarantee (solveList weight value items capacity)
    (solveList_subset_toFinset weight value items capacity)
    (solveList_feasible weight value hitems capacity)

end GameTheory.Mechanism.Knapsack
