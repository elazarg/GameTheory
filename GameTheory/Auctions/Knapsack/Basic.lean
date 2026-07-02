/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.Myerson
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort

/-!
# Knapsack Auctions

This file develops the single-parameter binary knapsack auction. Agents report
values, have public weights, and feasible allocations are subsets whose total
weight is at most the public capacity.

The welfare-maximizing allocation rule is monotone in each agent's own report.
Consequently the Myerson/envelope payment rule implements it in dominant
strategies.
-/

open scoped BigOperators

namespace GameTheory

variable {ι : Type}

namespace KnapsackAuction

/-- Public data of a binary knapsack auction: each agent has a public weight and
the knapsack has a public capacity. -/
structure Data (ι : Type) where
  /-- Public weight or size of agent `i`. -/
  weight : ι → ℝ
  /-- Total knapsack capacity. -/
  capacity : ℝ

variable [Fintype ι]

/-- A binary allocation profile: an agent is selected or not selected. -/
abbrev BinaryAllocation (ι : Type) := ι → Bool

/-- Interpret a binary allocation as a `0/1` single-parameter allocation vector. -/
def binaryToAllocation (x : BinaryAllocation ι) : ι → ℝ :=
  fun i => if x i then 1 else 0

/-- Total load of a binary allocation. -/
def binaryLoad (A : Data ι) (x : BinaryAllocation ι) : ℝ :=
  ∑ i, A.weight i * binaryToAllocation x i

/-- A binary allocation respects the knapsack capacity. -/
def binaryRespectsCapacity (A : Data ι) (x : BinaryAllocation ι) : Prop :=
  binaryLoad A x ≤ A.capacity

/-- Feasible binary allocations for the public knapsack data. -/
noncomputable def feasibleBinaryAllocations (A : Data ι) :
    Finset (BinaryAllocation ι) :=
  by
    classical
    exact Finset.univ.filter (binaryRespectsCapacity A)

/-- Social welfare of a binary allocation at a bid/value profile. -/
def binarySocialWelfare (bids : ι → ℝ) (x : BinaryAllocation ι) : ℝ :=
  ∑ i, bids i * binaryToAllocation x i

/-- The all-zero allocation respects any nonnegative capacity. -/
theorem zeroBinaryRespectsCapacity (A : Data ι) (hcap : 0 ≤ A.capacity) :
    binaryRespectsCapacity A (fun _ => false) := by
  simpa [binaryRespectsCapacity, binaryLoad, binaryToAllocation] using hcap

/-- The feasible allocation set is nonempty when capacity is nonnegative. -/
theorem feasibleBinaryAllocations_nonempty (A : Data ι) (hcap : 0 ≤ A.capacity) :
    (feasibleBinaryAllocations A).Nonempty := by
  classical
  exact ⟨fun _ => false, by simp [feasibleBinaryAllocations, zeroBinaryRespectsCapacity A hcap]⟩

/-- There exists a feasible allocation maximizing reported social welfare. -/
theorem exists_welfareMaximizer (A : Data ι) (bids : ι → ℝ)
    (hcap : 0 ≤ A.capacity) :
    ∃ x ∈ feasibleBinaryAllocations A,
      ∀ y ∈ feasibleBinaryAllocations A,
        binarySocialWelfare bids y ≤ binarySocialWelfare bids x :=
  Finset.exists_max_image (feasibleBinaryAllocations A) (binarySocialWelfare bids)
    (feasibleBinaryAllocations_nonempty A hcap)

/-- A chosen feasible welfare maximizer. -/
noncomputable def welfareMaximizer (A : Data ι) (bids : ι → ℝ)
    (hcap : 0 ≤ A.capacity) : BinaryAllocation ι :=
  Classical.choose (exists_welfareMaximizer A bids hcap)

/-- The chosen welfare maximizer is feasible. -/
theorem welfareMaximizer_mem_feasibleBinaryAllocations (A : Data ι)
    (bids : ι → ℝ) (hcap : 0 ≤ A.capacity) :
    welfareMaximizer A bids hcap ∈ feasibleBinaryAllocations A :=
  (Classical.choose_spec (exists_welfareMaximizer A bids hcap)).1

/-- Every feasible allocation has welfare at most the chosen welfare maximizer. -/
theorem welfareMaximizer_ge (A : Data ι) (bids : ι → ℝ)
    (hcap : 0 ≤ A.capacity) {x : BinaryAllocation ι}
    (hx : x ∈ feasibleBinaryAllocations A) :
    binarySocialWelfare bids x ≤
      binarySocialWelfare bids (welfareMaximizer A bids hcap) :=
  (Classical.choose_spec (exists_welfareMaximizer A bids hcap)).2 x hx

/-- The welfare value of the chosen welfare-maximizing binary allocation. -/
noncomputable def maximalSocialWelfare (A : Data ι) (bids : ι → ℝ)
    (hcap : 0 ≤ A.capacity) : ℝ :=
  binarySocialWelfare bids (welfareMaximizer A bids hcap)

/-- The chosen welfare maximizer respects capacity. -/
theorem welfareMaximizer_respectsCapacity (A : Data ι) (bids : ι → ℝ)
    (hcap : 0 ≤ A.capacity) :
    binaryRespectsCapacity A (welfareMaximizer A bids hcap) := by
  have hmem := welfareMaximizer_mem_feasibleBinaryAllocations A bids hcap
  simpa [feasibleBinaryAllocations] using hmem

theorem binaryRespectsCapacity_of_mem_feasibleBinaryAllocations (A : Data ι)
    {x : BinaryAllocation ι} (hx : x ∈ feasibleBinaryAllocations A) :
    binaryRespectsCapacity A x := by
  classical
  simpa [feasibleBinaryAllocations] using hx

section FractionalGreedy

/-- Fractional social welfare for an allocation vector. -/
def fractionalSocialWelfare (bids : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, bids i * x i

/-- Feasibility of a fractional knapsack allocation. -/
def fractionalFeasible (A : Data ι) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    (∑ i, A.weight i * x i) ≤ A.capacity

/-- Value-to-weight ratio used by the fractional greedy rule. -/
noncomputable def ratio (A : Data ι) (bids : ι → ℝ) (i : ι) : ℝ :=
  bids i / A.weight i

/-- Sorting key for fractional greedy: higher ratio first, then the ambient
order on agents. -/
noncomputable def ratioTieKey [LinearOrder ι] (A : Data ι) (bids : ι → ℝ)
    (i : ι) : ℝ × ι :=
  (-ratio A bids i, i)

/-- Agents sorted by decreasing value-to-weight ratio. -/
noncomputable def sortedAgentsByRatio [LinearOrder ι] (A : Data ι)
    (bids : ι → ℝ) : List ι := by
  classical
  exact ((Finset.univ : Finset ι).toList).mergeSort
    (fun i j => decide (ratioTieKey A bids i ≤ ratioTieKey A bids j))

/-- Greedy fractional allocation along a fixed list order. If the next item does
not fully fit, the algorithm takes the remaining fraction and stops. -/
noncomputable def fractionalGreedyList [DecidableEq ι] (A : Data ι) :
    List ι → ℝ → ι → ℝ
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if remaining ≤ 0 then
        fun _ => 0
      else if A.weight i ≤ remaining then
        Function.update (fractionalGreedyList A items (remaining - A.weight i)) i 1
      else
        fun j => if j = i then remaining / A.weight i else 0
termination_by items _ => items.length

/-- The ratio-sorted fractional greedy allocation. -/
noncomputable def fractionalGreedyAllocation [DecidableEq ι] [LinearOrder ι]
    (A : Data ι) (bids : ι → ℝ) : ι → ℝ :=
  fractionalGreedyList A (sortedAgentsByRatio A bids) A.capacity

/-- Every feasible binary allocation is feasible for the fractional relaxation. -/
theorem binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
    (A : Data ι) {x : BinaryAllocation ι}
    (hx : binaryRespectsCapacity A x) :
    fractionalFeasible A (binaryToAllocation x) := by
  constructor
  · intro i
    by_cases hxi : x i <;> simp [binaryToAllocation, hxi]
  · simpa [fractionalFeasible, binaryRespectsCapacity, binaryLoad, binaryToAllocation] using hx

/-- If the fractional greedy allocation is optimal for the fractional relaxation,
then it dominates the welfare of the optimal binary allocation. -/
theorem fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal [DecidableEq ι] [LinearOrder ι]
    (A : Data ι) (bids : ι → ℝ) (hcap : 0 ≤ A.capacity)
    (hgreedyOptimal :
      ∀ x : ι → ℝ, fractionalFeasible A x →
        fractionalSocialWelfare bids x ≤
          fractionalSocialWelfare bids (fractionalGreedyAllocation A bids)) :
    maximalSocialWelfare A bids hcap ≤
      fractionalSocialWelfare bids (fractionalGreedyAllocation A bids) := by
  let xStar := welfareMaximizer A bids hcap
  have hxStarFeas : fractionalFeasible A (binaryToAllocation xStar) :=
    binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity A
      (binaryRespectsCapacity_of_mem_feasibleBinaryAllocations A
        (welfareMaximizer_mem_feasibleBinaryAllocations A bids hcap))
  calc
    maximalSocialWelfare A bids hcap
        = fractionalSocialWelfare bids (binaryToAllocation xStar) := by
          simp [maximalSocialWelfare, fractionalSocialWelfare, xStar, binarySocialWelfare]
    _ ≤ fractionalSocialWelfare bids (fractionalGreedyAllocation A bids) :=
      hgreedyOptimal _ hxStarFeas

end FractionalGreedy

/-- Updating one bid separates the updated bidder's contribution from the
unchanged opponents' contribution. -/
theorem binarySocialWelfare_update_eq_add [DecidableEq ι] (bids : ι → ℝ) (i : ι) (bid : ℝ)
    (x : BinaryAllocation ι) :
    binarySocialWelfare (Function.update bids i bid) x =
      binarySocialWelfare bids x + (bid - bids i) * binaryToAllocation x i := by
  classical
  rw [binarySocialWelfare, binarySocialWelfare]
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset ι)) (a := i)
      (f := fun j => Function.update bids i bid j * binaryToAllocation x j)
      (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset ι)) (a := i)
      (f := fun j => bids j * binaryToAllocation x j) (Finset.mem_univ i)]
  have hsums :
      (∑ j ∈ (Finset.univ.erase i),
          Function.update bids i bid j * binaryToAllocation x j) =
        ∑ j ∈ (Finset.univ.erase i),
          bids j * binaryToAllocation x j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hji]
  rw [hsums]
  simp only [Function.update_self]
  ring

variable [DecidableEq ι]

/-- The welfare-maximizing allocation rule, viewed as a real `0/1` allocation
for the single-parameter mechanism layer. -/
noncomputable def welfareMaximizingAllocationRule (A : Data ι)
    (hcap : 0 ≤ A.capacity) : (ι → ℝ) → ι → ℝ :=
  fun bids => binaryToAllocation (welfareMaximizer A bids hcap)

/-- The Myerson payment rule for the welfare-maximizing knapsack allocation. -/
noncomputable def welfareMaximizingPaymentRule (A : Data ι)
    (hcap : 0 ≤ A.capacity) : (ι → ℝ) → ι → ℝ :=
  SingleParameterMechanism.myersonPayment
    (welfareMaximizingAllocationRule A hcap)

/-- The welfare-maximizing knapsack mechanism with Myerson payments. -/
noncomputable def welfareMaximizingMechanism (A : Data ι)
    (hcap : 0 ≤ A.capacity) : SingleParameterMechanism ι :=
  SingleParameterMechanism.withMyersonPayment
    (welfareMaximizingAllocationRule A hcap)

/-- The welfare-maximizing allocation rule is monotone in each agent's own bid. -/
theorem welfareMaximizingAllocationRule_isMonotone (A : Data ι)
    (hcap : 0 ≤ A.capacity) :
    SingleParameterMechanism.AllocationIsMonotone
      (welfareMaximizingAllocationRule A hcap) := by
  intro i bids bid hle
  by_cases heq : bids i = bid
  · subst bid
    simp [welfareMaximizingAllocationRule]
  · have hlt : bids i < bid := lt_of_le_of_ne hle heq
    let xLo := welfareMaximizer A bids hcap
    let bidsHi := Function.update bids i bid
    let xHi := welfareMaximizer A bidsHi hcap
    have hxLo_feas : xLo ∈ feasibleBinaryAllocations A :=
      welfareMaximizer_mem_feasibleBinaryAllocations A bids hcap
    have hxHi_feas : xHi ∈ feasibleBinaryAllocations A :=
      welfareMaximizer_mem_feasibleBinaryAllocations A bidsHi hcap
    have hLo :
        binarySocialWelfare bids xHi ≤ binarySocialWelfare bids xLo :=
      welfareMaximizer_ge A bids hcap hxHi_feas
    have hHi :
        binarySocialWelfare bidsHi xLo ≤ binarySocialWelfare bidsHi xHi :=
      welfareMaximizer_ge A bidsHi hcap hxLo_feas
    by_cases hxLo_i : xLo i <;> by_cases hxHi_i : xHi i
    · simp [welfareMaximizingAllocationRule, xLo, xHi, bidsHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · exfalso
      have hHi_eq :
          binarySocialWelfare bidsHi xHi = binarySocialWelfare bids xHi := by
        rw [binarySocialWelfare_update_eq_add bids i bid xHi]
        simp [binaryToAllocation, hxHi_i]
      have hLo_eq :
          binarySocialWelfare bidsHi xLo =
            binarySocialWelfare bids xLo + (bid - bids i) := by
        rw [binarySocialWelfare_update_eq_add bids i bid xLo]
        simp [binaryToAllocation, hxLo_i]
      have hpos : 0 < bid - bids i := sub_pos.mpr hlt
      rw [hHi_eq, hLo_eq] at hHi
      linarith
    · simp [welfareMaximizingAllocationRule, xLo, xHi, bidsHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · simp [welfareMaximizingAllocationRule, xLo, xHi, bidsHi, binaryToAllocation,
        hxLo_i, hxHi_i]

/-- The welfare-maximizing knapsack mechanism is DSIC. -/
theorem welfareMaximizingMechanism_isDSIC (A : Data ι)
    (hcap : 0 ≤ A.capacity) :
    (welfareMaximizingMechanism A hcap).IsDSIC := by
  let allocation := welfareMaximizingAllocationRule A hcap
  have hmono : SingleParameterMechanism.AllocationIsMonotone allocation :=
    welfareMaximizingAllocationRule_isMonotone A hcap
  have hint : SingleParameterMechanism.IsEnvelopeIntegrable allocation :=
    SingleParameterMechanism.isEnvelopeIntegrable_of_isMonotone hmono
  simpa [welfareMaximizingMechanism, allocation] using
    SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone allocation hmono hint

section DynamicProgramming

/-- Integer-valued welfare of a binary allocation profile. -/
def natBinarySocialWelfare (bids : ι → Nat) (x : BinaryAllocation ι) : Nat :=
  ∑ i, if x i then bids i else 0

/-- Integer-valued load of a binary allocation profile. -/
def natBinaryLoad (w : ι → Nat) (x : BinaryAllocation ι) : Nat :=
  ∑ i, if x i then w i else 0

/-- An allocation is supported on a list of agents if every selected agent
appears in that list. -/
private def supportedOn (items : List ι) (x : BinaryAllocation ι) : Prop :=
  ∀ i, x i = true → i ∈ items

omit [Fintype ι] [DecidableEq ι] in
private theorem eq_false_of_supportedOn_of_not_mem
    {items : List ι} {x : BinaryAllocation ι}
    (hsupp : supportedOn items x) {i : ι} (hi : i ∉ items) :
    x i = false := by
  cases hxi : x i with
  | false => rfl
  | true => exact False.elim (hi (hsupp i hxi))

omit [Fintype ι] [DecidableEq ι] in
private theorem supportedOn_nil_iff {x : BinaryAllocation ι} :
    supportedOn ([] : List ι) x ↔ x = fun _ => false := by
  constructor
  · intro hsupp
    funext i
    exact eq_false_of_supportedOn_of_not_mem hsupp (by simp)
  · intro hx i hi
    simp [hx] at hi

omit [Fintype ι] [DecidableEq ι] in
private theorem supportedOn_tail_of_eq_false
    {i : ι} {items : List ι} {x : BinaryAllocation ι}
    (hsupp : supportedOn (i :: items) x) (hxi : x i = false) :
    supportedOn items x := by
  intro j hj
  have hjmem : j ∈ i :: items := hsupp j hj
  rcases List.mem_cons.mp hjmem with rfl | hjtail
  · simp [hxi] at hj
  · exact hjtail

omit [Fintype ι] in
private theorem supportedOn_update_false
    {i : ι} {items : List ι} {x : BinaryAllocation ι}
    (hsupp : supportedOn (i :: items) x) :
    supportedOn items (Function.update x i false) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp at hj
  · have hxj : x j = true := by simpa [Function.update, hji] using hj
    have hjmem : j ∈ i :: items := hsupp j hxj
    rcases List.mem_cons.mp hjmem with rfl | hjtail
    · exact False.elim (hji rfl)
    · exact hjtail

private theorem natBinarySocialWelfare_eq_add_of_true
    (bids : ι → Nat) {x : BinaryAllocation ι} {i : ι}
    (hxi : x i = true) :
    natBinarySocialWelfare bids x =
      bids i + natBinarySocialWelfare bids (Function.update x i false) := by
  have htail :
      natBinarySocialWelfare bids (Function.update x i false) =
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then bids j else 0) := by
    rw [natBinarySocialWelfare,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i)
            (fun j => if Function.update x i false j = true then bids j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if x j = true then bids j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [Function.update] using hs
  rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [hxi]

private theorem natBinaryLoad_eq_add_of_true
    (w : ι → Nat) {x : BinaryAllocation ι} {i : ι}
    (hxi : x i = true) :
    natBinaryLoad w x =
      w i + natBinaryLoad w (Function.update x i false) := by
  have htail :
      natBinaryLoad w (Function.update x i false) =
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
    rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i)
            (fun j => if Function.update x i false j = true then w j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [Function.update] using hs
  rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [hxi]

private theorem natBinarySocialWelfare_update_true_of_false
    (bids : ι → Nat) {x : BinaryAllocation ι} {i : ι}
    (hxi : x i = false) :
    natBinarySocialWelfare bids (Function.update x i true) =
      bids i + natBinarySocialWelfare bids x := by
  have htail :
      natBinarySocialWelfare bids x =
        Finset.sum (Finset.univ.erase i)
          (fun j => if Function.update x i true j = true then bids j else 0) := by
    rw [natBinarySocialWelfare,
      ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then bids j else 0) =
          Finset.sum (Finset.univ.erase i)
            (fun j => if Function.update x i true j = true then bids j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [hxi] using hs
  rw [natBinarySocialWelfare,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [Function.update]

private theorem natBinaryLoad_update_true_of_false
    (w : ι → Nat) {x : BinaryAllocation ι} {i : ι}
    (hxi : x i = false) :
    natBinaryLoad w (Function.update x i true) =
      w i + natBinaryLoad w x := by
  have htail :
      natBinaryLoad w x =
        Finset.sum (Finset.univ.erase i)
          (fun j => if Function.update x i true j = true then w j else 0) := by
    rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) =
          Finset.sum (Finset.univ.erase i)
            (fun j => if Function.update x i true j = true then w j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [hxi] using hs
  rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [Function.update]

/-- A recursive skip/take dynamic-programming solver for finite `0/1` knapsack
instances over natural weights and values. -/
def dpSolveList (w bids : ι → Nat) : List ι → Nat → BinaryAllocation ι
  | [], _ => fun _ => false
  | i :: items, capacity =>
      if w i ≤ capacity then
        let skip := dpSolveList w bids items capacity
        let takeTail := dpSolveList w bids items (capacity - w i)
        let take := Function.update takeTail i true
        if natBinarySocialWelfare bids take ≥ natBinarySocialWelfare bids skip then
          take
        else
          skip
      else
        dpSolveList w bids items capacity
termination_by items _ => items.length

private theorem dpSolveList_supportedOn (w bids : ι → Nat) :
    ∀ items capacity, supportedOn items (dpSolveList w bids items capacity) := by
  intro items
  induction items with
  | nil =>
      intro capacity i hi
      simp [dpSolveList] at hi
  | cons i items ih =>
      intro capacity
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w bids items capacity
        let takeTail := dpSolveList w bids items (capacity - w i)
        let take := Function.update takeTail i true
        by_cases hchoose : natBinarySocialWelfare bids take ≥ natBinarySocialWelfare bids skip
        · intro j hj
          have hjtake : take j = true := by
            simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hj
          by_cases hji : j = i
          · subst hji
            simp
          · exact List.mem_cons.2
              (.inr (ih (capacity - w i) j
                (by simpa [take, Function.update, hji] using hjtake)))
        · intro j hj
          have hjskip : skip j = true := by
            simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hj
          exact List.mem_cons.2 (.inr (ih capacity j hjskip))
      · intro j hj
        have hj' : dpSolveList w bids items capacity j = true := by
          simpa [dpSolveList, hwi] using hj
        exact List.mem_cons.2 (.inr ((ih capacity) j hj'))

private theorem dpSolveList_feasible (w bids : ι → Nat) :
    ∀ items, items.Nodup → ∀ capacity,
      natBinaryLoad w (dpSolveList w bids items capacity) ≤ capacity := by
  intro items hnodup
  induction hnodup with
  | nil =>
      intro capacity
      simp [dpSolveList, natBinaryLoad]
  | @cons i items hnotmem _ ih =>
      intro capacity
      have hi_not_mem : i ∉ items := by
        intro hi
        exact (hnotmem i hi) rfl
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w bids items capacity
        let takeTail := dpSolveList w bids items (capacity - w i)
        let take := Function.update takeTail i true
        have htail : natBinaryLoad w takeTail ≤ capacity - w i := ih (capacity - w i)
        have htakeTailFalse : takeTail i = false :=
          eq_false_of_supportedOn_of_not_mem
            (dpSolveList_supportedOn w bids items (capacity - w i)) hi_not_mem
        by_cases hchoose : natBinarySocialWelfare bids take ≥ natBinarySocialWelfare bids skip
        · have hdp : dpSolveList w bids (i :: items) capacity = take := by
            simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          rw [hdp]
          rw [natBinaryLoad_update_true_of_false w htakeTailFalse]
          calc
            w i + natBinaryLoad w takeTail ≤ w i + (capacity - w i) :=
              Nat.add_le_add_left htail _
            _ = capacity := Nat.add_sub_of_le hwi
        · have hdp : dpSolveList w bids (i :: items) capacity = skip := by
            simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          rw [hdp]
          exact ih capacity
      · simpa [dpSolveList, hwi] using ih capacity

private theorem dpSolveList_optimal (w bids : ι → Nat) :
    ∀ (items : List ι), items.Nodup → ∀ capacity {x : BinaryAllocation ι},
      supportedOn items x →
      natBinaryLoad w x ≤ capacity →
        natBinarySocialWelfare bids x ≤ natBinarySocialWelfare bids
          (dpSolveList w bids items capacity) := by
  intro items hnodup
  induction hnodup with
  | nil =>
      intro capacity x hsupp _hload
      rw [(supportedOn_nil_iff.mp hsupp)]
      simp [dpSolveList, natBinarySocialWelfare]
  | @cons i items hnotmem _ ih =>
      intro capacity x hsupp hload
      have hi_not_mem : i ∉ items := by
        intro hi
        exact (hnotmem i hi) rfl
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w bids items capacity
        let takeTail := dpSolveList w bids items (capacity - w i)
        let take := Function.update takeTail i true
        by_cases hxi : x i = true
        · have hsuppTail : supportedOn items (Function.update x i false) :=
            supportedOn_update_false hsupp
          have hloadTail : natBinaryLoad w (Function.update x i false) ≤ capacity - w i := by
            rw [natBinaryLoad_eq_add_of_true w hxi] at hload
            exact (Nat.le_sub_iff_add_le hwi).2
              (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hload)
          have hoptTail :
              natBinarySocialWelfare bids (Function.update x i false) ≤
                natBinarySocialWelfare bids takeTail :=
            ih (capacity - w i) hsuppTail hloadTail
          have htakeTailFalse : takeTail i = false :=
            eq_false_of_supportedOn_of_not_mem
              (dpSolveList_supportedOn w bids items (capacity - w i)) hi_not_mem
          have hx :
              natBinarySocialWelfare bids x ≤ natBinarySocialWelfare bids take := by
            rw [natBinarySocialWelfare_eq_add_of_true bids hxi,
              natBinarySocialWelfare_update_true_of_false bids htakeTailFalse]
            exact Nat.add_le_add_left hoptTail (bids i)
          by_cases hchoose : natBinarySocialWelfare bids take ≥ natBinarySocialWelfare bids skip
          · simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hx
          · have htake_le_skip :
                natBinarySocialWelfare bids take ≤ natBinarySocialWelfare bids skip :=
              le_of_not_ge hchoose
            exact le_trans hx
              (by simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using htake_le_skip)
        · have hxiFalse : x i = false := by
            cases hxib : x i with
            | false => rfl
            | true => exact False.elim (hxi hxib)
          have hsuppSkip : supportedOn items x :=
            supportedOn_tail_of_eq_false hsupp hxiFalse
          have hskip :
              natBinarySocialWelfare bids x ≤ natBinarySocialWelfare bids skip :=
            ih capacity hsuppSkip hload
          by_cases hchoose : natBinarySocialWelfare bids take ≥ natBinarySocialWelfare bids skip
          · exact
              (by
                simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using
                  (le_trans hskip hchoose))
          · simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hskip
      · have hxiFalse : x i = false := by
          by_cases hxi : x i = true
          · have hwi' : w i ≤ natBinaryLoad w x := by
              rw [natBinaryLoad_eq_add_of_true w hxi]
              exact Nat.le_add_right _ _
            exact False.elim (hwi (le_trans hwi' hload))
          · cases hxib : x i with
            | false => rfl
            | true => exact False.elim (hxi hxib)
        have hsuppTail : supportedOn items x :=
          supportedOn_tail_of_eq_false hsupp hxiFalse
        simpa [dpSolveList, hwi] using ih capacity hsuppTail hload

/-- The allocation obtained by running the dynamic program on the finite agent
set. -/
noncomputable def dynamicProgrammingOptimalAllocation
    (w bids : ι → Nat) (capacity : Nat) : BinaryAllocation ι :=
  dpSolveList w bids ((Finset.univ : Finset ι).toList) capacity

/-- The social welfare achieved by the dynamic-programming allocation. -/
noncomputable def dynamicProgrammingOptimalValue
    (w bids : ι → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare bids (dynamicProgrammingOptimalAllocation w bids capacity)

/-- The dynamic-programming allocation satisfies the knapsack capacity
constraint. -/
theorem dynamicProgrammingOptimalAllocation_feasible
    (w bids : ι → Nat) (capacity : Nat) :
    natBinaryLoad w (dynamicProgrammingOptimalAllocation w bids capacity) ≤ capacity := by
  classical
  simpa [dynamicProgrammingOptimalAllocation] using
    (dpSolveList_feasible (w := w) (bids := bids)
      ((Finset.univ : Finset ι).toList)
      (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset ι))))
      capacity)

/-- The dynamic-programming allocation maximizes integer social welfare among
all feasible binary allocations. -/
theorem dynamicProgrammingOptimalAllocation_optimal
    (w bids : ι → Nat) (capacity : Nat) {x : BinaryAllocation ι}
    (hfeas : natBinaryLoad w x ≤ capacity) :
    natBinarySocialWelfare bids x ≤
      natBinarySocialWelfare bids (dynamicProgrammingOptimalAllocation w bids capacity) := by
  classical
  simpa [dynamicProgrammingOptimalAllocation] using
    (dpSolveList_optimal (w := w) (bids := bids)
      ((Finset.univ : Finset ι).toList)
      (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset ι))))
      capacity
      (x := x)
      (by intro i _hi; exact Finset.mem_toList.mpr (Finset.mem_univ i))
      hfeas)

end DynamicProgramming

section GreedyApproximation

variable [LinearOrder ι] [Nonempty ι]

/-- Real-valued knapsack data induced by natural weights and capacity. -/
def natAuctionData (w : ι → Nat) (capacity : Nat) : Data ι where
  weight := fun i => (w i : ℝ)
  capacity := capacity

/-- Natural-number bids viewed as real-valued bids. -/
def realBidOfNat (bids : ι → Nat) : ι → ℝ :=
  fun i => (bids i : ℝ)

/-- The integral greedy prefix algorithm: process items in order, take each
whole item if it fits, and halt when the first item fails to fit. -/
def integralGreedyList (w : ι → Nat) : List ι → Nat → BinaryAllocation ι
  | [], _ => fun _ => false
  | i :: items, remaining =>
      if w i ≤ remaining then
        Function.update (integralGreedyList w items (remaining - w i)) i true
      else
        fun _ => false
termination_by items _ => items.length

/-- The ratio-sorted integral greedy allocation. -/
noncomputable def integralGreedyAllocation
    (w bids : ι → Nat) (capacity : Nat) : BinaryAllocation ι :=
  integralGreedyList w (sortedAgentsByRatio (natAuctionData w capacity)
    (realBidOfNat bids)) capacity

/-- Welfare of the ratio-sorted integral greedy allocation. -/
noncomputable def integralGreedyValue (w bids : ι → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare bids (integralGreedyAllocation w bids capacity)

/-- Highest single-item value. -/
noncomputable def highestBidValue (bids : ι → Nat) : Nat :=
  Finset.sup' Finset.univ Finset.univ_nonempty bids

omit [DecidableEq ι] [LinearOrder ι] in
theorem le_highestBidValue (bids : ι → Nat) (i : ι) :
    bids i ≤ highestBidValue bids := by
  classical
  exact Finset.le_sup' (s := Finset.univ) (f := bids) (by simp)

omit [DecidableEq ι] [LinearOrder ι] [Nonempty ι] in
theorem fractionalSocialWelfare_realBidOfNat_binaryToAllocation
    (bids : ι → Nat) (x : BinaryAllocation ι) :
    fractionalSocialWelfare (realBidOfNat bids) (binaryToAllocation x) =
      natBinarySocialWelfare bids x := by
  simp [fractionalSocialWelfare, realBidOfNat, binaryToAllocation, natBinarySocialWelfare]

/-- Fractional greedy prefix algorithm on a natural remaining capacity. -/
noncomputable def natFractionalGreedyList (w : ι → Nat) : List ι → Nat → ι → ℝ
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if w i ≤ remaining then
        Function.update (natFractionalGreedyList w items (remaining - w i)) i 1
      else
        fun j => if j = i then (remaining : ℝ) / w i else 0
termination_by items _ => items.length

/-- The ratio-sorted fractional greedy allocation on natural-number data. -/
noncomputable def natFractionalGreedyAllocation
    (w bids : ι → Nat) (capacity : Nat) : ι → ℝ :=
  natFractionalGreedyList w (sortedAgentsByRatio (natAuctionData w capacity)
    (realBidOfNat bids)) capacity

/-- Welfare of the ratio-sorted fractional greedy allocation. -/
noncomputable def natFractionalGreedyValue
    (w bids : ι → Nat) (capacity : Nat) : ℝ :=
  fractionalSocialWelfare (realBidOfNat bids)
    (natFractionalGreedyAllocation w bids capacity)

/-- A real-valued allocation is supported on a list if every nonzero coordinate
appears in that list. -/
private def fractionalSupportedOn (items : List ι) (x : ι → ℝ) : Prop :=
  ∀ i, x i ≠ 0 → i ∈ items

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Nonempty ι] in
private theorem eq_zero_of_fractionalSupportedOn_of_not_mem
    {items : List ι} {x : ι → ℝ}
    (hsupp : fractionalSupportedOn items x) {i : ι} (hi : i ∉ items) :
    x i = 0 := by
  by_contra hxi
  exact hi (hsupp i hxi)

omit [Fintype ι] [LinearOrder ι] [Nonempty ι] in
private theorem integralGreedyList_supportedOn (w : ι → Nat) :
    ∀ items remaining, supportedOn items (integralGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [integralGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : integralGreedyList w items (remaining - w i) j = true := by
            simpa [integralGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · simp [integralGreedyList, hfit] at hj

omit [Fintype ι] [LinearOrder ι] [Nonempty ι] in
private theorem natFractionalGreedyList_supportedOn (w : ι → Nat) :
    ∀ items remaining,
      fractionalSupportedOn items (natFractionalGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [natFractionalGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : natFractionalGreedyList w items (remaining - w i) j ≠ 0 := by
            simpa [natFractionalGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · by_cases hji : j = i
        · subst hji
          simp
        · exfalso
          simp [natFractionalGreedyList, hfit, hji] at hj

omit [LinearOrder ι] [Nonempty ι] in
private theorem fractionalSocialWelfare_update_one_of_zero
    (bids : ι → ℝ) {x : ι → ℝ} {i : ι}
    (hxi : x i = 0) :
    fractionalSocialWelfare bids (Function.update x i 1) =
      bids i + fractionalSocialWelfare bids x := by
  rw [fractionalSocialWelfare, fractionalSocialWelfare,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hs :
      Finset.sum (Finset.univ.erase i) (fun j => bids j * Function.update x i 1 j) =
        Finset.sum (Finset.univ.erase i) (fun j => bids j * x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [hs]
  simp [Function.update, hxi]

omit [LinearOrder ι] [Nonempty ι] in
private theorem fractionalSocialWelfare_singleton
    (bids : ι → ℝ) (i : ι) (α : ℝ) :
    fractionalSocialWelfare bids (fun j => if j = i then α else 0) = bids i * α := by
  rw [fractionalSocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hs :
      Finset.sum (Finset.univ.erase i) (fun j => bids j * (if j = i then α else 0)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [hji]
  rw [hs]
  simp

omit [LinearOrder ι] in
private theorem natFractionalGreedyList_le_integralGreedyList_plus_highest
    (w bids : ι → Nat) (hwpos : ∀ i, 0 < w i) :
    ∀ {items : List ι}, items.Nodup → ∀ remaining,
      fractionalSocialWelfare (realBidOfNat bids) (natFractionalGreedyList w items remaining) ≤
        (natBinarySocialWelfare bids (integralGreedyList w items remaining) : ℝ) +
          highestBidValue bids := by
  intro items hitems
  induction items with
  | nil =>
      intro remaining
      have hnil :
          (0 : ℝ) ≤
            (natBinarySocialWelfare bids (fun _ => false) : ℝ) + highestBidValue bids := by
        positivity
      simpa [natFractionalGreedyList, integralGreedyList, fractionalSocialWelfare] using hnil
  | cons i items ih =>
      intro remaining
      have hnotin : i ∉ items := (List.nodup_cons.mp hitems).1
      have htailNodup : items.Nodup := (List.nodup_cons.mp hitems).2
      by_cases hfit : w i ≤ remaining
      · have hfracTail := ih htailNodup (remaining - w i)
        have hfracZero : natFractionalGreedyList w items (remaining - w i) i = 0 :=
          eq_zero_of_fractionalSupportedOn_of_not_mem
            (natFractionalGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintFalse : integralGreedyList w items (remaining - w i) i = false :=
          eq_false_of_supportedOn_of_not_mem
            (integralGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintEq :
            (natBinarySocialWelfare bids (integralGreedyList w (i :: items) remaining) : ℝ) =
              (bids i : ℝ) +
                natBinarySocialWelfare bids (integralGreedyList w items (remaining - w i)) := by
          exact_mod_cast
            (show natBinarySocialWelfare bids (integralGreedyList w (i :: items) remaining) =
                bids i + natBinarySocialWelfare bids
                  (integralGreedyList w items (remaining - w i)) by
              simpa [integralGreedyList, hfit] using
                (natBinarySocialWelfare_update_true_of_false
                  (bids := bids) (x := integralGreedyList w items (remaining - w i))
                  (i := i) hintFalse))
        calc
          fractionalSocialWelfare (realBidOfNat bids)
              (natFractionalGreedyList w (i :: items) remaining)
              = (bids i : ℝ) +
                  fractionalSocialWelfare (realBidOfNat bids)
                    (natFractionalGreedyList w items (remaining - w i)) := by
                  simp [natFractionalGreedyList, hfit]
                  simpa [realBidOfNat] using
                    (fractionalSocialWelfare_update_one_of_zero
                      (bids := realBidOfNat bids)
                      (x := natFractionalGreedyList w items (remaining - w i))
                      (i := i) hfracZero)
          _ ≤ (bids i : ℝ) +
                ((natBinarySocialWelfare bids
                    (integralGreedyList w items (remaining - w i)) : ℝ) +
                  highestBidValue bids) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left hfracTail (bids i : ℝ)
          _ = (natBinarySocialWelfare bids
                (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue bids := by
                rw [hintEq]
                ring
      · have hwipos : 0 < w i := hwpos i
        have hrem_le : remaining ≤ w i := Nat.le_of_lt (lt_of_not_ge hfit)
        have hratio_le_one : (remaining : ℝ) / w i ≤ 1 :=
          (div_le_one (by exact_mod_cast hwipos)).2 (by exact_mod_cast hrem_le)
        calc
          fractionalSocialWelfare (realBidOfNat bids)
              (natFractionalGreedyList w (i :: items) remaining)
              = (bids i : ℝ) * ((remaining : ℝ) / w i) := by
                  simp [natFractionalGreedyList, hfit]
                  simp [fractionalSocialWelfare_singleton, realBidOfNat]
          _ ≤ bids i := by
              have hmul :
                  (bids i : ℝ) * ((remaining : ℝ) / w i) ≤ (bids i : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hratio_le_one (show 0 ≤ (bids i : ℝ) by positivity)
              simpa using hmul
          _ ≤ highestBidValue bids := by
              exact_mod_cast le_highestBidValue bids i
          _ ≤ (natBinarySocialWelfare bids (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue bids := by
              have hnonneg :
                  (0 : ℝ) ≤
                    (natBinarySocialWelfare bids
                      (integralGreedyList w (i :: items) remaining) : ℝ) := by
                positivity
              exact le_add_of_nonneg_left hnonneg

private theorem natFractionalGreedyValue_le_integralGreedyValue_plus_highest
    (w bids : ι → Nat) (capacity : Nat) (hwpos : ∀ i, 0 < w i) :
    natFractionalGreedyValue w bids capacity ≤
      integralGreedyValue w bids capacity + highestBidValue bids := by
  classical
  have hnodup :
      (sortedAgentsByRatio (natAuctionData w capacity) (realBidOfNat bids)).Nodup := by
    simpa [sortedAgentsByRatio] using
      ((List.nodup_mergeSort
          (l := (Finset.univ : Finset ι).toList)
          (le := fun i j =>
            decide
              (ratioTieKey (natAuctionData w capacity) (realBidOfNat bids) i ≤
                ratioTieKey (natAuctionData w capacity) (realBidOfNat bids) j))).2
        (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset ι)))))
  simpa [natFractionalGreedyValue, natFractionalGreedyAllocation,
    integralGreedyValue, integralGreedyAllocation] using
    (natFractionalGreedyList_le_integralGreedyList_plus_highest
      (w := w) (bids := bids) hwpos hnodup capacity)

omit [LinearOrder ι] [Nonempty ι] in
theorem dynamicProgrammingOptimalAllocation_fractionalFeasible
    (w bids : ι → Nat) (capacity : Nat) :
    fractionalFeasible (natAuctionData w capacity)
      (binaryToAllocation (dynamicProgrammingOptimalAllocation w bids capacity)) := by
  constructor
  · intro i
    by_cases hxi : dynamicProgrammingOptimalAllocation w bids capacity i <;>
      simp [binaryToAllocation, hxi]
  · have hfeas :=
      dynamicProgrammingOptimalAllocation_feasible (w := w) (bids := bids) (capacity := capacity)
    simpa [natAuctionData, natBinaryLoad, binaryToAllocation] using
      (show ((natBinaryLoad w (dynamicProgrammingOptimalAllocation w bids capacity) : Nat) : ℝ) ≤
          capacity by
        exact_mod_cast hfeas)

/-- The ratio-sorted integral greedy algorithm, compared with the highest
single-value item, achieves a `1/2`-approximation to the DP-optimal `0/1`
knapsack welfare, assuming the fractional greedy allocation is optimal for the
fractional relaxation. -/
theorem integralGreedy_halfApprox_dpOptimal
    (w bids : ι → Nat) (capacity : Nat)
    (hwpos : ∀ i, 0 < w i)
    (hfracOptimal :
      ∀ x : ι → ℝ, fractionalFeasible (natAuctionData w capacity) x →
        fractionalSocialWelfare (realBidOfNat bids) x ≤
          natFractionalGreedyValue w bids capacity) :
    ((dynamicProgrammingOptimalValue w bids capacity : ℝ) / 2) ≤
      max (integralGreedyValue w bids capacity) (highestBidValue bids) := by
  have hdp_le_frac :
      (dynamicProgrammingOptimalValue w bids capacity : ℝ) ≤
        natFractionalGreedyValue w bids capacity := by
    calc
      (dynamicProgrammingOptimalValue w bids capacity : ℝ)
          = fractionalSocialWelfare (realBidOfNat bids)
              (binaryToAllocation (dynamicProgrammingOptimalAllocation w bids capacity)) := by
                norm_num [dynamicProgrammingOptimalValue,
                  fractionalSocialWelfare_realBidOfNat_binaryToAllocation]
      _ ≤ natFractionalGreedyValue w bids capacity :=
          hfracOptimal _
            (dynamicProgrammingOptimalAllocation_fractionalFeasible
              (w := w) (bids := bids) (capacity := capacity))
  have hfrac_le :
      natFractionalGreedyValue w bids capacity ≤
        integralGreedyValue w bids capacity + highestBidValue bids :=
    natFractionalGreedyValue_le_integralGreedyValue_plus_highest
      (w := w) (bids := bids) (capacity := capacity) hwpos
  have hsum_le_twomax :
      ((integralGreedyValue w bids capacity : Nat) : ℝ) + highestBidValue bids ≤
        2 * max (integralGreedyValue w bids capacity) (highestBidValue bids) := by
    have h1 :
        ((integralGreedyValue w bids capacity : Nat) : ℝ) ≤
          max (integralGreedyValue w bids capacity) (highestBidValue bids) := by
      exact_mod_cast le_max_left _ _
    have h2 : (highestBidValue bids : ℝ) ≤
        max (integralGreedyValue w bids capacity) (highestBidValue bids) := by
      exact_mod_cast le_max_right _ _
    have h12 := add_le_add h1 h2
    simpa [two_mul] using h12
  have hdp_le_sum : (dynamicProgrammingOptimalValue w bids capacity : ℝ) ≤
      integralGreedyValue w bids capacity + highestBidValue bids :=
    le_trans hdp_le_frac hfrac_le
  have hdp_le_twomax : (dynamicProgrammingOptimalValue w bids capacity : ℝ) ≤
      2 * max (integralGreedyValue w bids capacity) (highestBidValue bids) :=
    le_trans hdp_le_sum hsum_le_twomax
  nlinarith

end GreedyApproximation

end KnapsackAuction

end GameTheory
