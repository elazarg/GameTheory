/-
# Executable knapsack approximation frontend

This leaf repairs the executable shape of the pinned greedy approximation:
items are supplied explicitly, individually infeasible items are removed,
density order is computed without division, and the result is an actual
finite-set allocation chosen between the greedy prefix and a feasible
singleton.  Correctness and the approximation ratio live in a separate leaf.

The recovered theorem family is attributed to
`reference/GameTheory-v1/GameTheory/Auctions/Knapsack/Basic.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; the executable API is repaired
rather than source-compatible.
-/

import GameTheory.Mechanism.Knapsack.Aggregate
import Mathlib.Data.List.Sort

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

/-- Executable nonincreasing-density comparison.  Positive-weight items are
compared by cross multiplication; zero-weight items are placed first so the
comparison remains total on unchecked inputs. -/
def densityLE (weight value : Agent → ℕ) (left right : Agent) : Bool :=
  if weight left = 0 then true
  else if weight right = 0 then false
  else decide (value right * weight left ≤ value left * weight right)

/-- Executably sort an explicit item list by nonincreasing density. -/
def sortByDensity (weight value : Agent → ℕ) (items : List Agent) : List Agent :=
  items.mergeSort (densityLE weight value)

/-- Remove items that cannot form a feasible singleton. -/
def feasibleItems (weight : Agent → ℕ) (capacity : ℕ)
    (items : List Agent) : List Agent :=
  items.filter fun item => weight item ≤ capacity

/-- Data returned by the stop-at-first-failure greedy prefix scan. -/
structure GreedySplit (Agent : Type) where
  /-- Items taken completely before the first failure. -/
  taken : List Agent
  /-- The first item that does not fit, if one exists. -/
  rejected : Option Agent
  /-- Items strictly after the first rejected item. -/
  rest : List Agent
  /-- Capacity left after the completely taken prefix. -/
  remaining : ℕ

/-- Scan a fixed order, taking a prefix until the first item fails to fit. -/
def greedySplit (weight : Agent → ℕ) : List Agent → ℕ → GreedySplit Agent
  | [], remaining => ⟨[], none, [], remaining⟩
  | item :: items, remaining =>
      if weight item ≤ remaining then
        let tail := greedySplit weight items (remaining - weight item)
        ⟨item :: tail.taken, tail.rejected, tail.rest, tail.remaining⟩
      else
        ⟨[], some item, items, remaining⟩

/-- Finite-set allocation selected by the integral greedy prefix. -/
def greedyPrefix (weight : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) : Finset Agent :=
  (greedySplit weight items capacity).taken.toFinset

/-- A highest-value item from an explicit list, with ties favoring the earlier
item. -/
def bestItem? (value : Agent → ℕ) : List Agent → Option Agent
  | [] => none
  | item :: items =>
      match bestItem? value items with
      | none => some item
      | some best => if value best ≤ value item then some item else some best

/-- The singleton allocation represented by an optional item. -/
def singletonAllocation : Option Agent → Finset Agent
  | none => ∅
  | some item => {item}

/-- Return whichever of two concrete allocations has larger value. -/
def betterAllocation (value : Agent → ℕ)
    (left right : Finset Agent) : Finset Agent :=
  if welfare value right ≤ welfare value left then left else right

/-- Executable repaired half-approximation candidate.

The algorithm filters overweight items, sorts the remaining explicit list by
the division-free density comparison, computes the stop-at-first-failure
greedy prefix, and returns the better of that prefix and the highest-value
feasible singleton. -/
def approximate (weight value : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) : Finset Agent :=
  let eligible := feasibleItems weight capacity items
  let ordered := sortByDensity weight value eligible
  let greedy := greedyPrefix weight ordered capacity
  let singleton := singletonAllocation (bestItem? value eligible)
  betterAllocation value greedy singleton

/-- Executable validation for the approximation theorem's raw-input
requirements.  Density order itself is produced internally by the verified
sorter rather than trusted from the caller. -/
def approximationInputValid (weight : Agent → ℕ) (items : List Agent) : Bool :=
  decide items.Nodup && items.all fun item => decide (0 < weight item)

/-- Checked executable approximation frontend.  Invalid duplicate or
zero-weight inputs return `none`; every successful result is an actual
allocation. -/
def approximate? (weight value : Agent → ℕ) (items : List Agent)
    (capacity : ℕ) : Option (Finset Agent) :=
  if approximationInputValid weight items then
    some (approximate weight value items capacity)
  else
    none

private def exampleWeight : ℕ → ℕ
  | 0 => 11
  | 1 => 6
  | 2 => 5
  | 3 => 10
  | 4 => 4
  | _ => 1

private def exampleValue : ℕ → ℕ
  | 0 => 1000
  | 1 => 60
  | 2 => 49
  | 3 => 95
  | 4 => 35
  | _ => 0

#guard (approximate? exampleWeight exampleValue [0, 1, 2, 3, 4] 10).map
    (fun result =>
      (decide (0 ∈ result), decide (3 ∈ result),
        welfare exampleValue result, result.card)) =
  some (false, true, 95, 1)

end GameTheory.Mechanism.Knapsack
