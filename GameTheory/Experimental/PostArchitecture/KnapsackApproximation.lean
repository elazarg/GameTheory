/-
# EXP-056 witness: repaired executable knapsack approximation

The deliberately hostile input includes an overweight, high-value item.  The
checked frontend accepts the explicit positive, duplicate-free list; every
successful result is then a feasible allocation and is within factor two of
the exact explicit-list solver.  This records the operational boundary without
asking the kernel to normalize a sorted finite-set value.
-/

import GameTheory.Mechanism.Knapsack

namespace GameTheory.Experimental.KnapsackApproximation

open GameTheory.Mechanism.Knapsack

private def hostileWeight : Fin 5 → ℕ
  | 0 => 11
  | 1 => 6
  | 2 => 5
  | 3 => 10
  | 4 => 4

private def hostileValue : Fin 5 → ℕ
  | 0 => 1000
  | 1 => 60
  | 2 => 49
  | 3 => 95
  | 4 => 35

private def hostileItems : List (Fin 5) := [0, 1, 2, 3, 4]

private theorem hostile_frontend_succeeds :
    (approximate? hostileWeight hostileValue hostileItems 10).isSome = true := by
  norm_num [approximate?, approximationInputValid, hostileItems, hostileWeight]
  decide

private theorem hostile_best_feasible_singleton :
    bestItem? hostileValue (feasibleItems hostileWeight 10 hostileItems) = some 3 := by
  norm_num [bestItem?, feasibleItems, hostileItems, hostileWeight, hostileValue]

theorem hostile_checked_result_exists :
    ∃ result : Finset (Fin 5),
      approximate? hostileWeight hostileValue hostileItems 10 = some result ∧
        result ⊆ hostileItems.toFinset ∧ load hostileWeight result ≤ 10 ∧
          welfare hostileValue
              (solveList hostileWeight hostileValue hostileItems 10) ≤
            2 * welfare hostileValue result := by
  rcases Option.isSome_iff_exists.mp hostile_frontend_succeeds with ⟨result, hresult⟩
  exact ⟨result, hresult,
    (approximate?_supported_feasible hostileWeight hostileValue hostileItems 10 hresult).1,
    (approximate?_supported_feasible hostileWeight hostileValue hostileItems 10 hresult).2,
    solveList_welfare_le_two_mul_approximate?
      hostileWeight hostileValue hostileItems 10 hresult⟩

example (result : Finset (Fin 5))
    (hresult : approximate? hostileWeight hostileValue hostileItems 10 = some result) :
    result ⊆ hostileItems.toFinset ∧ load hostileWeight result ≤ 10 :=
  approximate?_supported_feasible hostileWeight hostileValue hostileItems 10 hresult

example (result : Finset (Fin 5))
    (hresult : approximate? hostileWeight hostileValue hostileItems 10 = some result) :
    (0 : Fin 5) ∉ result := by
  intro hoverweight
  have hfeasible :=
    (approximate?_supported_feasible hostileWeight hostileValue hostileItems 10 hresult).2
  have hsingle : ({0} : Finset (Fin 5)) ⊆ result := by
    intro item hitem
    rw [Finset.mem_singleton.mp hitem]
    exact hoverweight
  have hload : load hostileWeight ({0} : Finset (Fin 5)) ≤
      load hostileWeight result := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsingle
      (by intro item _ _; exact Nat.zero_le _)
  have hsingleLoad : load hostileWeight ({0} : Finset (Fin 5)) = 11 := by
    norm_num [aggregate, hostileWeight]
  rw [hsingleLoad] at hload
  omega

example (result : Finset (Fin 5))
    (hresult : approximate? hostileWeight hostileValue hostileItems 10 = some result) :
    welfare hostileValue (solveList hostileWeight hostileValue hostileItems 10) ≤
      2 * welfare hostileValue result :=
  solveList_welfare_le_two_mul_approximate? hostileWeight hostileValue hostileItems 10 hresult


end GameTheory.Experimental.KnapsackApproximation
