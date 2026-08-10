/-
Executable 0/1 knapsack primitives. `solveList` is exact skip/take recursion
over the supplied list. It makes no memoization or asymptotic-complexity claim.
-/

import GameTheory.Mechanism.Knapsack.Aggregate

namespace GameTheory.Mechanism.Knapsack

variable {Agent : Type} [DecidableEq Agent]

/-- Exact explicit-list skip/take solver. Ties choose the take branch. -/
def solveList (weight value : Agent → ℕ) : List Agent → ℕ → Finset Agent
  | [], _ => ∅
  | agent :: agents, capacity =>
      if weight agent ≤ capacity then
        let skip := solveList weight value agents capacity
        let take := insert agent
          (solveList weight value agents (capacity - weight agent))
        if welfare value skip ≤ welfare value take then take else skip
      else
        solveList weight value agents capacity

private def exampleWeight : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | _ => 4

private def exampleValue : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | _ => 5

private example : (solveList exampleWeight exampleValue [0, 1, 2] 5).card = 2 := by
  decide

private example : solveList exampleWeight exampleValue [0, 1, 2] 5 = {0, 1} := by
  decide

end GameTheory.Mechanism.Knapsack
