module

/-
# Balancedness with negative worth and the empty-player boundary

The two-player game has a negative singleton value and a strict gain from
cooperation. Balancedness is checked directly from its weight constraints,
then supplies a core allocation through the general converse theorem.
The majority-game obstruction and empty-player boundary are retained.
-/

public import GameTheory.Tests.Balancedness

@[expose] public section

noncomputable section

namespace GameTheory.Tests.BondarevaShapley

open scoped BigOperators

def cooperationGame : CoalitionalGame Bool where
  value coalition := if coalition = Finset.univ then 3 else
    if false ∈ coalition then -2 else if true ∈ coalition then 1 else 0
  value_empty := by rw [ite_eq_right (by decide)]; rfl

private theorem all_coalitions : (Finset.univ : Finset (Finset Bool)) =
    {∅, {false}, {true}, Finset.univ} := by decide

theorem cooperationGame_isBalanced : cooperationGame.IsBalanced := by
  intro weights balanced
  have falseCover := balanced.2 false
  have trueCover := balanced.2 true
  have falseNonneg := balanced.1 {false}
  have coverFalse : (Finset.univ : Finset (Finset Bool)).filter (false ∈ ·) =
      {{false}, Finset.univ} := by decide
  have coverTrue : (Finset.univ : Finset (Finset Bool)).filter (true ∈ ·) =
      {{true}, Finset.univ} := by decide
  rw [coverFalse] at falseCover
  rw [coverTrue] at trueCover
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at falseCover trueCover
  rw [all_coalitions]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have empty_ne : (∅ : Finset Bool) ≠ Finset.univ := by decide
  have false_ne : ({false} : Finset Bool) ≠ Finset.univ := by decide
  have true_ne : ({true} : Finset Bool) ≠ Finset.univ := by decide
  simp only [cooperationGame, ite_eq_right empty_ne, ite_eq_right false_ne,
    ite_eq_right true_ne, Finset.notMem_empty, ↓reduceIte, Finset.mem_singleton,
    Bool.false_eq_true, mul_zero, zero_add]
  linarith

def emptyGame : CoalitionalGame Empty where
  value _ := 0
  value_empty := rfl

theorem emptyGame_isBalanced : emptyGame.IsBalanced := by
  intro weights _
  simp [emptyGame]

/-- Direct balancedness supplies a core without assuming any candidate
allocation. The negative singleton is retained in the downstream guarantees. -/
theorem cooperationGame_core_guarantees :
    ∃ allocation, IsInCore cooperationGame allocation ∧
      -2 ≤ allocation false ∧ 1 ≤ allocation true ∧
      allocation false + allocation true = 3 := by
  obtain ⟨allocation, core⟩ := cooperationGame_isBalanced.exists_core
  refine ⟨allocation, core, ?_, ?_, ?_⟩
  · have bound := core.individually_rational false
    have different : ({false} : Finset Bool) ≠ Finset.univ := by decide
    simpa only [cooperationGame, ite_eq_right different, Finset.mem_singleton,
      ↓reduceIte] using bound
  · have bound := core.individually_rational true
    have different : ({true} : Finset Bool) ≠ Finset.univ := by decide
    simpa only [cooperationGame, ite_eq_right different, Finset.mem_singleton,
      Bool.false_eq_true, ↓reduceIte] using bound
  · simpa only [payout, Fintype.sum_bool, cooperationGame, ↓reduceIte,
      add_comm] using core.efficient

/-- Empty player types do not require a separate nonemptiness premise. -/
theorem emptyGame_core_exists : ∃ allocation, IsInCore emptyGame allocation :=
  emptyGame_isBalanced.exists_core

/-- The full equivalence recovers the three-player majority obstruction. -/
theorem majority_core_empty : ¬ ∃ allocation, IsInCore majorityGame allocation := by
  rw [← majorityGame.isBalanced_iff_core_nonempty]
  exact Balancedness.majorityGame_not_isBalanced

end GameTheory.Tests.BondarevaShapley
