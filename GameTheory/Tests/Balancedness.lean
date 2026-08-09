/-
Bondareva--Shapley hostile fixture.

The three pair coalitions of the majority game each receive weight one half.
Every player is therefore covered twice by half, while the weighted coalition
worth is three halves although the grand coalition is worth only one.
-/

import GameTheory.Cooperative.Balancedness
import Mathlib.Tactic

noncomputable section

namespace GameTheory.Tests.Balancedness

open scoped BigOperators

def pairHalf : Finset (Fin 3) → ℝ := fun coalition =>
  if coalition.card = 2 then 1 / 2 else 0

@[simp] theorem pair01_ne_univ : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := by
  intro heq
  have hcard := congrArg Finset.card heq
  norm_num at hcard

@[simp] theorem pair02_ne_univ : ({0, 2} : Finset (Fin 3)) ≠ Finset.univ := by
  intro heq
  have hmem : (1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by
    rw [heq]
    simp
  simp at hmem

@[simp] theorem pair12_ne_univ : ({1, 2} : Finset (Fin 3)) ≠ Finset.univ := by
  intro heq
  have hmem : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by
    rw [heq]
    simp
  simp at hmem

@[simp] theorem univ_ne_pair01 : (Finset.univ : Finset (Fin 3)) ≠ {0, 1} := pair01_ne_univ.symm
@[simp] theorem univ_ne_pair02 : (Finset.univ : Finset (Fin 3)) ≠ {0, 2} := pair02_ne_univ.symm
@[simp] theorem univ_ne_pair12 : (Finset.univ : Finset (Fin 3)) ≠ {1, 2} := pair12_ne_univ.symm

theorem half_add_half : (2 : ℝ)⁻¹ + 2⁻¹ = 1 := by
  norm_num

theorem three_halves : (2 : ℝ)⁻¹ + (2⁻¹ + 2⁻¹) = 3 / 2 := by
  norm_num

/-- Balanced weights cover each player once; they are not a probability law
over coalitions and need not have total mass one. -/
theorem pairHalf_total :
    ∑ coalition, pairHalf coalition = 3 / 2 := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, Finset.univ} by decide]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals simp [pairHalf, Finset.card_univ, three_halves] <;> try decide

theorem pairHalf_isBalancedCollection :
    CoalitionalGame.IsBalancedCollection pairHalf := by
  constructor
  · intro coalition
    unfold pairHalf
    split <;> positivity
  · intro agent
    fin_cases agent
    · show ∑ coalition ∈
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 0 ∈ coalition),
          pairHalf coalition = 1
      rw [show
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 0 ∈ coalition) =
          {{0}, {0, 1}, {0, 2}, Finset.univ} by decide]
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      all_goals simp [pairHalf, Finset.card_univ, half_add_half] <;> try decide
    · show ∑ coalition ∈
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 1 ∈ coalition),
          pairHalf coalition = 1
      rw [show
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 1 ∈ coalition) =
          {{1}, {0, 1}, {1, 2}, Finset.univ} by decide]
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      all_goals simp [pairHalf, Finset.card_univ, half_add_half] <;> try decide
    · show ∑ coalition ∈
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 2 ∈ coalition),
          pairHalf coalition = 1
      rw [show
        (Finset.univ : Finset (Finset (Fin 3))).filter (fun coalition => 2 ∈ coalition) =
          {{2}, {0, 2}, {1, 2}, Finset.univ} by decide]
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      all_goals simp [pairHalf, Finset.card_univ, half_add_half] <;> try decide

theorem pairHalf_weighted_majorityGame :
    ∑ coalition, pairHalf coalition * majorityGame.value coalition = 3 / 2 := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, Finset.univ} by decide]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  all_goals simp [pairHalf, majorityGame, Finset.card_univ, three_halves] <;> try decide

theorem majorityGame_not_isBalanced : ¬ majorityGame.IsBalanced := by
  intro hbalanced
  have hbound := hbalanced pairHalf pairHalf_isBalancedCollection
  rw [pairHalf_weighted_majorityGame] at hbound
  norm_num [majorityGame] at hbound

theorem majorityGame_not_exists_core_of_isBalanced :
    ¬ ∃ allocation : Allocation (Fin 3), IsInCore majorityGame allocation := by
  rintro ⟨allocation, hcore⟩
  exact majorityGame_not_isBalanced hcore.isBalanced

theorem majorityGame_not_exists_core_pointwise :
    ¬ ∃ allocation : Allocation (Fin 3), IsInCore majorityGame allocation := by
  rintro ⟨allocation, hcore⟩
  exact majorityGame_core_empty allocation hcore

end GameTheory.Tests.Balancedness
