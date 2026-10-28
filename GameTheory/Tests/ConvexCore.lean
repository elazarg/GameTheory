module

/-
# Convex-core controls

Complementarity can make marginal core allocations depend on the order even
when singleton worth is negative. Empty player types require no special case
in the existence theorem. The majority game's empty core obstructs convexity.
-/

public import GameTheory.Cooperative.Convex

@[expose] public section

namespace GameTheory.Tests.ConvexCore

open GameTheory.CoalitionalGame

/-- A player who is costly alone can still contribute a surplus with a partner. -/
def complementary : CoalitionalGame Bool where
  value coalition := (if false ∈ coalition then -1 else 0) +
    (if true ∈ coalition then -2 else 0) +
    (if false ∈ coalition ∧ true ∈ coalition then 6 else 0)
  value_empty := by simp

theorem complementary_isConvex : complementary.IsConvex := by
  intro first second
  fin_cases first <;> fin_cases second <;> norm_num [complementary]

theorem negative_singletons :
    complementary.value {false} = -1 ∧ complementary.value {true} = -2 := by
  norm_num [complementary]

/-- Together the players earn strictly more than their separate worth. -/
theorem genuine_complementarity :
    complementary.value {false} + complementary.value {true} <
      complementary.value Finset.univ := by
  norm_num [complementary]

/-- The ordinary Boolean order places `false` first. -/
abbrev forwardOrder : LinearOrder Bool := inferInstance

/-- Reversing the order places `true` first. -/
abbrev reverseOrder : LinearOrder Bool := (inferInstance : LinearOrder Boolᵒᵈ)

theorem forward_payments :
    complementary.marginalAllocation forwardOrder false = -1 ∧
      complementary.marginalAllocation forwardOrder true = 4 := by
  norm_num [marginalAllocation, marginalContribution, forwardOrder, complementary,
    Fintype.univ_bool, Bool.lt_iff]

theorem reverse_payments :
    complementary.marginalAllocation reverseOrder false = 5 ∧
      complementary.marginalAllocation reverseOrder true = -2 := by
  have beforeFalse : Finset.univ.filter (fun earlier => reverseOrder.lt earlier false) =
      ({true} : Finset Bool) := by decide
  have beforeTrue : Finset.univ.filter (fun earlier => reverseOrder.lt earlier true) =
      (∅ : Finset Bool) := by decide
  simp only [marginalAllocation, beforeFalse, beforeTrue]
  norm_num [marginalContribution, complementary]

theorem both_orders_in_core :
    IsInCore complementary (complementary.marginalAllocation forwardOrder) ∧
      IsInCore complementary (complementary.marginalAllocation reverseOrder) :=
  ⟨complementary_isConvex.marginalAllocation_isInCore forwardOrder,
    complementary_isConvex.marginalAllocation_isInCore reverseOrder⟩

theorem different_marginal_allocations :
    complementary.marginalAllocation forwardOrder ≠
      complementary.marginalAllocation reverseOrder := by
  intro equal
  have same := congrFun equal false
  rw [forward_payments.1, reverse_payments.1] at same
  norm_num at same

/-- The unique empty-player game has zero worth. -/
def emptyGame : CoalitionalGame Empty where
  value _ := 0
  value_empty := rfl

theorem emptyGame_isConvex : emptyGame.IsConvex := by
  intro first second
  norm_num [emptyGame]

theorem empty_players_have_core :
    ∃ allocation : Allocation Empty, IsInCore emptyGame allocation :=
  emptyGame_isConvex.exists_core

/-- A game with an empty core cannot satisfy the convexity hypothesis. -/
theorem majority_not_isConvex : ¬ majorityGame.IsConvex := by
  intro convex
  obtain ⟨allocation, core⟩ := convex.exists_core
  exact majorityGame_core_empty allocation core

end GameTheory.Tests.ConvexCore
