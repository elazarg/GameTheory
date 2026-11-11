module

/-
# Joint acceptance and contraction

Every contract in an accepted set is accepted together. This is distinct from
a correspondence listing alternative bundles. The formulas below match the
set-based contract-choice conditions in the mathematical-economics consumer.
-/

public import GameTheory.Math.FiniteChoice
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Tauto

@[expose] public section

namespace GameTheory.Experimental.ContractChoice

open GameTheory.Math

/-- Accept the two highest-priority offered contracts, with priority 0, 1, 2. -/
def quotaSet (offers : Set (Fin 3)) : Set (Fin 3) :=
  {contract | contract ∈ offers ∧
    (contract = 2 → ¬ (0 ∈ offers ∧ 1 ∈ offers))}

theorem quota_subset (offers : Set (Fin 3)) : quotaSet offers ⊆ offers :=
  fun _ accepted => accepted.1

@[simp] theorem zero_accepted (offers : Set (Fin 3)) : 0 ∈ quotaSet offers ↔ 0 ∈ offers := by
  simp [quotaSet]

@[simp] theorem one_accepted (offers : Set (Fin 3)) : 1 ∈ quotaSet offers ↔ 1 ∈ offers := by
  simp [quotaSet]

/-- Contraction of offers preserves every retained accepted contract. -/
theorem quota_chernoff {small large : Set (Fin 3)} (subset : small ⊆ large) :
    quotaSet large ∩ small ⊆ quotaSet small := by
  rintro contract ⟨⟨_, rejection⟩, offered⟩
  exact ⟨offered, fun last top => rejection last ⟨subset top.1, subset top.2⟩⟩

/-- The same law in the consumer's rejection-monotonicity formulation. -/
theorem quota_substitutable {contract : Fin 3} {small large : Set (Fin 3)}
    (subset : small ⊆ large) (rejected : contract ∉ quotaSet (insert contract small)) :
    contract ∉ quotaSet (insert contract large) := by
  intro accepted
  exact rejected (quota_chernoff (Set.insert_subset_insert subset)
    ⟨accepted, Set.mem_insert _ _⟩)

/-- Removing only rejected offers does not change joint acceptance. -/
theorem quota_consistent {small large : Set (Fin 3)}
    (retained : quotaSet large ⊆ small) (subset : small ⊆ large) :
    quotaSet small = quotaSet large := by
  ext contract
  constructor
  · rintro ⟨offered, rejection⟩
    refine ⟨subset offered, fun last top => rejection last ?_⟩
    exact ⟨retained ((zero_accepted large).mpr top.1),
      retained ((one_accepted large).mpr top.2)⟩
  · intro accepted
    exact quota_chernoff subset ⟨accepted, retained accepted⟩

theorem quota_pathIndependent (first second : Set (Fin 3)) :
    quotaSet (first ∪ second) = quotaSet (quotaSet first ∪ second) := by
  ext contract
  fin_cases contract <;> simp [quotaSet]
  tauto

/-- Joint quota acceptance is not greatest-element item choice under WARP. -/
theorem quota_not_item_weakAxiom :
    ¬ FiniteChoice.WeakAxiom
      (fun offers : Finset (Fin 3) => quotaSet (offers : Set (Fin 3))) := by
  intro consistent
  have impossible := consistent {1, 2} {0, 1, 2} 2 1
    (by simp [quotaSet]) (by simp) (by simp [quotaSet]) (by simp)
  simp [quotaSet] at impossible

/-- Sen's expansion formula fails even though contraction and IRC hold. -/
theorem quota_not_expansion :
    ¬ ∀ first second : Set (Fin 3),
      quotaSet first ∩ quotaSet second ⊆ quotaSet (first ∪ second) := by
  intro expansion
  have impossible : (2 : Fin 3) ∈ quotaSet
      (({0, 2} : Set (Fin 3)) ∪ {1, 2}) :=
    expansion {0, 2} {1, 2} ⟨by simp [quotaSet], by simp [quotaSet]⟩
  simp [quotaSet] at impossible

/-- Complementary contracts are accepted together and neither is accepted alone. -/
def complements (offers : Set Bool) : Set Bool :=
  {contract | contract ∈ offers ∧ false ∈ offers ∧ true ∈ offers}

theorem complements_subset (offers : Set Bool) : complements offers ⊆ offers :=
  fun _ accepted => accepted.1

theorem complements_not_chernoff :
    ¬ ∀ small large : Set Bool, small ⊆ large →
      complements large ∩ small ⊆ complements small := by
  intro contraction
  have impossible : true ∈ complements {true} :=
    contraction {true} Set.univ (Set.subset_univ _)
      ⟨by simp [complements], by simp⟩
  simp [complements] at impossible

/-- This is the acceptance step used to reduce a joint block to a single
contract. It needs contraction, not a game arena or an interpersonal score. -/
theorem joint_acceptance_singleton {Contract : Type*}
    (choose : Set Contract → Set Contract)
    (contraction : ∀ small large : Set Contract, small ⊆ large →
      choose large ∩ small ⊆ choose small)
    {incumbent proposed : Set Contract}
    (accepted : proposed ⊆ choose (incumbent ∪ proposed)) :
    ∀ contract ∈ proposed, contract ∈ choose (insert contract incumbent) := by
  intro contract member
  apply contraction (insert contract incumbent) (incumbent ∪ proposed)
    (Set.insert_subset (Or.inr member) Set.subset_union_left)
  exact ⟨accepted member, Set.mem_insert _ _⟩

/-- Rational choice over whole bundles cannot replace the contraction premise:
the complementary pair is accepted jointly, but no singleton is accepted. -/
theorem complements_joint_without_singletons :
    Set.univ ⊆ complements ((∅ : Set Bool) ∪ Set.univ) ∧
    ¬ ∀ contract ∈ (Set.univ : Set Bool),
      contract ∈ complements (insert contract (∅ : Set Bool)) := by
  constructor
  · simp [complements]
  · intro singletons
    have impossible := singletons true (Set.mem_univ _)
    simp [complements] at impossible

end GameTheory.Experimental.ContractChoice
