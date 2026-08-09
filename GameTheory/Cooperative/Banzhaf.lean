/-
# Banzhaf and Shapley--Shubik power indices

The probabilistic Banzhaf value weights every coalition of the other agents
equally.  On simple coalitional games, the Shapley value is the
Shapley--Shubik power index.  Both constructions reuse the canonical
`CoalitionalGame`; this opt-in module introduces no second voting-game carrier.

The theorem family is adapted from
`reference/GameTheory-v1/GameTheory/Cooperative/CoalitionalGame/Banzhaf.lean`
at pinned commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Core.Shapley
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace GameTheory.CoalitionalGame

open scoped BigOperators

universe ua

variable {Agent : Type ua} [Fintype Agent] [DecidableEq Agent]

/-- The unnormalized probabilistic Banzhaf value: the average marginal
contribution over all coalitions not containing the agent. -/
noncomputable def probabilisticBanzhafValue
    (G : CoalitionalGame Agent) : Allocation Agent :=
  fun agent =>
    (∑ coalition ∈
        (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∉ coalition),
      G.marginalContribution agent coalition) /
        (2 ^ (Fintype.card Agent - 1) : ℝ)

/-- A null agent has zero probabilistic Banzhaf value. -/
theorem probabilisticBanzhafValue_null
    (G : CoalitionalGame Agent) {agent : Agent}
    (hnull : G.IsNull agent) :
    G.probabilisticBanzhafValue agent = 0 := by
  simp only [probabilisticBanzhafValue]
  rw [show
    (∑ coalition ∈
        (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∉ coalition),
      G.marginalContribution agent coalition) = 0 from ?_, zero_div]
  apply Finset.sum_eq_zero
  intro coalition hcoalition
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoalition
  exact hnull coalition hcoalition

/-- Coalitions not containing an agent are precisely the subsets of the
remaining agents. -/
theorem filter_notMem_eq_powerset_compl (agent : Agent) :
    (Finset.univ : Finset (Finset Agent)).filter
        (fun coalition => agent ∉ coalition) =
      ((Finset.univ : Finset Agent) \ {agent}).powerset := by
  ext coalition
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powerset, Finset.subset_sdiff,
    Finset.disjoint_singleton_right]
  exact ⟨fun hnotmem => ⟨Finset.subset_univ coalition, hnotmem⟩,
    fun h => h.2⟩

/-- There are `2^(n-1)` coalitions not containing a fixed agent. -/
theorem card_filter_notMem (agent : Agent) :
    ((Finset.univ : Finset (Finset Agent)).filter
      (fun coalition => agent ∉ coalition)).card =
        2 ^ (Fintype.card Agent - 1) := by
  rw [filter_notMem_eq_powerset_compl, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.subset_univ ({agent} : Finset Agent)),
    Finset.card_univ, Finset.card_singleton]

/-- The probabilistic Banzhaf value is additive across games. -/
theorem probabilisticBanzhafValue_add
    (G H : CoalitionalGame Agent) (agent : Agent) :
    (add G H).probabilisticBanzhafValue agent =
      G.probabilisticBanzhafValue agent +
        H.probabilisticBanzhafValue agent := by
  simp only [probabilisticBanzhafValue, add, marginalContribution]
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- The probabilistic Banzhaf value commutes with scalar multiplication. -/
theorem probabilisticBanzhafValue_smul
    (scalar : ℝ) (G : CoalitionalGame Agent) (agent : Agent) :
    (smul scalar G).probabilisticBanzhafValue agent =
      scalar * G.probabilisticBanzhafValue agent := by
  simp only [probabilisticBanzhafValue, smul, marginalContribution]
  rw [show
    (∑ coalition ∈
        (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∉ coalition),
      (scalar * G.value (insert agent coalition) -
        scalar * G.value coalition)) =
      scalar *
        ∑ coalition ∈
          (Finset.univ : Finset (Finset Agent)).filter
            (fun coalition => agent ∉ coalition),
          (G.value (insert agent coalition) - G.value coalition) from ?_]
  · rw [mul_div_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- A simple coalitional game has Boolean values, is monotone, and makes the
grand coalition winning. -/
structure IsSimpleGame (G : CoalitionalGame Agent) : Prop where
  /-- Every coalition is losing or winning. -/
  boolean : ∀ coalition, G.value coalition = 0 ∨ G.value coalition = 1
  /-- A superset of a winning coalition remains winning. -/
  monotone : ∀ {smaller larger : Finset Agent},
    smaller ⊆ larger → G.value smaller = 1 → G.value larger = 1
  /-- The grand coalition is winning. -/
  grandWinning : G.value Finset.univ = 1

/-- The Shapley--Shubik power index of a simple game. -/
noncomputable def shapleyShubikIndex
    (G : CoalitionalGame Agent) (_simple : G.IsSimpleGame) : Allocation Agent :=
  G.shapleyValue

/-- Shapley--Shubik power is efficient. -/
theorem shapleyShubikIndex_sum_eq_one
    (G : CoalitionalGame Agent) (simple : G.IsSimpleGame) :
    ∑ agent, G.shapleyShubikIndex simple agent = 1 := by
  simp only [shapleyShubikIndex]
  rw [G.shapleyValue_efficient, simple.grandWinning]

/-- A null agent has zero Shapley--Shubik power. -/
theorem shapleyShubikIndex_null
    (G : CoalitionalGame Agent) (simple : G.IsSimpleGame)
    {agent : Agent} (hnull : G.IsNull agent) :
    G.shapleyShubikIndex simple agent = 0 := by
  exact G.shapleyValue_null hnull

/-- An agent has Banzhaf value one in their singleton unanimity game. -/
theorem unanimityGame_singleton_probabilisticBanzhafValue (agent : Agent) :
    (unanimityGame ({agent} : Finset Agent)
      (Finset.singleton_nonempty agent)).probabilisticBanzhafValue agent = 1 := by
  classical
  simp only [probabilisticBanzhafValue, marginalContribution, unanimityGame]
  have hmarginal :
      ∀ coalition ∈
        (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∉ coalition),
        (if ({agent} : Finset Agent) ⊆ insert agent coalition then (1 : ℝ) else 0) -
          (if ({agent} : Finset Agent) ⊆ coalition then 1 else 0) = 1 := by
    intro coalition hcoalition
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoalition
    have hinsert : ({agent} : Finset Agent) ⊆ insert agent coalition := by
      simp only [Finset.singleton_subset_iff, Finset.mem_insert, true_or]
    have hnotSubset : ¬ ({agent} : Finset Agent) ⊆ coalition := by
      simpa only [Finset.singleton_subset_iff] using hcoalition
    simp [hinsert, hnotSubset]
  rw [Finset.sum_congr rfl hmarginal, Finset.sum_const, nsmul_eq_mul,
    card_filter_notMem, mul_one]
  have hnonzero : (2 : ℝ) ^ (Fintype.card Agent - 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  push_cast
  exact div_self hnonzero

end GameTheory.CoalitionalGame
