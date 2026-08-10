/-
# The Shapley--Shubik power index

This leaf is the intersection of simple voting games and the Shapley value.
The standalone Banzhaf construction therefore does not inherit the full
Shapley characterization dependency.
-/

import GameTheory.Cooperative.Banzhaf
import GameTheory.Core.Shapley

namespace GameTheory.CoalitionalGame

open scoped BigOperators

universe ua

variable {Agent : Type ua} [Fintype Agent] [DecidableEq Agent]

/-- The Shapley--Shubik power index of a simple game. -/
noncomputable def shapleyShubikIndex
    (G : SimpleGame Agent) : Allocation Agent :=
  G.1.shapleyValue

/-- Shapley--Shubik power is efficient. -/
theorem shapleyShubikIndex_sum_eq_one
    (G : SimpleGame Agent) :
    ∑ agent, shapleyShubikIndex G agent = 1 := by
  simp only [shapleyShubikIndex]
  rw [G.1.shapleyValue_efficient, G.2.grandWinning]

/-- A null agent has zero Shapley--Shubik power. -/
theorem shapleyShubikIndex_null
    (G : SimpleGame Agent) {agent : Agent} (hnull : G.1.IsNull agent) :
    shapleyShubikIndex G agent = 0 := by
  exact G.1.shapleyValue_null hnull

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
