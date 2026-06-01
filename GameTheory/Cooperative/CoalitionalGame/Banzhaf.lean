/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability
import GameTheory.Cooperative.CoalitionalGame.Shapley

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace CoalGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Banzhaf power index and simple games

The *Banzhaf index* (Penrose 1946, Banzhaf 1965) is an alternative power
index that weights every coalition equally instead of by Shapley's
arrival-order weights. On *simple games* — coalitional games whose values
lie in `{0, 1}`, modeling voting bodies — the Shapley value is known as
the **Shapley–Shubik power index** (Shapley–Shubik 1954). -/

/-- **Banzhaf power index**: an unweighted average of player `i`'s
marginal contributions to all coalitions not containing them.
Equals `(1/2^{n-1}) · Σ_{S : i ∉ S} (v(S ∪ {i}) - v(S))`. -/
noncomputable def banzhafIndex (G : CoalGame ι) (i : ι) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
      G.marginalContribution i S) / (2 ^ (Fintype.card ι - 1) : ℝ)

/-- A null player receives Banzhaf index `0`. -/
theorem banzhafIndex_null (G : CoalGame ι) {i : ι} (h : G.IsNull i) :
    G.banzhafIndex i = 0 := by
  simp only [banzhafIndex]
  rw [show (∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∉ S),
      G.marginalContribution i S) = 0 from ?_, zero_div]
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  exact h S hS

/-- The set of coalitions not containing player `i` (a Finset of Finsets)
equals the powerset of `univ \ {i}`: the elements are exactly the
subsets of the other players. -/
theorem filter_notMem_eq_powerset_compl (i : ι) :
    (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S) =
    ((Finset.univ : Finset ι) \ {i}).powerset := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
    Finset.subset_sdiff, Finset.disjoint_singleton_right]
  refine ⟨fun hi => ⟨Finset.subset_univ S, hi⟩, fun ⟨_, hi⟩ => hi⟩

/-- The number of coalitions not containing `i` is `2^(n-1)`. -/
theorem card_filter_notMem (i : ι) :
    ((Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S)).card =
      2 ^ (Fintype.card ι - 1) := by
  rw [filter_notMem_eq_powerset_compl, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.subset_univ ({i} : Finset ι)),
    Finset.card_univ, Finset.card_singleton]

/-- Banzhaf is additive across coalitional games, like Shapley. -/
theorem banzhafIndex_additive (G₁ G₂ : CoalGame ι) (i : ι) :
    (gameAdd G₁ G₂).banzhafIndex i = G₁.banzhafIndex i + G₂.banzhafIndex i := by
  simp only [banzhafIndex, gameAdd, marginalContribution]
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- Banzhaf scales with scalar multiplication. -/
theorem banzhafIndex_scalar (c : ℝ) (G : CoalGame ι) (i : ι) :
    (gameScalar c G).banzhafIndex i = c * G.banzhafIndex i := by
  simp only [banzhafIndex, gameScalar, marginalContribution]
  rw [show
    (∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∉ S),
      (c * G.v (insert i S) - c * G.v S)) =
    c * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∉ S),
      (G.v (insert i S) - G.v S) from ?_]
  · rw [mul_div_assoc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- A *simple game* (or *voting game*): values are restricted to `{0, 1}`
and the game is *monotone* — adding players to a winning coalition keeps
it winning. These are the natural arena for political power indices. -/
structure IsSimpleGame (G : CoalGame ι) : Prop where
  /-- Values are `0` or `1`. -/
  boolean : ∀ S, G.v S = 0 ∨ G.v S = 1
  /-- Monotonicity: supersets of winning coalitions remain winning. -/
  monotone : ∀ {S T : Finset ι}, S ⊆ T → G.v S = 1 → G.v T = 1
  /-- The grand coalition is winning. -/
  grandWinning : G.v Finset.univ = 1

/-- **Shapley–Shubik power index**: the Shapley value applied to a simple
(voting) game. It measures the probability that a uniformly random
ordering makes player `i` *pivotal* — i.e., the predecessors of `i`
form a losing coalition but together with `i` they form a winning one. -/
noncomputable def shapleyShubikIndex (G : CoalGame ι) (_h : G.IsSimpleGame)
    (i : ι) : ℝ := G.shapleyValue i

/-- For simple games, the Shapley–Shubik index sums to `1` — the unit of
power is split among the players. -/
theorem shapleyShubikIndex_sum_eq_one (G : CoalGame ι) (h : G.IsSimpleGame) :
    ∑ i, G.shapleyShubikIndex h i = 1 := by
  simp only [shapleyShubikIndex]
  rw [shapleyValue_efficient, h.grandWinning]

/-- A null player has Shapley–Shubik index `0` (no power). -/
theorem shapleyShubikIndex_null (G : CoalGame ι) (h : G.IsSimpleGame) {i : ι}
    (hnull : G.IsNull i) : G.shapleyShubikIndex h i = 0 :=
  shapleyValue_null G hnull

/-- **Banzhaf index of the singleton unanimity game**: player `i` has
Banzhaf index `1` in `unanimityGame {i}` — they are pivotal in every
coalition since the game wins iff they join. -/
theorem unanimityGame_singleton_banzhafIndex [Nonempty ι] (i : ι) :
    (unanimityGame ({i} : Finset ι) (Finset.singleton_nonempty i)).banzhafIndex i
      = 1 := by
  classical
  simp only [banzhafIndex, marginalContribution, unanimityGame]
  -- For each S with i ∉ S: the marginal contribution is 1.
  have hMC : ∀ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
      (if ({i} : Finset ι) ⊆ insert i S then (1 : ℝ) else 0)
        - (if ({i} : Finset ι) ⊆ S then 1 else 0) = 1 := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have h1 : ({i} : Finset ι) ⊆ insert i S := by
      simp [Finset.singleton_subset_iff]
    have h2 : ¬ ({i} : Finset ι) ⊆ S := by
      simp [Finset.singleton_subset_iff, hS]
    simp [h1, h2]
  rw [Finset.sum_congr rfl hMC, Finset.sum_const, nsmul_eq_mul,
    card_filter_notMem, mul_one]
  -- 2^(n-1) / 2^(n-1) = 1.
  have hpos : (2 : ℝ) ^ (Fintype.card ι - 1) ≠ 0 := by
    positivity
  push_cast
  rw [div_self hpos]


end CoalGame

end GameTheory
