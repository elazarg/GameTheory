/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability
import GameTheory.Cooperative.CoalitionalGame.Convex

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace CoalGame

variable {ι : Type} [DecidableEq ι]

/-! ### Additive games

An *additive* coalitional game has `v(S) = ∑_{i ∈ S} α i` for some
per-player vector `α`. These are degenerate from a cooperative-game
standpoint (no synergy from cooperation), but they form a natural class
on which the Shapley value, Banzhaf index, and core all collapse to the
identity allocation. -/

/-- The additive game with weights `α`: `v(S) = ∑_{i ∈ S} α i`. -/
def additiveGame (α : ι → ℝ) : CoalGame ι where
  v := fun S => ∑ i ∈ S, α i
  v_empty := Finset.sum_empty

@[simp]
theorem additiveGame_v (α : ι → ℝ) (S : Finset ι) :
    (additiveGame α).v S = ∑ i ∈ S, α i := rfl

section Core

noncomputable local instance finiteFintype {α : Type} [Finite α] : Fintype α :=
  Fintype.ofFinite α

/-- In an additive game, the weight vector `α` itself is in the core
(with equality on every coalition). -/
theorem additiveGame_isCore [Finite ι] (α : ι → ℝ) : (additiveGame α).IsCore α := by
  exact ⟨rfl, fun _ => le_refl _⟩

/-- The core of an additive game is exactly `{α}`: every core allocation equals
the weight vector. Coalition-rationality on `{i}` gives `x i ≥ α i`; on `{i}ᶜ`
together with efficiency it gives `x i ≤ α i`. (Existence is `additiveGame_isCore`.) -/
theorem additiveGame_core_eq [Finite ι] (α x : ι → ℝ)
    (hx : (additiveGame α).IsCore x) : x = α := by
  classical
  funext i
  have heff : ∑ j, x j = ∑ j, α j := by
    simpa [additiveGame_v] using IsCore.efficient _ hx
  have hcompl : ∑ j ∈ ({i}ᶜ : Finset ι), α j ≤ ∑ j ∈ ({i}ᶜ : Finset ι), x j := by
    simpa [additiveGame_v] using IsCore.coalition_rational _ hx ({i}ᶜ)
  have hsing : α i ≤ x i := by
    simpa [additiveGame_v, Finset.sum_singleton] using IsCore.individually_rational _ hx i
  have hsplit_x : x i + ∑ j ∈ ({i}ᶜ : Finset ι), x j = ∑ j, x j := by
    rw [← Finset.sum_add_sum_compl {i} x, Finset.sum_singleton]
  have hsplit_α : α i + ∑ j ∈ ({i}ᶜ : Finset ι), α j = ∑ j, α j := by
    rw [← Finset.sum_add_sum_compl {i} α, Finset.sum_singleton]
  linarith

end Core

/-- A player's marginal contribution in an additive game is exactly
their own weight `α i`, independent of the coalition. -/
theorem additiveGame_marginalContribution (α : ι → ℝ) (i : ι)
    {S : Finset ι} (hi : i ∉ S) :
    (additiveGame α).marginalContribution i S = α i := by
  simp only [marginalContribution, additiveGame_v,
    Finset.sum_insert hi]
  ring

variable [Fintype ι]

/-- An additive game decomposes as a sum of scaled singleton-unanimity games. -/
theorem additiveGame_eq_gameSum (α : ι → ℝ) :
    additiveGame α = gameSum (Finset.univ : Finset ι)
      (fun j => gameScalar (α j)
        (unanimityGame {j} (Finset.singleton_nonempty j))) := by
  ext S
  simp only [gameSum_v, gameScalar, unanimityGame, additiveGame_v]
  -- Convert `α j * if p j then 1 else 0` to `if p j then α j else 0`.
  have hmul : ∀ j : ι, α j * (if ({j} : Finset ι) ⊆ S then (1 : ℝ) else 0) =
      if ({j} : Finset ι) ⊆ S then α j else 0 := by
    intro j
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => hmul j)]
  rw [← Finset.sum_filter]
  -- The filter `{j} ⊆ S` is `j ∈ S`, and `univ.filter (· ∈ S) = S`.
  have hfilter : Finset.univ.filter (fun j : ι => ({j} : Finset ι) ⊆ S) = S := by
    ext j
    simp [Finset.singleton_subset_iff]
  rw [hfilter]

/-- **Banzhaf index of an additive game**: each player receives exactly
their own weight, like the Shapley value. Same decomposition trick:
`additiveGame α = Σ_j (α j) · u_{j}`, and Banzhaf is linear with
`banzhafIndex (unanimityGame {j}) i = 1[i = j]`. -/
theorem additiveGame_banzhafIndex (α : ι → ℝ) (i : ι) :
    (additiveGame α).banzhafIndex i = α i := by
  classical
  rw [additiveGame_eq_gameSum,
    gameSum_allocation_eq banzhafIndex
      (fun G₁ G₂ k => banzhafIndex_additive G₁ G₂ k)]
  -- shapleyValue (gameScalar (α j) (unanimityGame {j})) i = α j * (1[i = j])
  have hterm : ∀ j : ι,
      banzhafIndex (gameScalar (α j)
        (unanimityGame ({j} : Finset ι) (Finset.singleton_nonempty j))) i =
      if i = j then α j else 0 := by
    intro j
    rw [banzhafIndex_scalar]
    by_cases hij : i = j
    · subst hij
      rw [unanimityGame_singleton_banzhafIndex, mul_one]
      simp
    · have hnull : (unanimityGame ({j} : Finset ι) (Finset.singleton_nonempty j)).IsNull i := by
        apply unanimityGame_isNull_of_notMem
        simp [Finset.mem_singleton, hij]
      rw [banzhafIndex_null _ hnull, mul_zero]
      simp [hij]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp [Finset.sum_ite_eq]

/-- **Shapley value of an additive game**: each player receives exactly
their own weight. Combines linearity of Shapley with the explicit Shapley
formula on unanimity games. -/
theorem additiveGame_shapleyValue (α : ι → ℝ) (i : ι) :
    (additiveGame α).shapleyValue i = α i := by
  classical
  rw [additiveGame_eq_gameSum, gameSum_allocation_eq shapleyValue
    (fun G₁ G₂ k => shapleyValue_additive G₁ G₂ k)]
  -- Each j-th term: shapleyValue (gameScalar (α j) (unanimityGame {j})) i
  --              = α j * (if i ∈ {j} then 1/|{j}| else 0)
  --              = α j * (if i = j then 1 else 0)
  have hterm : ∀ j : ι,
      shapleyValue (gameScalar (α j)
        (unanimityGame ({j} : Finset ι) (Finset.singleton_nonempty j))) i =
      if i = j then α j else 0 := by
    intro j
    rw [shapleyValue_scalar, unanimityGame_shapleyValue]
    by_cases hij : i = j
    · subst hij
      simp [Finset.card_singleton]
    · have hni : i ∉ ({j} : Finset ι) := by
        simp [Finset.mem_singleton, hij]
      simp [hni, hij]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp [Finset.sum_ite_eq]

/-- **Sum of Shapley weights**: for every player `i`, the Shapley
combinatorial weights over coalitions not containing `i` sum to `1`.
This is the standard normalization, derived here from
`additiveGame_shapleyValue` applied to the unit vector at `i` (Shapley
of the resulting additive game must equal `1`, and the formula computes
to the desired sum). -/
theorem sum_shapleyWeights (i : ι) :
    ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
      ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
        ((Fintype.card ι).factorial : ℝ) = 1 := by
  classical
  -- Unit vector at i.
  let α : ι → ℝ := fun j => if j = i then 1 else 0
  have hα_eq : (additiveGame α).shapleyValue i = 1 := by
    rw [additiveGame_shapleyValue]
    simp [α]
  -- Expand and replace marginal contribution with constant 1.
  rw [shapleyValue] at hα_eq
  have hMC : ∀ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
      (additiveGame α).marginalContribution i S = 1 := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [additiveGame_marginalContribution _ _ hS]
    simp [α]
  have hα_simp :
      (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
        ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
        ((Fintype.card ι).factorial : ℝ) *
        (additiveGame α).marginalContribution i S) =
      (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
        ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
        ((Fintype.card ι).factorial : ℝ)) := by
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [hMC S hS, mul_one]
  rw [hα_simp] at hα_eq
  exact hα_eq

/-! ### 3-player majority game (worked example) -/

/-- The 3-player simple majority game: a coalition wins iff it has at
least two members. -/
def majorityGame3 : CoalGame (Fin 3) where
  v := fun S => if 2 ≤ S.card then 1 else 0
  v_empty := by simp

theorem majorityGame3_isSimple : majorityGame3.IsSimpleGame where
  boolean := by
    intro S
    simp only [majorityGame3]
    by_cases h : 2 ≤ S.card
    · right; rw [if_pos h]
    · left; rw [if_neg h]
  monotone := by
    intro S T hST hS
    simp only [majorityGame3] at *
    by_cases h2 : 2 ≤ T.card
    · rw [if_pos h2]
    · exfalso
      have hScard : 2 ≤ S.card := by
        by_contra hne
        rw [if_neg hne] at hS
        exact zero_ne_one hS
      have : S.card ≤ T.card := Finset.card_le_card hST
      omega
  grandWinning := by
    simp only [majorityGame3, Finset.card_univ, Fintype.card_fin]
    rfl

/-- All three players are pairwise symmetric in the majority game (the
game depends only on coalition size). -/
theorem majorityGame3_areSymmetric (i j : Fin 3) :
    majorityGame3.AreSymmetric i j := by
  intro S hi hj
  simp only [majorityGame3, Finset.card_insert_of_notMem hi,
    Finset.card_insert_of_notMem hj]

/-- The Shapley value of the 3-player majority game is `1/3` for every
player: by symmetry all three values are equal, and they sum to `v(univ) = 1`. -/
theorem majorityGame3_shapleyValue (i : Fin 3) :
    majorityGame3.shapleyValue i = 1 / 3 := by
  classical
  -- All players have the same Shapley value by symmetry.
  have hsym : ∀ j k : Fin 3, j ≠ k →
      majorityGame3.shapleyValue j = majorityGame3.shapleyValue k :=
    fun j k hne => shapleyValue_symmetric majorityGame3 hne
      (majorityGame3_areSymmetric j k)
  -- The values sum to v(univ) = 1.
  have hsum : ∑ k : Fin 3, majorityGame3.shapleyValue k = 1 := by
    rw [shapleyValue_efficient]
    exact majorityGame3_isSimple.grandWinning
  -- Each value equals 1/3.
  have hconst : ∀ k : Fin 3, majorityGame3.shapleyValue k =
      majorityGame3.shapleyValue i := by
    intro k
    by_cases hki : k = i
    · subst hki; rfl
    · exact hsym k i hki
  rw [Finset.sum_congr rfl (fun k _ => hconst k), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  -- hsum : ↑3 * shapleyValue i = 1; normalize the coercion and divide.
  have hsum' : (3 : ℝ) * majorityGame3.shapleyValue i = 1 := by
    push_cast at hsum; exact hsum
  linarith


end CoalGame

end GameTheory
