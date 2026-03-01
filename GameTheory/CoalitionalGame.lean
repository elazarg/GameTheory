import GameTheory.KernelGame
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Coalitional Games and the Shapley Value

A coalitional (transferable utility) game assigns a value to each
coalition of players. The Shapley value (1953) is the unique allocation
satisfying efficiency, symmetry, dummy, and additivity axioms.

## Main definitions

* `CoalGame` — TU coalitional game
* `CoalGame.shapleyValue` — the Shapley value
* `CoalGame.marginalContribution` — player's marginal contribution to a coalition
* `CoalGame.IsCore` — the core of a coalitional game

## Main results

* `shapleyValue_null` — null players get Shapley value 0
* `shapleyValue_additive` — Shapley value is additive across games
-/

open scoped BigOperators

namespace GameTheory

/-- A transferable-utility coalitional game: `v S` is the value of coalition `S`. -/
structure CoalGame (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Characteristic function: value of each coalition. -/
  v : Finset ι → ℝ
  /-- Empty coalition has zero value. -/
  v_empty : v ∅ = 0

namespace CoalGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Marginal contribution of player `i` to coalition `S`. -/
def marginalContribution (G : CoalGame ι) (i : ι) (S : Finset ι) : ℝ :=
  G.v (insert i S) - G.v S

/-- Player `i` is a null player if their marginal contribution to
    every coalition is zero. -/
def IsNull (G : CoalGame ι) (i : ι) : Prop :=
  ∀ S : Finset ι, i ∉ S → G.marginalContribution i S = 0

/-- The Shapley value: player `i`'s share, computed as the expected
    marginal contribution over all orderings.

    φᵢ = Σ_{S ⊆ N\{i}} |S|!(n-|S|-1)!/n! · [v(S∪{i}) - v(S)] -/
noncomputable def shapleyValue (G : CoalGame ι) (i : ι) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
    ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
      ((Fintype.card ι).factorial : ℝ) * G.marginalContribution i S

/-- An allocation is in the core if it is efficient and no coalition blocks. -/
def IsCore (G : CoalGame ι) (x : ι → ℝ) : Prop :=
  (∑ i, x i = G.v Finset.univ) ∧
  ∀ S : Finset ι, ∑ i ∈ S, x i ≥ G.v S

/-- A null player gets Shapley value 0. -/
theorem shapleyValue_null (G : CoalGame ι) {i : ι} (h : G.IsNull i) :
    G.shapleyValue i = 0 := by
  simp only [shapleyValue]
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [h S hS, mul_zero]

/-- Sum of two coalitional games. -/
def gameAdd (G₁ G₂ : CoalGame ι) : CoalGame ι where
  v := fun S => G₁.v S + G₂.v S
  v_empty := by simp [G₁.v_empty, G₂.v_empty]

/-- Shapley value is additive across games. -/
theorem shapleyValue_additive (G₁ G₂ : CoalGame ι) (i : ι) :
    (gameAdd G₁ G₂).shapleyValue i = G₁.shapleyValue i + G₂.shapleyValue i := by
  simp only [shapleyValue, gameAdd, marginalContribution]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext S
  ring

end CoalGame

end GameTheory
