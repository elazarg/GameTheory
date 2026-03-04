import GameTheory.Core.KernelGame
import Mathlib.Algebra.BigOperators.Ring.Finset
import Math.Probability

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

open Math.Probability

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

/-- Two players are symmetric if swapping them in any coalition
    preserves the value. -/
def AreSymmetric (G : CoalGame ι) (i j : ι) : Prop :=
  ∀ S : Finset ι, i ∉ S → j ∉ S → G.v (insert i S) = G.v (insert j S)

/-- Symmetric players have the same marginal contribution to coalitions
    containing neither of them. -/
theorem marginalContribution_eq_of_symmetric (G : CoalGame ι) {i j : ι}
    (hsym : G.AreSymmetric i j) {S : Finset ι}
    (hi : i ∉ S) (hj : j ∉ S) :
    G.marginalContribution i S = G.marginalContribution j S := by
  simp only [marginalContribution]
  rw [hsym S hi hj]

/-- Scalar multiplication of coalitional games. -/
def gameScalar (c : ℝ) (G : CoalGame ι) : CoalGame ι where
  v := fun S => c * G.v S
  v_empty := by simp [G.v_empty]

/-- Shapley value is linear: scales with scalar multiplication. -/
theorem shapleyValue_scalar (c : ℝ) (G : CoalGame ι) (i : ι) :
    (gameScalar c G).shapleyValue i = c * G.shapleyValue i := by
  simp only [shapleyValue, gameScalar, marginalContribution]
  rw [Finset.mul_sum]
  congr 1; ext S; ring

open Classical in
/-- Symmetric players have the same Shapley value. -/
theorem shapleyValue_symmetric (G : CoalGame ι) {i j : ι} (hne : i ≠ j)
    (hsym : G.AreSymmetric i j) :
    G.shapleyValue i = G.shapleyValue j := by
  simp only [shapleyValue]
  set Si := (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S)
  set Sj := (Finset.univ : Finset (Finset ι)).filter (fun S => j ∉ S)
  -- Bijection that swaps j→i (or i→j) in a coalition
  let swap (a b : ι) (S : Finset ι) : Finset ι :=
    if b ∈ S then insert a (S.erase b) else S
  -- Helper facts about swap
  have swap_mem (a b : ι) (hab : a ≠ b) (S : Finset ι) (ha : a ∉ S) :
      b ∉ swap a b S := by
    simp only [swap]
    split_ifs with hb
    · intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hbe
      · exact hab rfl
      · exact (Finset.notMem_erase b S) hbe
    · exact hb
  have swap_inv (a b : ι) (hab : a ≠ b) (S : Finset ι) (ha : a ∉ S) :
      swap b a (swap a b S) = S := by
    change (if a ∈ (if b ∈ S then insert a (S.erase b) else S)
      then insert b ((if b ∈ S then insert a (S.erase b) else S).erase a)
      else (if b ∈ S then insert a (S.erase b) else S)) = S
    by_cases hb : b ∈ S
    · -- b ∈ S: swap a b S = insert a (S.erase b)
      simp only [hb, ↓reduceIte, Finset.mem_insert_self]
      have ha_ne : a ∉ S.erase b := by
        intro hmem; exact ha (Finset.mem_of_mem_erase hmem)
      rw [Finset.erase_insert ha_ne, Finset.insert_erase hb]
    · -- b ∉ S: swap a b S = S
      simp only [hb, ↓reduceIte, show a ∉ S from ha]
  have swap_card (a b : ι) (S : Finset ι) (ha : a ∉ S) (hb : b ∈ S) :
      (swap a b S).card = S.card := by
    simp only [swap, hb, ↓reduceIte]
    have : a ∉ S.erase b := by
      simp only [Finset.mem_erase]; exact fun ⟨_, h⟩ => ha h
    rw [Finset.card_insert_of_notMem this, Finset.card_erase_of_mem hb]
    have : 0 < S.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  apply Finset.sum_nbij' (swap i j) (swap j i)
  -- swap i j maps Si into Sj
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and]
    exact swap_mem i j hne S hS
  -- swap j i maps Sj into Si
  · intro T hT
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
    exact swap_mem j i hne.symm T hT
  -- swap j i ∘ swap i j = id on Si
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact swap_inv i j hne S hS
  -- swap i j ∘ swap j i = id on Sj
  · intro T hT
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact swap_inv j i hne.symm T hT
  -- Values match
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [swap]
    split_ifs with hj
    · -- j ∈ S: cardinality preserved, marginal contribution preserved
      have hcard := swap_card i j S hS hj
      simp only [swap, hj, ↓reduceIte] at hcard
      set U := S.erase j with hU_def
      have hiU : i ∉ U := by
        simp only [Finset.mem_erase, hU_def]; exact fun ⟨_, h⟩ => hS h
      have hjU : j ∉ U := Finset.notMem_erase j S
      -- v(insert i U) = v(insert j U) by symmetry
      have hv_sym : G.v (insert i U) = G.v (insert j U) := hsym U hiU hjU
      -- insert j U = S
      have hv_S : insert j U = S := Finset.insert_erase hj
      -- insert j (insert i U) = insert i S
      have hv_jT : insert j (insert i U) = insert i S := by
        rw [Finset.insert_comm, hv_S]
      simp only [marginalContribution, hcard, hv_jT, ← hv_S, hv_sym]
    · -- j ∉ S: both absent
      congr 1
      exact G.marginalContribution_eq_of_symmetric hsym hS hj

end CoalGame

end GameTheory
