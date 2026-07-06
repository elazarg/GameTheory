/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Congestion.AffinePoA
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Routing examples: Pigou and Braess

The two canonical selfish-routing instances, expressed through the congestion
infrastructure with two atomic players.

**Pigou**: two parallel edges, one with load-proportional delay and one with
constant delay `2`. Sending both players on the variable edge is a Nash
equilibrium of social cost `4`, while the socially optimal profile splits at
cost `3` (`pigou_split_optimal`) — a price-of-anarchy witness of `4/3`,
inside the affine `5/2` guarantee.

**Braess**: the classical 4-edge diamond (plus zero-cost shortcut). In the
restricted network the split profile is a Nash equilibrium of social cost `7`.
Adding the free shortcut creates a Nash equilibrium in which both players use
it at social cost `8`, while the split profile stops being an equilibrium:
the shortcut equilibrium exhibited costs strictly more than the equilibrium
it displaces.

## Main results

* `pigou_both_isNash`, `pigou_split_optimal`, `pigou_poa_witness` — the `4/3`
  lower-bound instance
* `braessRestricted_split_isNash`, `braessAugmented_both_isNash`,
  `braessAugmented_split_not_isNash`, `braess_socialCost_increases` —
  Braess's paradox on the 4-edge network
-/

open scoped BigOperators

namespace GameTheory

namespace CongestionGame

open Classical in
/-- Two-player congestion counting: the load of a resource is the sum of the
two players' indicators. -/
theorem congestion_two (C : CongestionGame (Fin 2)) (σ : C.Profile)
    (r : C.Resource) :
    C.congestion σ r = (if r ∈ C.resources 0 (σ 0) then 1 else 0)
      + (if r ∈ C.resources 1 (σ 1) then 1 else 0) := by
  rw [congestion, Finset.card_filter, Fin.sum_univ_two]

end CongestionGame

namespace Congestion

open CongestionGame

/-! ### Pigou's example -/

/-- Pigou's network: edge `0` has delay equal to its load, edge `1` constant
delay `2`. Each of the two players picks one edge. -/
noncomputable abbrev pigou : CongestionGame (Fin 2) where
  Resource := Fin 2
  StrategySet := fun _ => Fin 2
  resources := fun _ s => {s}
  delay := fun r k => if r = 0 then (k : ℝ) else 2

theorem pigou_isAffine :
    pigou.IsAffine (fun r => if r = 0 then 1 else 0)
      (fun r => if r = 0 then 0 else 2) where
  delay_eq r n := by
    by_cases h : r = 0 <;> simp [pigou, h]
  a_nonneg r := by by_cases h : r = 0 <;> simp [h]
  b_nonneg r := by by_cases h : r = 0 <;> simp [h]

/-- Both players on the variable edge form a Nash equilibrium. -/
theorem pigou_both_isNash : pigou.toKernelGame.IsNash ![0, 0] := by
  have key : ∀ who s' : Fin 2,
      pigou.toKernelGame.eu ![0, 0] who
        ≥ pigou.toKernelGame.eu (Function.update ![0, 0] who s') who := by
    intro who s'
    simp only [eu_toKernelGame, ge_iff_le, neg_le_neg_iff]
    fin_cases who <;> fin_cases s' <;>
      simp [playerCost, congestion_two, pigou] <;>
        norm_num
  exact key

/-- The all-variable Nash equilibrium costs `4`... -/
theorem pigou_socialCost_both : pigou.socialCost ![0, 0] = 4 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou]
  norm_num

/-- ...while the split profile costs `3`. -/
theorem pigou_socialCost_split : pigou.socialCost ![0, 1] = 3 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou]
  norm_num

/-- The split profile is socially optimal. -/
theorem pigou_split_optimal (τ : pigou.Profile) :
    pigou.socialCost ![0, 1] ≤ pigou.socialCost τ := by
  rw [pigou_socialCost_split]
  obtain ⟨t0, h0⟩ : ∃ x, τ 0 = x := ⟨_, rfl⟩
  obtain ⟨t1, h1⟩ : ∃ x, τ 1 = x := ⟨_, rfl⟩
  fin_cases t0 <;> fin_cases t1 <;>
    simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou,
      h0, h1] <;> norm_num

/-- Pigou witnesses a price of anarchy of `4/3`: the all-variable equilibrium
costs `4/3` times the optimum. -/
theorem pigou_poa_witness :
    pigou.socialCost ![0, 0] = 4 / 3 * pigou.socialCost ![0, 1] := by
  rw [pigou_socialCost_both, pigou_socialCost_split]
  norm_num

/-- The Pigou equilibrium respects the affine `5/2` guarantee. -/
example (τ : pigou.Profile) :
    pigou.socialCost ![0, 0] ≤ 5 / 2 * pigou.socialCost τ :=
  pigou.socialCost_nash_le pigou_isAffine pigou_both_isNash τ

/-! ### Braess's paradox

Vertices `s, v, w, t`; edges `0 = s→v` (delay = load), `1 = v→t` (delay `5/2`),
`2 = s→w` (delay `5/2`), `3 = w→t` (delay = load), `4 = v→w` (delay `0`, the
shortcut). Routes: `P₀ = {0,1}`, `P₁ = {2,3}`, and in the augmented network
also `P₂ = {0,4,3}`. -/

/-- Delays of the Braess network. -/
noncomputable abbrev braessDelay (r : Fin 5) (k : ℕ) : ℝ :=
  if r = 0 ∨ r = 3 then (k : ℝ) else if r = 4 then 0 else 5 / 2

/-- The restricted Braess network: the two disjoint routes only. -/
noncomputable abbrev braessRestricted : CongestionGame (Fin 2) where
  Resource := Fin 5
  StrategySet := fun _ => Fin 2
  resources := fun _ s => if s = 0 then {0, 1} else {2, 3}
  delay := braessDelay

/-- The augmented Braess network: route `2` uses the zero-cost shortcut. -/
noncomputable abbrev braessAugmented : CongestionGame (Fin 2) where
  Resource := Fin 5
  StrategySet := fun _ => Fin 3
  resources := fun _ s => if s = 0 then {0, 1} else if s = 1 then {2, 3} else {0, 4, 3}
  delay := braessDelay

/-- In the restricted network the split profile is a Nash equilibrium. -/
theorem braessRestricted_split_isNash :
    braessRestricted.toKernelGame.IsNash ![0, 1] := by
  have key : ∀ who s' : Fin 2,
      braessRestricted.toKernelGame.eu ![0, 1] who
        ≥ braessRestricted.toKernelGame.eu (Function.update ![0, 1] who s') who := by
    intro who s'
    simp only [eu_toKernelGame, ge_iff_le, neg_le_neg_iff]
    fin_cases who <;> fin_cases s' <;>
      simp [playerCost, congestion_two, braessRestricted, braessDelay,
        Finset.sum_insert, Finset.sum_singleton,
        Finset.mem_insert, Finset.mem_singleton] <;> norm_num
  exact key

/-- Its social cost is `7`. -/
theorem braessRestricted_socialCost_split :
    braessRestricted.socialCost ![0, 1] = 7 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two,
    braessRestricted, braessDelay]
  norm_num

/-- In the augmented network both players taking the shortcut route is a Nash
equilibrium. -/
theorem braessAugmented_both_isNash :
    braessAugmented.toKernelGame.IsNash ![2, 2] := by
  have key : ∀ who : Fin 2, ∀ s' : Fin 3,
      braessAugmented.toKernelGame.eu ![2, 2] who
        ≥ braessAugmented.toKernelGame.eu (Function.update ![2, 2] who s') who := by
    intro who s'
    simp only [eu_toKernelGame, ge_iff_le, neg_le_neg_iff]
    fin_cases who <;> fin_cases s' <;>
      simp [playerCost, congestion_two, braessAugmented, braessDelay,
        Finset.sum_insert, Finset.sum_singleton,
        Finset.mem_insert, Finset.mem_singleton] <;> norm_num
  exact key

/-- Its social cost is `8`. -/
theorem braessAugmented_socialCost_both :
    braessAugmented.socialCost ![2, 2] = 8 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two,
    braessAugmented, braessDelay]
  norm_num

/-- The split profile is no longer an equilibrium once the shortcut exists:
deviating to the shortcut route strictly improves. -/
theorem braessAugmented_split_not_isNash :
    ¬ braessAugmented.toKernelGame.IsNash ![0, 1] := by
  intro hσ
  have h := hσ 0 (show braessAugmented.toKernelGame.Strategy 0 from (2 : Fin 3))
  simp only [eu_toKernelGame, ge_iff_le, neg_le_neg_iff] at h
  simp [playerCost, congestion_two, braessAugmented, braessDelay,
    Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_insert, Finset.mem_singleton] at h
  norm_num at h

/-- **Braess's paradox**: the shortcut equilibrium of the augmented network
costs strictly more than the split equilibrium of the restricted network —
which the shortcut destroys (`braessAugmented_split_not_isNash`). -/
theorem braess_socialCost_increases :
    braessRestricted.socialCost ![0, 1] < braessAugmented.socialCost ![2, 2] := by
  rw [braessRestricted_socialCost_split, braessAugmented_socialCost_both]
  norm_num

end Congestion

end GameTheory
