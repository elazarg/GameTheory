/-
# Pigou and Braess congestion examples

The canonical routing examples are expressed through `CongestionGame` and its
existing deterministic game form.  Their Nash statements therefore use the
library-wide `IsNash` predicate and `Profile.update`, rather than a separate
routing-game semantics.
-/

import GameTheory.Congestion.AffinePoA
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace CongestionGame

open Classical in
/-- With two players, a resource's load is the sum of their occupancy
indicators. -/
theorem congestion_two (C : CongestionGame (Fin 2)) (σ : C.Profile)
    (r : C.Resource) :
    C.congestion σ r = (if r ∈ C.resources 0 (σ 0) then 1 else 0)
      + (if r ∈ C.resources 1 (σ 1) then 1 else 0) := by
  rw [congestion, Finset.card_filter, Fin.sum_univ_two]

end CongestionGame

namespace Congestion

open CongestionGame

/-! ## Pigou's parallel-edge instance -/

/-- Pigou's two-edge routing instance: one load-proportional edge and one
constant-cost edge. -/
noncomputable abbrev pigou : CongestionGame (Fin 2) where
  Resource := Fin 2
  Strategy := fun _ => Fin 2
  resources := fun _ s => {s}
  delay := fun r k => if r = 0 then (k : ℝ) else 2

/-- Pigou's delays are nonnegative affine functions. -/
theorem pigou_isAffine :
    pigou.IsAffine (fun r => if r = 0 then 1 else 0)
      (fun r => if r = 0 then 0 else 2) where
  delay_eq r n := by
    by_cases h : r = 0 <;> simp [pigou, h]
  a_nonneg r := by by_cases h : r = 0 <;> simp [h]
  b_nonneg r := by by_cases h : r = 0 <;> simp [h]

/-- Both players choosing the variable-cost edge is a Nash equilibrium. -/
theorem pigou_both_isNash :
    IsNash pigou.toGameForm (euPreference pigou.utility) ![0, 0] := by
  have update_zero (s' : Fin 2) :
      Profile.update (sig := pigou.toGameForm.sig) ![0, 0] 0 s' = ![s', 0] := by
    funext j
    fin_cases j <;> simp
  have update_one (s' : Fin 2) :
      Profile.update (sig := pigou.toGameForm.sig) ![0, 0] 1 s' = ![0, s'] := by
    funext j
    fin_cases j <;> simp
  rw [isNash_iff]
  intro who s'
  simp only [euPreference_apply, toGameForm, expectedUtility_pure, utility,
    neg_le_neg_iff]
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · dsimp [pigou, CongestionGame.signature] at s'
    rw [update_zero s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, pigou]
    all_goals norm_num
  · dsimp [pigou, CongestionGame.signature] at s'
    rw [update_one s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, pigou]
    all_goals norm_num

/-- The all-variable-edge equilibrium has social cost four. -/
theorem pigou_socialCost_both : pigou.socialCost ![0, 0] = 4 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou]
  norm_num

/-- Splitting the players across the two edges has social cost three. -/
theorem pigou_socialCost_split : pigou.socialCost ![0, 1] = 3 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou]
  norm_num

/-- The split profile is socially optimal in Pigou's two-player instance. -/
theorem pigou_split_optimal (τ : pigou.Profile) :
    pigou.socialCost ![0, 1] ≤ pigou.socialCost τ := by
  rw [pigou_socialCost_split]
  obtain ⟨t0, h0⟩ : ∃ x, τ 0 = x := ⟨_, rfl⟩
  obtain ⟨t1, h1⟩ : ∃ x, τ 1 = x := ⟨_, rfl⟩
  fin_cases t0 <;> fin_cases t1 <;>
    simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two, pigou,
      h0, h1] <;> norm_num

/-- Pigou witnesses the price-of-anarchy lower bound `4 / 3`. -/
theorem pigou_poa_witness :
    pigou.socialCost ![0, 0] = 4 / 3 * pigou.socialCost ![0, 1] := by
  rw [pigou_socialCost_both, pigou_socialCost_split]
  norm_num

/-- The concrete Pigou equilibrium is covered by the generic affine `5/2`
bound.  This is the reader-facing integration witness for the smoothness API. -/
theorem pigou_socialCost_nash_le (target : pigou.Profile) :
    pigou.socialCost ![0, 0] ≤ 5 / 2 * pigou.socialCost target :=
  pigou.socialCost_nash_le pigou_isAffine pigou_both_isNash target

/-! ## Braess's paradox -/

/-- Delays of the Braess network. -/
noncomputable abbrev braessDelay (r : Fin 5) (k : ℕ) : ℝ :=
  if r = 0 ∨ r = 3 then (k : ℝ) else if r = 4 then 0 else 5 / 2

/-- The restricted Braess network has two disjoint routes. -/
noncomputable abbrev braessRestricted : CongestionGame (Fin 2) where
  Resource := Fin 5
  Strategy := fun _ => Fin 2
  resources := fun _ s => if s = 0 then {0, 1} else {2, 3}
  delay := braessDelay

/-- The augmented Braess network adds the zero-cost shortcut route. -/
noncomputable abbrev braessAugmented : CongestionGame (Fin 2) where
  Resource := Fin 5
  Strategy := fun _ => Fin 3
  resources := fun _ s =>
    if s = 0 then {0, 1} else if s = 1 then {2, 3} else {0, 4, 3}
  delay := braessDelay

/-- The split profile is Nash in the restricted Braess network. -/
theorem braessRestricted_split_isNash :
    IsNash braessRestricted.toGameForm (euPreference braessRestricted.utility) ![0, 1] := by
  have update_zero (s' : Fin 2) :
      Profile.update (sig := braessRestricted.toGameForm.sig) ![0, 1] 0 s' = ![s', 1] := by
    funext j
    fin_cases j <;> simp
  have update_one (s' : Fin 2) :
      Profile.update (sig := braessRestricted.toGameForm.sig) ![0, 1] 1 s' = ![0, s'] := by
    funext j
    fin_cases j <;> simp
  rw [isNash_iff]
  intro who s'
  simp only [euPreference_apply, toGameForm, expectedUtility_pure, utility,
    neg_le_neg_iff]
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · dsimp [braessRestricted, CongestionGame.signature] at s'
    rw [update_zero s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, braessRestricted, braessDelay,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
      Finset.mem_singleton]
    all_goals norm_num
  · dsimp [braessRestricted, CongestionGame.signature] at s'
    rw [update_one s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, braessRestricted, braessDelay,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
        Finset.mem_singleton]
    all_goals norm_num

/-- The restricted split profile has social cost seven. -/
theorem braessRestricted_socialCost_split :
    braessRestricted.socialCost ![0, 1] = 7 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two,
    braessRestricted, braessDelay]
  norm_num

/-- Both players selecting the shortcut route is Nash in the augmented
Braess network. -/
theorem braessAugmented_both_isNash :
    IsNash braessAugmented.toGameForm (euPreference braessAugmented.utility) ![2, 2] := by
  have update_zero (s' : Fin 3) :
      Profile.update (sig := braessAugmented.toGameForm.sig) ![2, 2] 0 s' = ![s', 2] := by
    funext j
    fin_cases j <;> simp
  have update_one (s' : Fin 3) :
      Profile.update (sig := braessAugmented.toGameForm.sig) ![2, 2] 1 s' = ![2, s'] := by
    funext j
    fin_cases j <;> simp
  rw [isNash_iff]
  intro who s'
  simp only [euPreference_apply, toGameForm, expectedUtility_pure, utility,
    neg_le_neg_iff]
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · dsimp [braessAugmented, CongestionGame.signature] at s'
    rw [update_zero s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, braessAugmented, braessDelay,
      Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
      Finset.mem_singleton]
    all_goals norm_num
  · dsimp [braessAugmented, CongestionGame.signature] at s'
    rw [update_one s']
    fin_cases s'
    all_goals simp [playerCost, congestion_two, braessAugmented, braessDelay,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
        Finset.mem_singleton]
    all_goals norm_num

/-- The shortcut equilibrium has social cost eight. -/
theorem braessAugmented_socialCost_both :
    braessAugmented.socialCost ![2, 2] = 8 := by
  simp [socialCost, Fin.sum_univ_two, playerCost, congestion_two,
    braessAugmented, braessDelay]
  norm_num

/-- Once the shortcut is present, the former split profile is not Nash. -/
theorem braessAugmented_split_not_isNash :
    ¬ IsNash braessAugmented.toGameForm (euPreference braessAugmented.utility) ![0, 1] := by
  have update_zero :
      Profile.update (sig := braessAugmented.toGameForm.sig) ![0, 1] 0 (2 : Fin 3) = ![2, 1] := by
    funext j
    fin_cases j <;> simp
  intro hσ
  have h := (isNash_iff (F := braessAugmented.toGameForm) ![0, 1]).mp hσ 0 (2 : Fin 3)
  simp only [euPreference_apply, toGameForm, expectedUtility_pure, utility,
    neg_le_neg_iff] at h
  rw [update_zero] at h
  simp [playerCost, congestion_two, braessAugmented, braessDelay,
    Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton] at h
  norm_num at h

/-- Braess's paradox: the shortcut equilibrium costs more than the displaced
restricted-network equilibrium. -/
theorem braess_socialCost_increases :
    braessRestricted.socialCost ![0, 1] < braessAugmented.socialCost ![2, 2] := by
  rw [braessRestricted_socialCost_split, braessAugmented_socialCost_both]
  norm_num

end Congestion

end GameTheory
