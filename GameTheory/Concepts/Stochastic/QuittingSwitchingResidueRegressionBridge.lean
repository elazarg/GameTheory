/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSwitchingResidueRegression
import GameTheory.Concepts.Stochastic.QuittingSureExitSet

/-!
# The switching-residue regression table has no sure exit set

`QuittingSwitchingResidueRegression` proves, by pure arithmetic on a
concrete three-player reward table, that every one of the seven nonempty
coalitions of `Fin 3` fails the sure-exit inequality system `SureExitFails`.
That module deliberately uses no stochastic-game dynamics, roots, or
profiles.

This tiny bridge file connects that arithmetic fact to the game layer's
`IsQuittingSureExitSet` (`QuittingSureExitSet.lean`): it packages the same
table as a genuine quitting-game reward `gameReward` on
`{S : Finset Player // S.Nonempty}`, checks that its extended set reward
`quittingSetReward gameReward` agrees with the arithmetic `reward` table at
every coalition including the empty one, and concludes that `gameReward` has
no sure exit set at all — for every nonempty `S`,
`¬ IsQuittingSureExitSet gameReward S`.

Every result here is original to this development; none of it is quoted or
adapted from a specific published source.
-/

noncomputable section

namespace GameTheory

namespace QuittingSwitchingResidueRegressionBridge

open QuittingSureSetOwnerRepair QuittingSwitchingResidueRegression

/-- **The game-layer reward table.** The arithmetic table
`QuittingSwitchingResidueRegression.reward`, restricted to nonempty
coalitions, read as a genuine quitting-game reward. -/
def gameReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S ↦ QuittingSwitchingResidueRegression.reward S.1

/-- The extended set reward of `gameReward` agrees with the arithmetic
`reward` table at every coalition, including the empty one. -/
theorem quittingSetReward_gameReward (S : Finset Player) :
    quittingSetReward gameReward S = QuittingSwitchingResidueRegression.reward S := by
  funext who
  by_cases hS : S.Nonempty
  · simp [quittingSetReward_of_nonempty gameReward hS, gameReward]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, quittingSetReward_empty,
      QuittingSwitchingResidueRegression.reward]

/-- A failure of the arithmetic sure-exit system at `S` defeats the
game-layer sure-exit-set predicate at the same `S`. -/
theorem not_isQuittingSureExitSet_of_sureExitFails
    {S : Finset Player} (h : SureExitFails S) :
    ¬ IsQuittingSureExitSet gameReward S := by
  rintro ⟨hmember, houtsider⟩
  rcases h with ⟨i, hi, hlt⟩ | ⟨j, hj, hlt⟩
  · exact absurd (hmember i hi) (by
      rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
      exact not_le.mpr hlt)
  · exact absurd (houtsider j hj) (by
      rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
      exact not_le.mpr hlt)

private theorem nonempty_fin3_cases (S : Finset Player) (hS : S.Nonempty) :
    S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
  by_cases h0 : 0 ∈ S
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; right
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · obtain ⟨who, hwho⟩ := hS
        fin_cases who <;> simp_all

/-- **No sure exit set.** Every nonempty coalition fails the game-layer
sure-exit-set test against `gameReward`: this is exactly the arithmetic
failure `SureExitFails`, established over the seven nonempty coalitions of
`QuittingSwitchingResidueRegression`, transported through
`quittingSetReward_gameReward`. -/
theorem not_isQuittingSureExitSet_gameReward
    (S : Finset Player) (hS : S.Nonempty) :
    ¬ IsQuittingSureExitSet gameReward S := by
  rcases nonempty_fin3_cases S hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_1
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_2
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_3
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_12
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_13
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_23
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_123

end QuittingSwitchingResidueRegressionBridge

end GameTheory
