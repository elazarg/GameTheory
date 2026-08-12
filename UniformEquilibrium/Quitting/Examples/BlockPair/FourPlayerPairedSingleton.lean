/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# The four-player paired-singleton family

This file fixes the common singleton data of the four-player
paired-singleton family and proves the first concrete completion.  Players
`0,1` form one pair and `2,3` the other.  A player quitting alone pays itself
`0`, its partner `3`, and either member of the opposite pair `-1`.

The stationary completion pays every player `-2` whenever at least two
players quit.  The pure row in which player `0` quits and everyone else
continues is an exact terminal Nash profile against arbitrary behavioral
deviations.  Its terminal payoff is therefore a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open StochasticGame

abbrev Player := Fin 4

/-- The paired singleton-comparison matrix displayed in the definition of
the family.  Rows are payoff recipients and columns are sole quitters. -/
def pairedSingletonMatrix : Player → Player → ℝ := fun who owner =>
  ![![0, 3, -1, -1],
    ![3, 0, -1, -1],
    ![-1, -1, 0, 3],
    ![-1, -1, 3, 0]] who owner

/-- The payoff vector when `owner` is the sole quitter. -/
def pairedSingletonReward (owner : Player) : Payoff Player := fun who =>
  pairedSingletonMatrix who owner

/-- A concrete presentation of the common singleton rows.  The fallback is
only used for non-singleton quitter sets. -/
def stationaryCompletionReward
    (quitters : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  if quitters.1 = {0} then pairedSingletonReward 0
  else if quitters.1 = {1} then pairedSingletonReward 1
  else if quitters.1 = {2} then pairedSingletonReward 2
  else if quitters.1 = {3} then pairedSingletonReward 3
  else fun _ => -2

/-- The stationary completion has exactly the prescribed singleton rows. -/
@[simp] theorem stationaryCompletionReward_singleton (owner : Player) :
    stationaryCompletionReward (quittingSingletonTerminal owner) =
      pairedSingletonReward owner := by
  fin_cases owner <;> rfl

@[simp] theorem stationaryCompletionReward_singleton_set (owner : Player) :
    stationaryCompletionReward ⟨{owner}, by simp⟩ =
      pairedSingletonReward owner := by
  fin_cases owner <;> rfl

/-- Its projective singleton matrix is the displayed paired matrix.  Since
the own-singleton entries vanish, no additional normalization is visible. -/
theorem stationaryCompletion_singletonMatrix (who owner : Player) :
    Math.LinearProgramming.quittingSingletonMatrix
        stationaryCompletionReward who owner =
      pairedSingletonMatrix who owner := by
  rw [Math.LinearProgramming.quittingSingletonMatrix]
  rw [stationaryCompletionReward_singleton_set,
    stationaryCompletionReward_singleton_set]
  fin_cases who <;> fin_cases owner <;>
    simp [pairedSingletonReward, pairedSingletonMatrix]

/-- Every collision row of the stationary completion pays `-2`. -/
theorem stationaryCompletionReward_of_one_lt_card
    (quitters : {S : Finset Player // S.Nonempty})
    (hcard : 1 < quitters.1.card) :
    stationaryCompletionReward quitters = fun _ => -2 := by
  unfold stationaryCompletionReward
  have h0 : quitters.1 ≠ {0} := by
    intro h
    rw [h] at hcard
    simp at hcard
  have h1 : quitters.1 ≠ {1} := by
    intro h
    rw [h] at hcard
    simp at hcard
  have h2 : quitters.1 ≠ {2} := by
    intro h
    rw [h] at hcard
    simp at hcard
  have h3 : quitters.1 ≠ {3} := by
    intro h
    rw [h] at hcard
    simp at hcard
  simp [h0, h1, h2, h3]

/-- Player `0` quitting surely while everyone else continues surely. -/
def stationaryPureRoot : Player → PMF Bool :=
  quittingSoloStationaryRoot 0 (PMF.pure true)

/-- At the pure owner row, every inactive player's joining payoff is `-2`. -/
theorem stationaryCompletion_collision_zero (other : Player)
    (hother : other ≠ 0) :
    quittingSingletonCollisionReward stationaryCompletionReward 0 other = -2 := by
  unfold quittingSingletonCollisionReward
  have hcard : 1 < ({0, other} : Finset Player).card := by
    rw [Finset.card_pair hother.symm]
    norm_num
  rw [stationaryCompletionReward_of_one_lt_card _ hcard]

/-- The pure owner row is exact terminal Nash against arbitrary behavioral
deviations, not merely against stationary deviations. -/
theorem stationaryPureProfile_isExactTerminalNash :
    (quittingGame stationaryCompletionReward).IsεAsymptoticNash
      (quittingTerminalPayoff stationaryCompletionReward) 0
      (quittingStationaryProfile stationaryCompletionReward
        stationaryPureRoot) := by
  apply isεAsymptoticNash_soloStationary_exact
      stationaryCompletionReward 0 (PMF.pure true)
  · simp
  · rw [show quittingSoloReward stationaryCompletionReward 0 0 = 0 by
      rw [quittingSoloReward, stationaryCompletionReward_singleton_set]
      rfl]
  · intro other hother
    rw [stationaryCompletion_collision_zero other hother]
    fin_cases other <;>
      simp [quittingSoloReward, stationaryCompletionReward_singleton_set,
        pairedSingletonReward, pairedSingletonMatrix] at hother ⊢
    all_goals norm_num

/-- The pure stationary profile's terminal payoff is the first singleton
column `(0,3,-1,-1)`. -/
theorem stationaryPureProfile_terminalPayoff :
    quittingTerminalPayoff stationaryCompletionReward
        (quittingStationaryProfile stationaryCompletionReward
          stationaryPureRoot) =
      pairedSingletonReward 0 := by
  funext who
  change quittingTerminalPayoff stationaryCompletionReward
      (quittingStationaryProfile stationaryCompletionReward
        (quittingSoloStationaryRoot 0 (PMF.pure true))) who = _
  rw [quittingTerminalPayoff_soloStationary
    stationaryCompletionReward 0 who (PMF.pure true)]
  · rfl
  · simp

/-- The stationary completion admits the displayed exact stationary uniform
equilibrium payoff. -/
theorem stationaryCompletion_isUniformEquilibriumPayoff :
    (quittingGame stationaryCompletionReward).IsUniformEquilibriumPayoff none
      (pairedSingletonReward 0) := by
  have h := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    stationaryCompletionReward _ stationaryPureProfile_isExactTerminalNash
  rwa [stationaryPureProfile_terminalPayoff] at h

end FourPlayerPairedSingleton
end GameTheory
