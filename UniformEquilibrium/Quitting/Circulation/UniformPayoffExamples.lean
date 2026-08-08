/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Circulation.RepairedFourPlayerStressCirculation

/-!
# Uniform payoffs from singleton face circulations

The singleton-circulation compiler turns a bounded face circulation into a
uniform-equilibrium payoff once its floor dominates the quitting punishment
value. This module discharges that final strategic inequality for two concrete
certificates already present in the library:

* the three-player scaled cyclic calibration; and
* the repaired four-player stress circulation.

In both cases the formal bound
`quittingPunishmentValue_le_max_solo` is enough. The certificate floor equals
the positive solo diagonal, so no separate computation of the exact min-max is
needed for these existence results.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

/-- The scaled cyclic circulation floor dominates the formal quitting
punishment value. -/
theorem quittingPunishmentValue_le_cyclicCirculationFloor
    (who : CyclicIndex) :
    quittingPunishmentValue (rewardOfWeight scaledCyclicWeight) who ≤
      cyclicCirculationFloor who := by
  refine
    (quittingPunishmentValue_le_max_solo
      (rewardOfWeight scaledCyclicWeight) who).trans ?_
  have hsolo :
      quittingSetReward (rewardOfWeight scaledCyclicWeight) {who} who =
        scaledCyclicWeight {who} who := by
    simp [quittingSetReward, rewardOfWeight]
  rw [hsolo, scaledCyclicWeight_diagonal]
  norm_num [cyclicCirculationFloor]

/-- The scaled cyclic quitting game has a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_scaledCyclicWeight :
    ∃ payoff : Payoff CyclicIndex,
      (quittingGame (rewardOfWeight scaledCyclicWeight)).IsUniformEquilibriumPayoff
        none payoff := by
  exact
    quittingGame_exists_uniformEquilibriumPayoff_of_singletonCirculation
      cyclicCirculation cyclicCirculationSupport
      1 (by norm_num) abs_scaledCyclicWeight_le_one
      (1 / 2) (fun _ ↦ le_rfl) (by norm_num)
      quittingPunishmentValue_le_cyclicCirculationFloor

namespace RepairedFourPlayerStress

/-- The repaired stress circulation floor dominates the formal quitting
punishment value. -/
theorem quittingPunishmentValue_le_stressFloor (who : Player) :
    quittingPunishmentValue (rewardOfWeight stressWeight) who ≤
      stressFloor who := by
  refine
    (quittingPunishmentValue_le_max_solo
      (rewardOfWeight stressWeight) who).trans ?_
  have hsolo :
      quittingSetReward (rewardOfWeight stressWeight) {who} who =
        stressWeight {who} who := by
    simp [quittingSetReward, rewardOfWeight]
  rw [hsolo, stressWeight_diagonal]
  norm_num [stressFloor]

/-- The repaired four-player stress quitting game has a
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_stressWeight :
    ∃ payoff : Payoff Player,
      (quittingGame (rewardOfWeight stressWeight)).IsUniformEquilibriumPayoff
        none payoff := by
  exact
    quittingGame_exists_uniformEquilibriumPayoff_of_singletonCirculation
      stressCirculation stressCirculationSupport
      3 (by norm_num) abs_stressWeight_le_three
      (1 / 2) (fun _ ↦ le_rfl) (by norm_num)
      quittingPunishmentValue_le_stressFloor

end RepairedFourPlayerStress
end GameTheory
