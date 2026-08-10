/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseUniform
import UniformEquilibrium.Quitting.Cycles.ConditionedSoloExtraction
import UniformEquilibrium.Quitting.Punishment.SoloFloorCompletion

/-!
# Deficient clocks on a proper singleton-tight face

A summable conditioned player-deleted clock concentrates the entire
conditioned payoff vector on that player's singleton payoff.  If the uniform
rescaled pure-Quit defect vanishes, the rescaled rows simultaneously converge
to the all-Continue root, so every player's own singleton payoff lies below
that limiting singleton vector.  The generic singleton-floor solo compiler
then produces a uniform-equilibrium payoff.

This removes deleted-clock completeness as an independent obstruction even
when some phantom-boundary coordinates are strict.  The only remaining
obstruction is the same nonvanishing immediate-Quit defect that appears in
the deleted-complete proper-face compiler.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A summable conditioned deleted clock and vanishing uniform rescaled
pure-Quit defect produce the deficient owner's singleton payoff as a uniform
equilibrium payoff.  No singleton-tightness or source-floor hypothesis is
needed for the other players. -/
theorem
    isUniformEquilibriumPayoff_solo_of_summableClock_and_vanishingQuitDefect
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hdefect : Tendsto
      (quittingConditionedRescaledQuitDefect reward roots value boundary
        hpositive) atTop (nhds 0))
    (owner : ι)
    (hclock : Summable (fun time =>
      quittingTailConditionedOpponentWeight roots time owner))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let M := quittingRewardBound reward
  have hconditionedLimit : ∀ who,
      Tendsto (fun time =>
        quittingTailConditionedValue roots value boundary time who)
        atTop (nhds (reward (quittingSingletonTerminal owner) who)) := by
    intro who
    exact tendsto_quittingTailConditionedValue_solo_of_summableOpponentWeight
      (reward := reward) roots value boundary hpolicy
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hpositive heventualZero
        hconditionedBound owner hclock who
  have hquitLimit : ∀ who,
      Tendsto (fun time =>
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who)
        atTop (nhds (reward (quittingSingletonTerminal who) who)) := by
    intro who
    let error : ℕ → ℝ := fun time =>
      2 * M * Fintype.card ι *
        quittingTailConditionedAbsorptionWeight roots time
    have herror : Tendsto error atTop (nhds 0) := by
      have hscaled := hmesh.const_mul (2 * M * Fintype.card ι)
      simpa [error, mul_assoc] using hscaled
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ time,
        ‖quittingStationaryFixedOpponentsQuitValue reward
              (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who -
            reward (quittingSingletonTerminal who) who‖ ≤ error time := by
      intro time
      rw [Real.norm_eq_abs]
      have hlocal :=
        abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
          (reward := reward)
          (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
      have hopponent :=
        quittingTailDiffuseRescaledRoot_opponentAbsorption_le_card_mul_weight
          roots time who (hpositive time)
      have hfactor : 0 ≤ 2 * M := by
        dsimp only [M]
        exact mul_nonneg (by norm_num)
          (quittingRewardBound_nonneg reward)
      exact hlocal.trans <| by
        dsimp only [error]
        simpa only [M, mul_assoc] using
          mul_le_mul_of_nonneg_left hopponent hfactor
    exact squeeze_zero (fun time => norm_nonneg _) hbound herror
  have hfloor : ∀ who,
      quittingSoloReward reward who who ≤
        quittingSoloReward reward owner who := by
    intro who
    have hpointwise : ∀ time,
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingTailDiffuseRescaledRoot roots time (hpositive time)) who ≤
          quittingTailConditionedValue roots value boundary time who +
            quittingConditionedRescaledQuitDefect reward roots value boundary
              hpositive time := by
      intro time
      exact
        quittingStationaryFixedOpponentsQuitValue_le_conditionedValue_add_defect
          (reward := reward) roots value boundary hpositive time who
    have hrhs : Tendsto (fun time =>
        quittingTailConditionedValue roots value boundary time who +
          quittingConditionedRescaledQuitDefect reward roots value boundary
            hpositive time)
        atTop (nhds (reward (quittingSingletonTerminal owner) who)) := by
      simpa using (hconditionedLimit who).add hdefect
    have hle := le_of_tendsto_of_tendsto (hquitLimit who) hrhs
      (Filter.Eventually.of_forall hpointwise)
    change reward (quittingSingletonTerminal who) who ≤
      reward (quittingSingletonTerminal owner) who
    exact hle
  exact isUniformEquilibriumPayoff_soloReward_of_soloFloor_of_punishmentIR
    reward owner hfloor hpunishment

end GameTheory
