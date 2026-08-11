/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ThreeBranchDisjunction
import UniformEquilibrium.Quitting.Punishment.CompletedCycle

/-!
# Punishment completion of a positive-rate solo cycle

A positive-rate solo row that is exact endpoint Nash against its own
singleton payoff vector is a self-consistent absorbing period-one cycle.
Every non-owner coordinate contracts because the owner quits with positive
probability.  The only noncontracting coordinate is the owner, so the exact
punishment-completed cycle compiler needs precisely one further inequality:

`quittingPunishmentValue reward owner ≤ quittingSoloReward reward owner owner`.

Under that inequality the singleton payoff vector is a uniform-equilibrium
payoff even when the owner's own singleton payoff is negative.  This is
strictly more flexible than the passive stationary solo compiler, whose
Never deviation requires a nonnegative owner payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Punishment-completed solo-cycle compiler.**  Exact endpoint Nash at a
positive solo rate, together with the owner's exact punishment floor, makes
the owner's singleton payoff vector a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let value : Payoff ι := quittingSoloReward reward owner
  let root : ι → PMF Bool := quittingSoloStationaryRoot owner hazard
  let block : QuittingFiniteNashBellmanPath ι 1 :=
    quittingRowBlock value root
  have hvalueBound : ∀ who, |value who| ≤ quittingRewardBound reward := by
    intro who
    exact abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) who
  have hsuccessor : value =
      quittingRootSuccessorPayoff reward value root := by
    exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward owner hazard).symm
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    dsimp only [root]
    rw [quittingRootAbsorptionMass_soloStationaryRoot]
    exact hpositive
  have hblock : IsQuittingCyclicContinuationBlock reward value 1 block :=
    quittingRowBlock_isQuittingCyclicContinuationBlock
      reward value root hvalueBound hsuccessor hnash habsorption
  have hcycleRoot : ∀ phase : Fin 1,
      quittingCyclicContinuationBlockCycle 0 block phase = root := by
    intro phase
    rw [quittingCyclicContinuationBlockCycle_eq_pathRoots,
      quittingFiniteNashBellmanPathRoots_of_lt 1 block phase.val
        phase.isLt]
    dsimp only [block]
    rw [quittingRootOfSimplex_quittingRowBlock]
  have hadmissible : IsQuittingCyclePunishmentAdmissible reward
      (quittingCyclicContinuationBlockCycle 0 block) := by
    intro who
    by_cases hwho : who = owner
    · subst who
      exact Or.inr hpunishment
    · left
      have hprod :
          (∏ phase : Fin 1,
              quittingStationaryFixedOpponentsContinueMass
                (quittingCyclicContinuationBlockCycle 0 block phase) who) =
            quittingStationaryFixedOpponentsContinueMass
              (quittingCyclicContinuationBlockCycle 0 block 0) who :=
        Fin.prod_univ_one _
      rw [hprod, hcycleRoot 0]
      exact quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
        hwho hazard hpositive
  exact isUniformEquilibriumPayoff_terminal_of_punishmentAdmissibleBlock
    reward value 0 block hblock hadmissible

end GameTheory
