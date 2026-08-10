/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion

/-!
# Counterexample exclusion on the singleton-tight diffuse boundary

The conditioned diffuse compilers no longer require the optimized source
values to dominate singleton payoffs.  Exact policy and endpoint Nash charge
that possible deficit to the deleted clock.  Consequently a counterexample
seam whose remaining absorption is positive and diffuse cannot converge to
the full singleton boundary.

The result keeps only the two genuine conditioning hypotheses explicit:
eventual absorption is positive at every date, and the normalized one-stage
mesh tends to zero.  Vanishing remaining absorption follows from the seam's
summable joint-absorption clock, while conditioned reward-box boundedness and
singleton individual rationality follow from the canonical seam itself.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

/-- **Singleton-tight diffuse closure.**  A canonical counterexample seam
cannot simultaneously have positive remaining absorption at every date,
vanishing conditioned mesh, and a phantom boundary equal to every player's
singleton payoff.  Both complete and deficient deleted clocks are consumed
by the conditioned compiler. -/
theorem not_all_limitValue_eq_singleton_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ¬ ∀ who, seam.limit.value who = quittingSoloBaseline reward who := by
  intro htight
  letI : Nonempty ι := regime.nonempty_players
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  have hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (seam.tail_edge time).1.1
  have hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time) := by
    intro time
    simpa only [value, roots, quittingDynamicDebtTailRoots] using
      (seam.tail_edge time).1.2
  have hsummable : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)) := by
    change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    exact seam.jointAbsorption_summable
  have heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0) :=
    tendsto_quittingTailEventualAbsorption_zero_of_summable_absorption
      roots hsummable
  have hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value seam.limit.value
        time player| ≤ quittingRewardBound reward := by
    intro time player
    exact abs_quittingTailConditionedValue_le roots value seam.limit.value
      hpolicy (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) seam.value_tendsto time
      (hpositive time) player
  have hpunishment : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who := by
    intro who
    calc
      quittingPunishmentValue reward who ≤ seam.limit.value who :=
        seam.punishmentValue_le_limitValue who
      _ = quittingSoloReward reward who who := by
        rw [htight who]
        rfl
  have hexists :=
    quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseTail_punishmentIR
      reward roots value seam.limit.value hpolicy hnash hpositive
      heventualZero hconditionedBound htight hmesh hpunishment
  exact regime.not_exists_uniformEquilibriumPayoff hexists

/-- In the diffuse positive-absorption branch, a counterexample therefore
has a genuinely strict phantom plateau coordinate.  The reverse weak
inequality is already forced by exact Nash at the limiting all-Continue
self-loop. -/
theorem exists_singleton_lt_limitValue_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who, quittingSoloBaseline reward who < seam.limit.value who := by
  by_contra hnot
  push Not at hnot
  apply seam.not_all_limitValue_eq_singleton_of_diffuse hpositive hmesh
  intro who
  apply le_antisymm
  · exact hnot who
  · simpa [quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using seam.limit.soloReward_le_value who

end QuittingCounterexampleSeamWitness

end GameTheory
