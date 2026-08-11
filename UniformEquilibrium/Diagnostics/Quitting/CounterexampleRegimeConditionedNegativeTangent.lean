/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneTangentReadout
import UniformEquilibrium.Quitting.Cycles.ConditionedTangentSeam

/-!
# Conditioned interpretation of a counterexample's negative tangent

The period-one tangent readout compares a selected root's absorbing delivery
with the source tail's unconditioned far annotation.  This file rewrites that
comparison through the honest value conditioned on eventual absorption.

The rewrite isolates the exact remaining alternative.  A finite negative
tangent either remains a negative conditioned delivery gap, or is paid for by
positive phantom survival and a strict boundary-over-conditioned gap.  Thus a
tight boundary coordinate cannot hide negative motion once the conditioned
state is known to stay on its safe side.

For an owner carrying positive limiting singleton mass, the separate local
phase obstruction is already complete: the selected owner eventually has
positive Quit probability, complementarity kills the phase slack, and the
period-one phase evaluator is strictly profitable.  This is still a
diagnostic payoff against the repeated root, not an attachment of that root
to the varying canonical suffix.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

namespace CounterexampleRegimePeriodOneTangentReadout

variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- Exact decomposition of a selected one-stage tangent through the honest
conditioned far value. -/
theorem periodOneReadoutTangent_eq_conditionedGap_add_phantomGap
    (index : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail)
      (readout.start index + 1)) :
    seam.periodOneReadoutTangent readout.start index who =
      (quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 -
        quittingTailConditionedValue
          (quittingDynamicDebtTailRoots seam.tail)
          (fun time ↦ (seam.tail time).1.1) seam.limit.value
          (readout.start index + 1) who) +
      quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail)
          (readout.start index + 1) *
        (quittingTailConditionedValue
            (quittingDynamicDebtTailRoots seam.tail)
            (fun time ↦ (seam.tail time).1.1) seam.limit.value
            (readout.start index + 1) who -
          seam.limit.value who) := by
  have hidentity :=
    conditionalAbsorbingDelivery_sub_value_eq_conditionedGap_add_phantomGap
      (reward := reward)
      (quittingDynamicDebtTailRoots seam.tail)
      (fun time ↦ (seam.tail time).1.1) seam.limit.value
      (readout.start index) who hnext
  have hidentity' :
      quittingRootConditionalAbsorbingDelivery reward
            (seam.periodOneReadoutRoot readout.start index) who -
          (seam.tail (readout.start index + 1)).1.1 who =
        (quittingRootConditionalAbsorbingDelivery reward
              (seam.periodOneReadoutRoot readout.start index) who -
            quittingTailConditionedValue
              (quittingDynamicDebtTailRoots seam.tail)
              (fun time ↦ (seam.tail time).1.1) seam.limit.value
              (readout.start index + 1) who) +
          quittingJointSurvivalLimit
              (quittingDynamicDebtTailRoots seam.tail)
              (readout.start index + 1) *
            (quittingTailConditionedValue
                (quittingDynamicDebtTailRoots seam.tail)
                (fun time ↦ (seam.tail time).1.1) seam.limit.value
                (readout.start index + 1) who -
              seam.limit.value who) := by
    simpa [periodOneReadoutRoot] using hidentity
  rw [← quittingWindowRestartDelivery_periodOne_one_eq_conditionalAbsorbingDelivery
    (reward := reward)
    (seam.periodOneReadoutRoot readout.start index) who] at hidentity'
  simpa [periodOneReadoutTangent] using hidentity'

/-- At a selected edge, negative tangent motion either survives conditioning
or is quantitatively financed by a strict phantom-boundary gap. -/
theorem conditionedGap_neg_or_strictPhantomFunding
    (index : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail)
      (readout.start index + 1))
    (htangent : seam.periodOneReadoutTangent readout.start index who < 0) :
    (quittingWindowRestartDelivery reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) who 0 1 -
        quittingTailConditionedValue
          (quittingDynamicDebtTailRoots seam.tail)
          (fun time ↦ (seam.tail time).1.1) seam.limit.value
          (readout.start index + 1) who < 0) ∨
      (0 < quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail)
          (readout.start index + 1) ∧
        quittingTailConditionedValue
            (quittingDynamicDebtTailRoots seam.tail)
            (fun time ↦ (seam.tail time).1.1) seam.limit.value
            (readout.start index + 1) who < seam.limit.value who ∧
        -seam.periodOneReadoutTangent readout.start index who ≤
          quittingJointSurvivalLimit
              (quittingDynamicDebtTailRoots seam.tail)
              (readout.start index + 1) *
            (seam.limit.value who -
              quittingTailConditionedValue
                (quittingDynamicDebtTailRoots seam.tail)
                (fun time ↦ (seam.tail time).1.1) seam.limit.value
                (readout.start index + 1) who)) := by
  have halternative :=
    conditionedGap_neg_or_strictPhantomFunding_of_tangent_neg
      (reward := reward)
      (quittingDynamicDebtTailRoots seam.tail)
      (fun time ↦ (seam.tail time).1.1) seam.limit.value
      (readout.start index) who hnext
      (by
        simpa [periodOneReadoutTangent, periodOneReadoutRoot,
          quittingWindowRestartDelivery_periodOne_one_eq_conditionalAbsorbingDelivery]
          using htangent)
  simpa [periodOneReadoutTangent, periodOneReadoutRoot,
    quittingWindowRestartDelivery_periodOne_one_eq_conditionalAbsorbingDelivery]
    using halternative

/-- Positive limiting singleton mass forces the displayed owner to have
positive prescribed Quit probability at every sufficiently late selected
root. -/
theorem eventually_quitProbability_pos_of_packetMass_pos
    (player : ι) (hmass : 0 < readout.packet.mass player) :
    ∀ᶠ index in atTop,
      0 < (seam.periodOneReadoutRoot
        readout.start index player true).toReal := by
  have hmassEventually : ∀ᶠ index in atTop,
      0 < seam.periodOneReadoutMass readout.start index player :=
    (readout.mass_tendsto player).eventually_const_lt hmass
  filter_upwards [hmassEventually] with index hmassIndex
  have hcoalition : 0 < quittingRootCoalitionMass
      (seam.periodOneReadoutRoot readout.start index) {player} := by
    change 0 < quittingRootCoalitionMass
        (seam.periodOneReadoutRoot readout.start index) {player} /
      quittingRootAbsorptionMass
        (seam.periodOneReadoutRoot readout.start index) at hmassIndex
    rcases (div_pos_iff.mp hmassIndex) with hpositive | hnegativeDenominator
    · exact hpositive.1
    · exact (not_lt_of_ge (readout.absorption_pos index).le
        hnegativeDenominator.2).elim
  exact
    QuittingFiniteRootWindow.quitProbability_pos_of_singletonCoalitionMass_pos
      (seam.periodOneReadoutRoot readout.start index) player hcoalition

/-- On a negative tangent coordinate carrying positive limiting owner mass,
the actual phase-evaluator gain converges to the strictly positive number
`-packet.tangent player`.  This strengthens the sign diagnostic without
attaching the repeated root to the varying suffix. -/
theorem tendsto_phaseGain_of_mass_pos_of_tangent_neg
    (player : ι) (hmass : 0 < readout.packet.mass player)
    (_hnegative : readout.packet.tangent player < 0) :
    Tendsto (fun index ↦
      quittingPeriodicWindowBestPhaseStop reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 1 -
          quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 0 1)
      atTop (nhds (-readout.packet.tangent player)) := by
  have hquit := readout.eventually_quitProbability_pos_of_packetMass_pos
    seam player hmass
  have habsorption :=
    seam.rootAbsorptionMass_tendsto_zero.comp readout.start_tendsto
  have hcontinue : Tendsto (fun index ↦
      quittingStationaryContinueMass
        (seam.periodOneReadoutRoot readout.start index)) atTop (nhds 1) := by
    have honeSub :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
        habsorption
    simpa [quittingRootAbsorptionMass, periodOneReadoutRoot,
      quittingDynamicDebtTailRoots] using honeSub
  have hlimit := (hcontinue.mul (readout.tangent_tendsto player)).neg
  have hlimit' : Tendsto (fun index ↦
      -(quittingStationaryContinueMass
          (seam.periodOneReadoutRoot readout.start index) *
        seam.periodOneReadoutTangent readout.start index player))
      atTop (nhds (-readout.packet.tangent player)) := by
    simpa only [one_mul] using hlimit
  apply hlimit'.congr'
  filter_upwards [hquit] with index hquitIndex
  rw [readout.bestPhaseStop_sub_restartDelivery_eq seam index player,
    readout.phaseSlack_eq_zero_of_quitProbability_pos
      seam index player hquitIndex]
  ring

/-- A negative tangent carried by positive limiting owner mass has no
eventual off-support escape: it yields a strict period-one phase gain along
all sufficiently late selected roots. -/
theorem eventually_phaseGain_of_mass_pos_of_tangent_neg
    (player : ι) (hmass : 0 < readout.packet.mass player)
    (hnegative : readout.packet.tangent player < 0) :
    ∀ᶠ index in atTop,
      0 < quittingPeriodicWindowBestPhaseStop reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 1 -
          quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) player 0 1 :=
  (readout.tendsto_phaseGain_of_mass_pos_of_tangent_neg
    seam player hmass hnegative).eventually_const_lt (neg_pos.mpr hnegative)

end CounterexampleRegimePeriodOneTangentReadout

end QuittingCounterexampleSeamWitness

end GameTheory
