/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Positive target-edge atoms do not supply a state-matched strategic sign

This two-player regression preserves the target-side pure-time edge, its
literal causal date, and its actual terminal coalition.  Moving the observer's
quit time from date zero to date one raises terminal payoff by one.  The whole
gain is carried by a positive collision atom at date one, with target mass one.

Nevertheless the observer's Quit-versus-Continue endpoint difference, and
hence its coordinate Nash defect, vanish at the reached date-one root for
every continuation payoff.  The gain came from surviving date zero; the
marked action is strategically neutral because the clock-alone and collision
rewards agree.

Thus the positive-slope target-edge output cannot by itself be compiled into
a state-matched punishment, toggle, or atomic-blocker certificate.  Such a
compiler needs an additional local successor/cap sign (or directly a positive
coordinate defect) at the marked row.  This statement concerns the target
edge's own atom and makes no identification with the possibly different
coalition carried by the four-profile rectangle atom.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace PositiveSlopeTargetEdgeStateMatchRegression

abbrev Player := Bool
abbrev observer : Player := false
abbrev clock : Player := true

def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if who = observer then
      if terminal.val = {observer} then 0
      else if terminal.val = {clock} then 1
      else 1
    else 0

/-- The clock quits surely at the marked date and continues elsewhere. -/
def roots (time : ℕ) (who : Player) : PMF Bool :=
  if who = clock ∧ time = 1 then PMF.pure true else PMF.pure false

def base : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward roots 0

/-- The source endpoint makes the observer quit at date zero. -/
def source : (quittingGame reward).BehaviorProfile :=
  Function.update base observer
    (quittingPureTimeBehaviorStrategy reward observer (some 0))

/-- The profitable target endpoint postpones the observer to date one. -/
def target : (quittingGame reward).BehaviorProfile :=
  Function.update base observer
    (quittingPureTimeBehaviorStrategy reward observer (some 1))

def collisionTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{observer, clock}, by simp⟩

/-- The actual live root at the positive atom's causal date. -/
def markedRoot : Player → PMF Bool :=
  quittingProfileLiveRoot reward target 1

theorem source_payoff_eq_zero :
    quittingTerminalPayoff reward source observer = 0 := by
  rw [source, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    base, quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [expect_eq_sum, roots, reward, observer, clock, quittingRootPayoff,
    quittingQuitters, Finset.ext_iff]

theorem target_payoff_eq_one :
    quittingTerminalPayoff reward target observer = 1 := by
  rw [target, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    base, quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp
  unfold quittingFixedOpponentsContinueReward
    quittingFixedOpponentsContinueMass quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool,
    Math.PMFProduct.expect_pmfPi_bool]
  simp [expect_eq_sum, roots, reward, observer, clock, quittingRootPayoff,
    quittingQuitters, quittingStationaryContinueMass,
    quittingAllContinueAction, Finset.ext_iff]

/-- The target-side edge is profitable by exactly one. -/
theorem targetEdge_gain_eq_one :
    quittingTerminalPayoff reward target observer -
        quittingTerminalPayoff reward source observer = 1 := by
  rw [target_payoff_eq_one, source_payoff_eq_zero]
  norm_num

theorem target_collision_mass_eq_one :
    quittingTerminalOutcomeMass reward target (some collisionTerminal) = 1 := by
  rw [target,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward base observer 1 collisionTerminal (by simp [collisionTerminal]),
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  simp [base, roots, quittingProfileLiveRoot, quittingRootSequenceProfile,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingJointSurvivalWeight, quittingFiniteContinueWeight,
    quittingRootCoalitionMass, quittingRootQuitRates, coalitionMass,
    collisionTerminal, quittingStationaryContinueMass]
  rw [show ({clock} : Finset Player)ᶜ.erase observer = ∅ by decide]
  simp [quittingAllContinueAction]

theorem source_collision_mass_eq_zero :
    quittingTerminalOutcomeMass reward source (some collisionTerminal) = 0 := by
  rw [source,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward base observer 0 collisionTerminal (by simp [collisionTerminal]),
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  simp [base, roots, quittingProfileLiveRoot, quittingRootSequenceProfile,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingRootCoalitionMass, quittingRootQuitRates, coalitionMass,
    collisionTerminal]

/-- The profitable edge has a positive actual terminal collision atom. -/
theorem targetEdge_collisionAtom_eq_one :
    quittingTerminalPayoffDifferenceAtom reward target source observer
      (some collisionTerminal) = 1 := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [target_collision_mass_eq_one, source_collision_mass_eq_zero]
  simp [quittingTerminalOutcomeReward, reward, collisionTerminal, observer,
    Finset.ext_iff]

theorem target_collision_stageMass_eq_one :
    quittingStageCoalitionMass reward target 1 collisionTerminal = 1 := by
  rw [target, ← quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
    reward base observer 1 collisionTerminal (by simp [collisionTerminal])]
  simpa only [target] using target_collision_mass_eq_one

theorem source_collision_stageMass_eq_zero :
    quittingStageCoalitionMass reward source 1 collisionTerminal = 0 := by
  unfold quittingStageCoalitionMass
  rw [source,
    quittingLiveMass_update_pureTime_some_eq_zero_of_stop_lt
      reward base observer (by omega : 0 < 1)]
  simp

/-- The same atom remains positive after localization to its literal date. -/
theorem targetEdge_collisionStageAtom_eq_one :
    quittingStoppingLawRectangleStageAtom reward base observer
      (quittingPureTimeBehaviorStrategy reward observer (some 0))
      (quittingPureTimeBehaviorStrategy reward observer (some 1)) observer 1
      collisionTerminal = 1 := by
  unfold quittingStoppingLawRectangleStageAtom
  rw [show Function.update base observer
        (quittingPureTimeBehaviorStrategy reward observer (some 1)) = target by rfl,
    show Function.update base observer
        (quittingPureTimeBehaviorStrategy reward observer (some 0)) = source by rfl,
    target_collision_stageMass_eq_one, source_collision_stageMass_eq_zero]
  simp [reward, collisionTerminal, observer, Finset.ext_iff]

theorem markedRoot_eq_allQuit :
    markedRoot = fun _ => PMF.pure true := by
  funext who
  cases who <;>
    simp [markedRoot, target, base, quittingProfileLiveRoot,
      quittingRootSequenceProfile, quittingPureTimeBehaviorStrategy,
      quittingPureTimeHazard, roots, observer, clock]

/-- At the exact reached row carrying the positive atom, Quit and Continue
have equal value for the observer for every attached continuation. -/
theorem markedRow_endpointDifference_eq_zero (tail : Payoff Player) :
    quittingRootEndpointDifference reward tail markedRoot observer = 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool,
    Math.PMFProduct.expect_pmfPi_bool]
  simp [markedRoot, target, base, quittingProfileLiveRoot,
    quittingRootSequenceProfile, roots, reward, observer, clock,
    quittingRootPayoff, quittingQuitters, Finset.nonempty_iff_ne_empty,
    Finset.ext_iff]

/-- In particular the positive atom supplies no state-matched strategic
defect, even if the continuation payoff is chosen after seeing the row. -/
theorem markedRow_coordinateNashDefect_eq_zero (tail : Payoff Player) :
    quittingRootCoordinateNashDefect reward tail markedRoot observer = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    markedRow_endpointDifference_eq_zero]
  simp

/-- Capstone no-go: a profitable target edge with positive terminal and
chronological atoms, at actual target mass one, can still be strategically
neutral at the atom's literal reached state. -/
theorem profitableEdge_positiveActualAtom_but_markedState_neutral :
    quittingTerminalPayoff reward target observer -
          quittingTerminalPayoff reward source observer = 1 ∧
      quittingTerminalPayoffDifferenceAtom reward target source observer
          (some collisionTerminal) = 1 ∧
      quittingStoppingLawRectangleStageAtom reward base observer
          (quittingPureTimeBehaviorStrategy reward observer (some 0))
          (quittingPureTimeBehaviorStrategy reward observer (some 1))
          observer 1 collisionTerminal = 1 ∧
      quittingTerminalOutcomeMass reward target (some collisionTerminal) = 1 ∧
      ∀ tail : Payoff Player,
        quittingRootEndpointDifference reward tail markedRoot observer = 0 ∧
          quittingRootCoordinateNashDefect reward tail markedRoot observer = 0 := by
  exact ⟨targetEdge_gain_eq_one, targetEdge_collisionAtom_eq_one,
    targetEdge_collisionStageAtom_eq_one, target_collision_mass_eq_one,
    fun tail => ⟨markedRow_endpointDifference_eq_zero tail,
      markedRow_coordinateNashDefect_eq_zero tail⟩⟩

end PositiveSlopeTargetEdgeStateMatchRegression

end GameTheory
