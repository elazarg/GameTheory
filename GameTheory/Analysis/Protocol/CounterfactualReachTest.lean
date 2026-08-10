/-
# Counterfactual-reach consumers

The one-shot simultaneous fixture separates focal, opponent, and actual reach.
The two-step fixture checks that recursive reach multiplies across an actual
canonical trace rather than passing only at the final step.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Examples.FOSG
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualReachTest

open GameTheory.Languages GameTheory.Probability GameTheory.Protocol

namespace Simultaneous

open GameTheory.Languages.NFG.OneShotFOSG

abbrev source := GameTheory.Examples.FOSG.twoBit

def actionPolicy (who action : Bool) :
    source.information.BehavioralPolicy who :=
  (Policy.ofAction GameTheory.Examples.FOSG.twoBitSource action).toBehavioral

def focalTrueOpponentTrue :
    (player : Bool) → source.information.BehavioralPolicy player
  | false => actionPolicy false true
  | true => actionPolicy true true

def focalFalseOpponentTrue :
    (player : Bool) → source.information.BehavioralPolicy player
  | false => actionPolicy false false
  | true => actionPolicy true true

def focalTrueOpponentFalse :
    (player : Bool) → source.information.BehavioralPolicy player
  | false => actionPolicy false true
  | true => actionPolicy true false

theorem profiles_eq_off_focal (other : Bool) (hne : other ≠ false) :
    focalTrueOpponentTrue other = focalFalseOpponentTrue other := by
  cases other
  · exact False.elim (hne rfl)
  · rfl

def chosenJoint :
    { joint : (player : Bool) → Option (source.execution.Action player) //
      source.execution.Legal source.execution.initHistory.state joint } :=
  NFG.OneShotFOSG.chooserOfProfile
    GameTheory.Examples.FOSG.twoBitSource (fun _ => true)
    source.execution.initHistory.state (by
      simp [source, NFG.OneShotFOSG.execution,
        ExecutionProtocol.initHistory])

def target : source.execution.State :=
  .finished (fun _ => true)

theorem chosenJoint_transition :
    source.execution.step source.execution.initHistory.state chosenJoint =
      FinDist.pure target := by
  have hrun := NFG.OneShotFOSG.runFor_chooserOfProfile_one
    GameTheory.Examples.FOSG.twoBitSource (fun _ => true)
  simpa [ExecutionProtocol.runFor, chosenJoint, target,
    ExecutionProtocol.initHistory] using hrun

theorem targetRealized :
    target ∈ (source.execution.step source.execution.initHistory.state
      chosenJoint).support := by
  rw [chosenJoint_transition]
  exact FinDist.mem_support_pure.mpr rfl

def chosenTrace : source.execution.Trace target :=
  source.execution.initHistory.trace.extend chosenJoint.1 chosenJoint.2
    targetRealized

theorem focal_true_player_factor :
    source.information.playerStepProb focalTrueOpponentTrue false
      source.execution.initHistory.trace chosenJoint = 1 := by
  classical
  simp [InformationModel.playerStepProb, InformationModel.choicesOfLegal,
    focalTrueOpponentTrue, actionPolicy, chosenJoint,
    InformationModel.Policy.toBehavioral, NFG.OneShotFOSG.Policy.ofAction,
    InfoSignals.infoOf, NFG.OneShotFOSG.signals,
    NFG.OneShotFOSG.chooserOfProfile, ExecutionProtocol.initHistory]

theorem focal_false_player_factor :
    source.information.playerStepProb focalFalseOpponentTrue false
      source.execution.initHistory.trace chosenJoint = 0 := by
  classical
  simp [InformationModel.playerStepProb, InformationModel.choicesOfLegal,
    focalFalseOpponentTrue, actionPolicy, chosenJoint,
    InformationModel.Policy.toBehavioral, NFG.OneShotFOSG.Policy.ofAction,
    InfoSignals.infoOf, NFG.OneShotFOSG.signals,
    NFG.OneShotFOSG.chooserOfProfile, ExecutionProtocol.initHistory]
  apply FinDist.prob_pure_of_ne
  intro heq
  have hvalue := congrArg Subtype.val heq
  simp at hvalue

theorem counterfactual_factor_eq_one :
    source.information.counterfactualStepProb
      focalTrueOpponentTrue false source.execution.initHistory.trace
      chosenJoint target = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb, chosenJoint_transition,
    FinDist.prob_pure_self]
  unfold InformationModel.opponentsStepProb
  rw [show Finset.univ.erase false = {true} by decide,
    Finset.prod_singleton]
  simp [InformationModel.choicesOfLegal, focalTrueOpponentTrue,
    actionPolicy, chosenJoint, InformationModel.Policy.toBehavioral,
    NFG.OneShotFOSG.Policy.ofAction, InfoSignals.infoOf,
    NFG.OneShotFOSG.signals, NFG.OneShotFOSG.chooserOfProfile,
    ExecutionProtocol.initHistory]

theorem opponent_false_counterfactual_factor_eq_zero :
    source.information.counterfactualStepProb
      focalTrueOpponentFalse false source.execution.initHistory.trace
      chosenJoint target = 0 := by
  classical
  rw [InformationModel.counterfactualStepProb, chosenJoint_transition,
    FinDist.prob_pure_self]
  unfold InformationModel.opponentsStepProb
  rw [show Finset.univ.erase false = {true} by decide,
    Finset.prod_singleton]
  simp [InformationModel.choicesOfLegal, focalTrueOpponentFalse,
    actionPolicy, chosenJoint, InformationModel.Policy.toBehavioral,
    NFG.OneShotFOSG.Policy.ofAction, InfoSignals.infoOf,
    NFG.OneShotFOSG.signals, NFG.OneShotFOSG.chooserOfProfile,
    ExecutionProtocol.initHistory]
  apply FinDist.prob_pure_of_ne
  intro heq
  have hvalue := congrArg Subtype.val heq
  simp at hvalue

theorem counterfactual_ignores_focal_change :
    source.information.counterfactualReachProbability
        focalTrueOpponentTrue false chosenTrace =
      source.information.counterfactualReachProbability
        focalFalseOpponentTrue false chosenTrace :=
  source.information.counterfactualReachProbability_eq_of_eq_off
    profiles_eq_off_focal chosenTrace

theorem focal_true_player_reach_eq_one :
    source.information.playerReachProbability
      focalTrueOpponentTrue false chosenTrace = 1 := by
  simp only [chosenTrace, InformationModel.playerReachProbability]
  have hstep (hlegal : source.execution.Legal
      source.execution.initHistory.state chosenJoint.1) :
      source.information.playerStepProb focalTrueOpponentTrue false
        source.execution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ = 1 := by
    simpa only using focal_true_player_factor
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

theorem focal_false_player_reach_eq_zero :
    source.information.playerReachProbability
      focalFalseOpponentTrue false chosenTrace = 0 := by
  simp only [chosenTrace, InformationModel.playerReachProbability]
  have hstep (hlegal : source.execution.Legal
      source.execution.initHistory.state chosenJoint.1) :
      source.information.playerStepProb focalFalseOpponentTrue false
        source.execution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ = 0 := by
    simpa only using focal_false_player_factor
  rw [hstep]
  ring

theorem counterfactual_reach_eq_one :
    source.information.counterfactualReachProbability
      focalTrueOpponentTrue false chosenTrace = 1 := by
  simp only [chosenTrace, InformationModel.counterfactualReachProbability]
  have hstep (hlegal : source.execution.Legal
      source.execution.initHistory.state chosenJoint.1) :
      source.information.counterfactualStepProb focalTrueOpponentTrue false
        source.execution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ target = 1 := by
    simpa only using counterfactual_factor_eq_one
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

theorem opponent_false_counterfactual_reach_eq_zero :
    source.information.counterfactualReachProbability
      focalTrueOpponentFalse false chosenTrace = 0 := by
  simp only [chosenTrace, InformationModel.counterfactualReachProbability]
  have hstep (hlegal : source.execution.Legal
      source.execution.initHistory.state chosenJoint.1) :
      source.information.counterfactualStepProb focalTrueOpponentFalse false
        source.execution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ target = 0 := by
    simpa only using opponent_false_counterfactual_factor_eq_zero
  rw [hstep]
  ring

theorem canonical_history_reach_factors :
    source.information.historyReachProbability focalTrueOpponentTrue
        ⟨target, chosenTrace⟩ = 1 ∧
      source.information.historyReachProbability focalFalseOpponentTrue
        ⟨target, chosenTrace⟩ = 0 ∧
      source.information.counterfactualReachProbability
        focalTrueOpponentTrue false chosenTrace = 1 ∧
      source.information.counterfactualReachProbability
        focalTrueOpponentFalse false chosenTrace = 0 := by
  constructor
  · rw [source.information.historyReachProbability_eq_player_mul_counterfactual
      focalTrueOpponentTrue false chosenTrace,
      focal_true_player_reach_eq_one, counterfactual_reach_eq_one]
    norm_num
  constructor
  · rw [source.information.historyReachProbability_eq_player_mul_counterfactual
      focalFalseOpponentTrue false chosenTrace,
      focal_false_player_reach_eq_zero]
    norm_num
  exact ⟨counterfactual_reach_eq_one,
    opponent_false_counterfactual_reach_eq_zero⟩

end Simultaneous

namespace TwoStep

open GameTheory.Tests.Randomized

abbrev execution := twice
abbrev information := model

def profile : (player : Unit) → information.BehavioralPolicy player
  | () => coinPolicy

def firstJoint :
    { joint : (player : Unit) → Option (execution.Action player) //
      execution.Legal execution.initHistory.state joint } :=
  ⟨fun _ => some .up, legal_of_not_stopped rfl .up⟩

theorem firstTransition :
    execution.step execution.initHistory.state firstJoint =
      FinDist.pure (.after .up) :=
  step_eq_pure .start rfl .up firstJoint.2

theorem firstRealized :
    Round.after .up ∈
      (execution.step execution.initHistory.state firstJoint).support := by
  rw [firstTransition]
  exact FinDist.mem_support_pure.mpr rfl

def firstTrace : execution.Trace (.after .up) :=
  execution.initHistory.trace.extend firstJoint.1 firstJoint.2 firstRealized

def secondJoint :
    { joint : (player : Unit) → Option (execution.Action player) //
      execution.Legal (.after .up) joint } :=
  ⟨fun _ => some .down, legal_of_not_stopped rfl .down⟩

theorem secondTransition :
    execution.step (.after .up) secondJoint =
      FinDist.pure (.done .up .down) :=
  step_eq_pure (.after .up) rfl .down secondJoint.2

theorem secondRealized :
    Round.done .up .down ∈
      (execution.step (.after .up) secondJoint).support := by
  rw [secondTransition]
  exact FinDist.mem_support_pure.mpr rfl

def fullTrace : execution.Trace (.done .up .down) :=
  firstTrace.extend secondJoint.1 secondJoint.2 secondRealized

theorem first_player_factor :
    information.playerStepProb profile () execution.initHistory.trace
      firstJoint = 1 / 2 := by
  classical
  unfold InformationModel.playerStepProb
  show (coinPolicy false).prob ⟨some .up, _⟩ = 1 / 2
  rw [show coinPolicy false = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure ⟨some .up, up_mem_menu⟩)
      (FinDist.pure ⟨some .down, down_mem_menu⟩) from rfl,
    FinDist.prob_mix]
  simp [FinDist.prob_pure_eq_ite]

theorem second_player_factor :
      information.playerStepProb profile () firstTrace secondJoint = 1 / 2 := by
  classical
  unfold InformationModel.playerStepProb
  show (coinPolicy false).prob ⟨some .down, _⟩ = 1 / 2
  rw [show coinPolicy false = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure ⟨some .up, up_mem_menu⟩)
      (FinDist.pure ⟨some .down, down_mem_menu⟩) from rfl,
    FinDist.prob_mix]
  simp [FinDist.prob_pure_eq_ite]
  norm_num

theorem first_counterfactual_factor :
    information.counterfactualStepProb profile ()
      execution.initHistory.trace firstJoint (.after .up) = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb, firstTransition,
    FinDist.prob_pure_self]
  simp [InformationModel.opponentsStepProb]

theorem second_counterfactual_factor :
    information.counterfactualStepProb profile () firstTrace secondJoint
      (.done .up .down) = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb, secondTransition,
    FinDist.prob_pure_self]
  simp [InformationModel.opponentsStepProb]

theorem first_player_reach :
    information.playerReachProbability profile () firstTrace = 1 / 2 := by
  simp only [firstTrace, InformationModel.playerReachProbability]
  have hstep (hlegal : execution.Legal execution.initHistory.state
      firstJoint.1) :
      information.playerStepProb profile () execution.initHistory.trace
        ⟨firstJoint.1, hlegal⟩ = 1 / 2 := by
    simpa only using first_player_factor
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

theorem first_counterfactual_reach :
    information.counterfactualReachProbability profile () firstTrace = 1 := by
  simp only [firstTrace, InformationModel.counterfactualReachProbability]
  have hstep (hlegal : execution.Legal execution.initHistory.state
      firstJoint.1) :
      information.counterfactualStepProb profile ()
        execution.initHistory.trace ⟨firstJoint.1, hlegal⟩ (.after .up) = 1 := by
    simpa only using first_counterfactual_factor
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

/-- Two independent consultations of the same information state multiply to
one quarter. Counterfactual reach excludes both focal factors and remains one. -/
theorem two_step_reach_values :
    information.playerReachProbability profile () fullTrace = 1 / 4 ∧
      information.counterfactualReachProbability profile () fullTrace = 1 := by
  constructor
  · simp only [fullTrace,
      InformationModel.playerReachProbability]
    have hsecond (hlegal : execution.Legal (.after .up) secondJoint.1) :
        information.playerStepProb profile () firstTrace
          ⟨secondJoint.1, hlegal⟩ = 1 / 2 := by
      simpa only using second_player_factor
    rw [hsecond, first_player_reach]
    norm_num
  · simp only [fullTrace,
      InformationModel.counterfactualReachProbability]
    have hsecond (hlegal : execution.Legal (.after .up) secondJoint.1) :
        information.counterfactualStepProb profile () firstTrace
          ⟨secondJoint.1, hlegal⟩ (.done .up .down) = 1 := by
      simpa only using second_counterfactual_factor
    rw [hsecond, first_counterfactual_reach]
    norm_num

/-- The recursive coefficients compute the existing canonical history law,
including a genuine two-step multiplication rather than a one-step alias. -/
theorem canonical_two_step_history_reach :
    information.historyReachProbability profile
      ⟨.done .up .down, fullTrace⟩ = 1 / 4 := by
  rw [information.historyReachProbability_eq_player_mul_counterfactual
    profile () fullTrace, two_step_reach_values.1,
    two_step_reach_values.2]
  norm_num

end TwoStep

end GameTheory.Analysis.Protocol.CounterfactualReachTest
