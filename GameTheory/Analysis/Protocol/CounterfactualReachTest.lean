/-
# Counterfactual-reach consumers

The one-shot simultaneous fixture separates focal, opponent, and actual reach.
The two-step fixture checks that recursive reach multiplies across an actual
canonical trace rather than passing only at the final step.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Languages.FOSG
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualReachTest

open GameTheory.Languages GameTheory.Math.Probability GameTheory.Protocol

namespace Simultaneous

inductive SourceState | initial | finished (actions : Bool → Bool)

@[reducible] def sourceExecution : ExecutionProtocol Bool where
  State := SourceState
  Action _ := Bool
  init := .initial
  active _ _ := True
  available _ _ := Set.univ
  terminal state := match state with | .initial => False | .finished _ => True
  step state joint := match state with
    | .initial => PMF.pure (.finished fun i => (joint.1 i).getD false)
    | .finished _ => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | initial =>
        exact ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    | finished actions => exact False.elim (hterm trivial)

@[reducible] def sourceSignals : InfoSignals sourceExecution where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

def sourceMenu (_ : Unit) : Set (Option Bool) := {some false, some true}

@[reducible] def sourceInformation : InformationModel sourceExecution where
  toInfoSignals := sourceSignals
  menu _ := sourceMenu
  menu_adequate := by
    intro who state trace choice
    cases choice with
    | none => simp [sourceMenu, LegalOption, sourceExecution]
    | some action => simp [sourceMenu, LegalOption, sourceExecution]

abbrev source : GameTheory.Languages.FOSG.Game Bool :=
  ⟨sourceExecution, sourceInformation⟩

def actionPolicy (who action : Bool) :
    sourceInformation.BehavioralPolicy who := fun _ =>
  PMF.pure ⟨some action, by simp [sourceMenu]⟩

def focalTrueOpponentTrue :
    (player : Bool) → sourceInformation.BehavioralPolicy player
  | false => actionPolicy false true
  | true => actionPolicy true true

def focalFalseOpponentTrue :
    (player : Bool) → sourceInformation.BehavioralPolicy player
  | false => actionPolicy false false
  | true => actionPolicy true true

def focalTrueOpponentFalse :
    (player : Bool) → sourceInformation.BehavioralPolicy player
  | false => actionPolicy false true
  | true => actionPolicy true false

theorem profiles_eq_off_focal (other : Bool) (hne : other ≠ false) :
    focalTrueOpponentTrue other = focalFalseOpponentTrue other := by
  cases other
  · exact False.elim (hne rfl)
  · rfl

def chosenJoint :
    { joint : (player : Bool) → Option (sourceExecution.Action player) //
    sourceExecution.Legal sourceExecution.initHistory.state joint } :=
  ⟨fun _ => some true,
    ExecutionProtocol.legal_of_legalOption (by
      simp [sourceExecution, ExecutionProtocol.initHistory])
      (fun _ => ⟨trivial, Set.mem_univ _⟩)⟩

def target : sourceExecution.State :=
  .finished (fun _ => true)

theorem chosenJoint_transition :
    sourceExecution.step sourceExecution.initHistory.state chosenJoint =
      PMF.pure target := by
  rfl

theorem targetRealized :
    target ∈ (sourceExecution.step sourceExecution.initHistory.state
      chosenJoint).support := by
  rw [chosenJoint_transition]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def chosenTrace : sourceExecution.Trace target :=
  sourceExecution.initHistory.trace.extend chosenJoint.1 chosenJoint.2
    targetRealized

theorem focal_true_player_factor :
    sourceInformation.playerStepProb focalTrueOpponentTrue false
      sourceExecution.initHistory.trace chosenJoint = 1 := by
  classical
  rw [InformationModel.playerStepProb]
  simp only [focalTrueOpponentTrue, actionPolicy]
  have hchoice :
      (⟨some true, by simp [sourceMenu]⟩ : sourceInformation.Choice false
        (sourceInformation.infoOf false sourceExecution.initHistory.trace)) =
        sourceInformation.choicesOfLegal sourceExecution.initHistory.trace
          chosenJoint false := by
    apply Subtype.ext
    rfl
  rw [← hchoice, PMF.pure_apply_self]
  simp

theorem focal_false_player_factor :
    sourceInformation.playerStepProb focalFalseOpponentTrue false
      sourceExecution.initHistory.trace chosenJoint = 0 := by
  classical
  rw [InformationModel.playerStepProb]
  simp only [focalFalseOpponentTrue, actionPolicy]
  have hval :
      (sourceInformation.choicesOfLegal sourceExecution.initHistory.trace
        chosenJoint false).1 ≠ some false := by
    simp [InformationModel.choicesOfLegal, chosenJoint]
  rw [PMF.pure_apply]
  simp only [Subtype.ext_iff]
  rw [ite_eq_right hval]
  simp

theorem counterfactual_factor_eq_one :
    sourceInformation.counterfactualStepProb
      focalTrueOpponentTrue false sourceExecution.initHistory.trace
      chosenJoint target = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb,
    InformationModel.opponentsStepProb,
    show Finset.univ.erase false = {true} by decide,
    Finset.prod_singleton, chosenJoint_transition]
  norm_num [InformationModel.choicesOfLegal, focalTrueOpponentTrue,
    actionPolicy, chosenJoint, source, sourceInformation, sourceMenu,
    InfoSignals.infoOf, sourceSignals, sourceExecution, target,
    ExecutionProtocol.initHistory, PMF.pure_apply]

theorem opponent_false_counterfactual_factor_eq_zero :
    sourceInformation.counterfactualStepProb
      focalTrueOpponentFalse false sourceExecution.initHistory.trace
      chosenJoint target = 0 := by
  classical
  rw [InformationModel.counterfactualStepProb,
    InformationModel.opponentsStepProb,
    show Finset.univ.erase false = {true} by decide,
    Finset.prod_singleton, chosenJoint_transition]
  norm_num [InformationModel.choicesOfLegal, focalTrueOpponentFalse,
    actionPolicy, chosenJoint, source, sourceInformation, sourceMenu,
    InfoSignals.infoOf, sourceSignals, sourceExecution, target,
    ExecutionProtocol.initHistory, PMF.pure_apply, Subtype.ext_iff]

theorem counterfactual_ignores_focal_change :
    sourceInformation.counterfactualReachProbability
        focalTrueOpponentTrue false chosenTrace =
      sourceInformation.counterfactualReachProbability
        focalFalseOpponentTrue false chosenTrace :=
  sourceInformation.counterfactualReachProbability_eq_of_eq_off
    profiles_eq_off_focal chosenTrace

theorem focal_true_player_reach_eq_one :
    sourceInformation.playerReachProbability
      focalTrueOpponentTrue false chosenTrace = 1 := by
  simp only [chosenTrace, InformationModel.playerReachProbability]
  have hstep (hlegal : sourceExecution.Legal
      sourceExecution.initHistory.state chosenJoint.1) :
      sourceInformation.playerStepProb focalTrueOpponentTrue false
        sourceExecution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ = 1 := by
    simpa only using focal_true_player_factor
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

theorem focal_false_player_reach_eq_zero :
    sourceInformation.playerReachProbability
      focalFalseOpponentTrue false chosenTrace = 0 := by
  simp only [chosenTrace, InformationModel.playerReachProbability]
  have hstep (hlegal : sourceExecution.Legal
      sourceExecution.initHistory.state chosenJoint.1) :
      sourceInformation.playerStepProb focalFalseOpponentTrue false
        sourceExecution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ = 0 := by
    simpa only using focal_false_player_factor
  rw [hstep]
  ring

theorem counterfactual_reach_eq_one :
    sourceInformation.counterfactualReachProbability
      focalTrueOpponentTrue false chosenTrace = 1 := by
  simp only [chosenTrace, InformationModel.counterfactualReachProbability]
  have hstep (hlegal : sourceExecution.Legal
      sourceExecution.initHistory.state chosenJoint.1) :
      sourceInformation.counterfactualStepProb focalTrueOpponentTrue false
        sourceExecution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ target = 1 := by
    simpa only using counterfactual_factor_eq_one
  rw [hstep]
  simp [ExecutionProtocol.initHistory]

theorem opponent_false_counterfactual_reach_eq_zero :
    sourceInformation.counterfactualReachProbability
      focalTrueOpponentFalse false chosenTrace = 0 := by
  simp only [chosenTrace, InformationModel.counterfactualReachProbability]
  have hstep (hlegal : sourceExecution.Legal
      sourceExecution.initHistory.state chosenJoint.1) :
      sourceInformation.counterfactualStepProb focalTrueOpponentFalse false
        sourceExecution.initHistory.trace
          ⟨chosenJoint.1, hlegal⟩ target = 0 := by
    simpa only using opponent_false_counterfactual_factor_eq_zero
  rw [hstep]
  ring

theorem canonical_history_reach_factors :
    (sourceInformation.historyReachWeight focalTrueOpponentTrue
        ⟨target, chosenTrace⟩).toReal = 1 ∧
      (sourceInformation.historyReachWeight focalFalseOpponentTrue
        ⟨target, chosenTrace⟩).toReal = 0 ∧
      sourceInformation.counterfactualReachProbability
        focalTrueOpponentTrue false chosenTrace = 1 ∧
      sourceInformation.counterfactualReachProbability
        focalTrueOpponentFalse false chosenTrace = 0 := by
  constructor
  · rw [sourceInformation.historyReachProbability_eq_player_mul_counterfactual
      focalTrueOpponentTrue false chosenTrace,
      focal_true_player_reach_eq_one, counterfactual_reach_eq_one]
    norm_num
  constructor
  · rw [sourceInformation.historyReachProbability_eq_player_mul_counterfactual
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
      PMF.pure (.after .up) :=
  step_eq_pure .start rfl .up firstJoint.2

theorem firstRealized :
    Round.after .up ∈
      (execution.step execution.initHistory.state firstJoint).support := by
  rw [firstTransition]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def firstTrace : execution.Trace (.after .up) :=
  execution.initHistory.trace.extend firstJoint.1 firstJoint.2 firstRealized

def secondJoint :
    { joint : (player : Unit) → Option (execution.Action player) //
      execution.Legal (.after .up) joint } :=
  ⟨fun _ => some .down, legal_of_not_stopped rfl .down⟩

theorem secondTransition :
    execution.step (.after .up) secondJoint =
      PMF.pure (.done .up .down) :=
  step_eq_pure (.after .up) rfl .down secondJoint.2

theorem secondRealized :
    Round.done .up .down ∈
      (execution.step (.after .up) secondJoint).support := by
  rw [secondTransition]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def fullTrace : execution.Trace (.done .up .down) :=
  firstTrace.extend secondJoint.1 secondJoint.2 secondRealized

set_option backward.isDefEq.respectTransparency false in
theorem first_player_factor :
    information.playerStepProb profile () execution.initHistory.trace
      firstJoint = 1 / 2 := by
  classical
  unfold InformationModel.playerStepProb
  show ((coinPolicy false) ⟨some .up, up_mem_menu⟩).toReal = 1 / 2
  rw [show coinPolicy false = mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure ⟨some .up, up_mem_menu⟩)
      (PMF.pure ⟨some .down, down_mem_menu⟩) from rfl,
    mix_apply]
  norm_num [PMF.pure_apply]

set_option backward.isDefEq.respectTransparency false in
theorem second_player_factor :
      information.playerStepProb profile () firstTrace secondJoint = 1 / 2 := by
  classical
  unfold InformationModel.playerStepProb
  show ((coinPolicy false) ⟨some .down, down_mem_menu⟩).toReal = 1 / 2
  rw [show coinPolicy false = mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure ⟨some .up, up_mem_menu⟩)
      (PMF.pure ⟨some .down, down_mem_menu⟩) from rfl,
    mix_apply]
  norm_num [PMF.pure_apply]

theorem first_counterfactual_factor :
    information.counterfactualStepProb profile ()
      execution.initHistory.trace firstJoint (.after .up) = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb, firstTransition,
    PMF.pure_apply_self]
  simp [InformationModel.opponentsStepProb]

theorem second_counterfactual_factor :
    information.counterfactualStepProb profile () firstTrace secondJoint
      (.done .up .down) = 1 := by
  classical
  rw [InformationModel.counterfactualStepProb, secondTransition,
    PMF.pure_apply_self]
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
    (information.historyReachWeight profile ⟨.done .up .down, fullTrace⟩).toReal =
      1 / 4 := by
  rw [information.historyReachProbability_eq_player_mul_counterfactual
    profile () fullTrace, two_step_reach_values.1,
    two_step_reach_values.2]
  norm_num

end TwoStep

end GameTheory.Analysis.Protocol.CounterfactualReachTest
