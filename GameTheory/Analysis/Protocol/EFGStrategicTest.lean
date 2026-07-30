/-
Hostile T1 strategic-transfer probe.

The existing finite EFG hides a fair Boolean state and then lets one player
choose without observing it. Here a pure contingent plan always chooses
`false`, and terminal utility rewards exactly that action. The plan is Nash,
while a genuinely mixed profile that sometimes chooses `true` is not. Both
claims pass through the EFG-facing pure/mixed iff theorems.
-/

import GameTheory.Languages.EFG.Strategic
import GameTheory.Analysis.Protocol.EFGTest
import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory.Tests.EFGStrategic

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Probability
open GameTheory.Tests.EFG

/-- The finite hidden-bit EFG has a genuinely enumerable contingent-plan
carrier once its local information and menu capabilities are supplied. -/
@[reducible]
noncomputable def finiteContingentPlans :
    Fintype (game.ContingentPlan .player) := by
  classical
  exact game.contingentPlanFintype .player

/-- Choose one fixed Boolean at the only decision information state. -/
def fixedPolicy (action : Bool) : information.Policy .player
  | .waiting => ⟨none, by simp⟩
  | .acting => ⟨some action, by simp⟩
  | .done => ⟨none, by simp⟩

def fixedProfile (action : Bool) :
    Profile game.strategicSignature :=
  fun who => by
    cases who
    exact fixedPolicy action

/-- A nonconstant terminal payoff: choosing `false` pays one and choosing
`true` pays zero, independently of nature's hidden bit. -/
def preferFalse (history : game.History) (_who : Player) : ℝ :=
  match history.state with
  | .terminal _hidden _arrival action =>
      if action .player = some false then 1 else 0
  | _ => 0

@[simp]
theorem historyChooser_decision_fixed (action hidden : Bool) :
    (information.historyChooser (fixedProfile action)
      (decisionHistory hidden) (decision_not_terminal hidden)).1 .player =
        some action := by
  show
    (fixedPolicy action).act
        (information.infoOf .player (decisionHistory hidden).trace) =
      some action
  rw [infoOf_decisionHistory]
  rfl

theorem step_historyChooser_initial (action : Bool) :
    execution.step execution.initHistory.state
        (information.historyChooser (fixedProfile action)
          execution.initHistory initial_not_terminal) =
      FinDist.map
        (fun hidden => State.decision hidden execution.noop) fairCoin :=
  by
    have hjoint :=
      initial_legal_joint_eq_noop
        (information.historyChooser (fixedProfile action)
          execution.initHistory initial_not_terminal)
    show
      FinDist.map
          (fun hidden =>
            State.decision hidden
              (information.historyChooser (fixedProfile action)
                execution.initHistory initial_not_terminal).1) fairCoin =
        FinDist.map
          (fun hidden => State.decision hidden execution.noop) fairCoin
    simpa only using congrArg
      (fun joint =>
        FinDist.map (fun hidden => State.decision hidden joint) fairCoin)
      hjoint

theorem runHistoryFor_one_decision_fixed (action hidden : Bool) :
    (execution.runHistoryFor
      (information.historyChooser (fixedProfile action)) 1
      (decisionHistory hidden)).expect
        (fun history => preferFalse history .player) =
      (if action = false then 1 else 0) := by
  rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
    _ 0 (decision_not_terminal hidden)]
  simp [execution, decisionHistory, preferFalse]
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    InformationModel.Policy.act, fixedProfile]
  have hchoice :
      ↑(fixedPolicy action
        (signals.infoOf .player (decisionTrace hidden))) = some action := by
    exact historyChooser_decision_fixed action hidden
  simp [hchoice]

theorem fixed_value (action : Bool) :
    expectedUtility preferFalse .player
      (information.run (fixedProfile action) 2) =
        (if action = false then 1 else 0) := by
  unfold expectedUtility InformationModel.run InformationModel.runFrom
  rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
    _ 1 initial_not_terminal]
  calc
    _ = ((execution.step execution.initHistory.state
          (information.historyChooser (fixedProfile action)
            execution.initHistory initial_not_terminal)).bindOnSupport
          fun _state _hstate => FinDist.pure ()).expect
            (fun _unit => if action = false then 1 else 0) := by
        apply FinDist.expect_bindOnSupport_congr
        intro state hstate
        have hmapped :
            state ∈
              (FinDist.map
                (fun hidden => State.decision hidden execution.noop)
                fairCoin).support := by
          rw [← step_historyChooser_initial action]
          exact hstate
        rw [FinDist.support_map] at hmapped
        rcases hmapped with ⟨hidden, _hhidden, hstateEq⟩
        subst state
        have hhistory :
            execution.initHistory.extend
                (information.historyChooser (fixedProfile action)
                  execution.initHistory initial_not_terminal).2 hstate =
              decisionHistory hidden := by
          congr 1
        rw [hhistory, runHistoryFor_one_decision_fixed action hidden]
        exact
          (FinDist.expect_pure ()
            (fun _unit => if action = false then 1 else 0)).symm
    _ = (if action = false then 1 else 0) := by
      rw [FinDist.bindOnSupport_eq_bind]
      exact FinDist.expect_const ..

theorem fixedFalse_value :
    expectedUtility preferFalse .player
      (information.run (fixedProfile false) 2) = 1 := by
  simpa using fixed_value false

theorem fixedTrue_value :
    expectedUtility preferFalse .player
      (information.run (fixedProfile true) 2) = 0 := by
  simpa using fixed_value true

theorem anyPlan_value_le_one (profile : Profile game.strategicSignature) :
    expectedUtility preferFalse .player
      (information.run profile 2) ≤ 1 := by
  unfold expectedUtility
  calc
    (information.run profile 2).expect
        (fun history => preferFalse history .player) ≤
      (information.run profile 2).expect (fun _history => 1) := by
        apply FinDist.expect_mono
        intro history _
        rcases history with ⟨state, trace⟩
        cases state <;> simp [preferFalse]
        split <;> norm_num
    _ = 1 := FinDist.expect_const ..

theorem fixedFalse_isNash :
    IsNash (game.toGameForm 2) (euPreference preferFalse)
      (fixedProfile false) := by
  rw [game.isNash_toGameForm_iff]
  intro who replacement
  cases who
  calc
    expectedUtility preferFalse .player
        (information.run
          (Profile.update (fixedProfile false) .player replacement) 2) ≤ 1 :=
      anyPlan_value_le_one _
    _ = expectedUtility preferFalse .player
        (information.run (fixedProfile false) 2) :=
      fixedFalse_value.symm

def halfMixedProfile : Profile game.strategicSignature.mixed :=
  fun who => by
    cases who
    exact
      FinDist.mix (1 / 2) (by norm_num) (by norm_num)
        (FinDist.pure (fixedPolicy false))
        (FinDist.pure (fixedPolicy true))

theorem fixedMixedDeviation_value (action : Bool) :
    expectedUtility preferFalse .player
        ((game.toGameForm 2).mixed.play
          (Profile.update halfMixedProfile .player
            (FinDist.pure (fixedPolicy action)))) =
      (if action = false then 1 else 0) := by
  have hprofile :
      Profile.update halfMixedProfile .player
          (FinDist.pure (fixedPolicy action)) =
        (game.toGameForm 2).purify (fixedProfile action) := by
    funext who
    cases who
    rw [Profile.update_same]
    rfl
  rw [hprofile, GameForm.mixed_play_purify, game.toGameForm_play]
  exact fixed_value action

theorem halfMixed_value :
    expectedUtility preferFalse .player
      (information.runMixed halfMixedProfile 2) = 1 / 2 := by
  rw [← game.toGameForm_mixed_play]
  calc
    expectedUtility preferFalse .player
        ((game.toGameForm 2).mixed.play halfMixedProfile) =
      (halfMixedProfile .player).expect fun policy =>
        expectedUtility preferFalse .player
          ((game.toGameForm 2).mixed.play
            (Profile.update halfMixedProfile .player
              (FinDist.pure policy))) :=
      expectedUtility_mixed_eq_expect
        (game.toGameForm 2) preferFalse halfMixedProfile .player
    _ = 1 / 2 := by
      show
        (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
          (FinDist.pure (fixedPolicy false))
          (FinDist.pure (fixedPolicy true))).expect
            (fun policy =>
              expectedUtility preferFalse .player
                ((game.toGameForm 2).mixed.play
                  (Profile.update halfMixedProfile .player
                    (FinDist.pure policy)))) = 1 / 2
      rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
        fixedMixedDeviation_value, fixedMixedDeviation_value]
      norm_num

theorem fixedFalseMixedDeviation_value :
    expectedUtility preferFalse .player
      (information.runMixed
        (Profile.update halfMixedProfile .player
          (FinDist.pure (fixedPolicy false))) 2) = 1 := by
  rw [← game.toGameForm_mixed_play]
  simpa using fixedMixedDeviation_value false

theorem halfMixed_not_isNash :
    ¬ IsNash (game.toGameForm 2).mixed (euPreference preferFalse)
      halfMixedProfile := by
  rw [game.isNash_mixed_toGameForm_iff]
  intro hnash
  have hdeviation := hnash .player (FinDist.pure (fixedPolicy false))
  rw [fixedFalseMixedDeviation_value, halfMixed_value] at hdeviation
  norm_num at hdeviation

end GameTheory.Tests.EFGStrategic
