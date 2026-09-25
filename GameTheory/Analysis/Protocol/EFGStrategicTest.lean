/-
Nonconstant-payoff strategic-transfer probe.

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
open GameTheory.Math.Probability
open GameTheory.Tests.EFG

local instance : Fintype game.History := game.historyFintype

/-- The finite hidden-bit EFG has a genuinely enumerable contingent-plan
carrier once its local information and menu capabilities are supplied. -/
@[reducible]
noncomputable def finiteContingentPlans :
    Fintype (game.ContingentPlan .player) := by
  classical
  exact game.contingentPlanFintype .player

local instance : Fintype (game.ContingentPlan .player) :=
  finiteContingentPlans

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

/-- The finite EFG history carrier makes this nonconstant payoff integrable. -/
theorem preferFalse_integrable (law : PMF game.History) :
    UtilityIntegrable preferFalse .player law :=
  payoffIntegrable_of_finite _ _

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
      PMF.map
        (fun hidden => State.decision hidden execution.noop) fairCoin :=
  by
    have hjoint :=
      initial_legal_joint_eq_noop
        (information.historyChooser (fixedProfile action)
          execution.initHistory initial_not_terminal)
    show
      PMF.map
          (fun hidden =>
            State.decision hidden
              (information.historyChooser (fixedProfile action)
                execution.initHistory initial_not_terminal).1) fairCoin =
        PMF.map
          (fun hidden => State.decision hidden execution.noop) fairCoin
    simpa only using congrArg
      (fun joint =>
        PMF.map (fun hidden => State.decision hidden joint) fairCoin)
      hjoint

theorem runHistoryFor_one_decision_fixed (action hidden : Bool) :
    expect (execution.runHistoryFor
      (information.historyChooser (fixedProfile action)) 1
      (decisionHistory hidden))
        (fun history => preferFalse history .player)
        (payoffIntegrable_of_finite _ _) =
      (if action = false then 1 else 0) := by
  rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
    _ 0 (decision_not_terminal hidden)]
  simp [execution, decisionHistory, preferFalse, expect_pure]

theorem fixed_value (action : Bool) :
    expectedUtility preferFalse .player
      (information.run (fixedProfile action) 2)
        (preferFalse_integrable _) =
        (if action = false then 1 else 0) := by
  let joint := information.historyChooser (fixedProfile action)
    execution.initHistory initial_not_terminal
  let stepLaw := execution.step execution.initHistory.state joint
  let continuation : ∀ state, state ∈ stepLaw.support → PMF game.History :=
    fun state realized => execution.runHistoryFor
      (information.historyChooser (fixedProfile action)) 1
      (execution.initHistory.extend joint.2 realized)
  have hlaw : information.run (fixedProfile action) 2 =
      stepLaw.bindOnSupport continuation := by
    unfold InformationModel.run InformationModel.runFrom
    rw [ExecutionProtocol.runHistoryFor_succ_of_not_terminal
      _ 1 initial_not_terminal]
  let payoff := fun history : game.History => preferFalse history .player
  let value : ℝ := if action = false then 1 else 0
  have hbranch (state : State) (hstate : state ∈ stepLaw.support)
      (h : PayoffIntegrable (continuation state hstate) payoff) :
      expect (continuation state hstate) payoff h = value := by
    have hmapped : state ∈
        (PMF.map (fun hidden => State.decision hidden execution.noop)
          fairCoin).support := by
      rw [← step_historyChooser_initial action]
      exact hstate
    rw [PMF.support_map] at hmapped
    rcases hmapped with ⟨hidden, _hhidden, hstateEq⟩
    subst state
    have hhistory :
        execution.initHistory.extend joint.2 hstate =
          decisionHistory hidden := by
      congr 1
    have hvalue := runHistoryFor_one_decision_fixed action hidden
    simpa only [continuation, payoff, value, hhistory] using hvalue
  calc
    expectedUtility preferFalse .player
        (information.run (fixedProfile action) 2)
          (preferFalse_integrable _) =
      expect (stepLaw.bindOnSupport continuation) payoff
        (payoffIntegrable_of_finite _ _) := by
        exact expectedUtility_congr_law preferFalse .player hlaw
          (preferFalse_integrable _) (payoffIntegrable_of_finite _ _)
    _ = expect stepLaw (fun _ => value)
          (payoffIntegrable_bindOnSupport_conditionalValue_on_support
            stepLaw continuation payoff (payoffIntegrable_of_finite _ _)
            (fun _ => value) (fun state hstate =>
              (hbranch state hstate _).symm)) := by
        exact expect_bindOnSupport_tower_on_support stepLaw continuation
          payoff (payoffIntegrable_of_finite _ _) (fun _ => value)
          (fun state hstate => (hbranch state hstate _).symm)
    _ = value := expect_constant stepLaw value _

theorem fixedFalse_value :
    expectedUtility preferFalse .player
      (information.run (fixedProfile false) 2)
        (preferFalse_integrable _) = 1 := by
  simpa using fixed_value false

theorem fixedTrue_value :
    expectedUtility preferFalse .player
      (information.run (fixedProfile true) 2)
        (preferFalse_integrable _) = 0 := by
  simpa using fixed_value true

theorem anyPlan_value_le_one (profile : Profile game.strategicSignature) :
    expectedUtility preferFalse .player
      (information.run profile 2) (preferFalse_integrable _) ≤ 1 := by
  unfold expectedUtility
  calc
    expect (information.run profile 2)
        (fun history => preferFalse history .player)
        (preferFalse_integrable _) ≤
      expect (information.run profile 2) (fun _history => 1)
        (payoffIntegrable_constant _ 1) := by
        apply expect_mono
        intro history _
        rcases history with ⟨state, trace⟩
        cases state <;> simp [preferFalse]
        split <;> norm_num
    _ = 1 := expect_constant _ 1 _

theorem fixedFalse_isNash :
    IsNash (game.toGameForm 2) (euPreference preferFalse)
      (fixedProfile false) := by
  rw [game.isNash_toGameForm_iff]
  intro who replacement
  cases who
  refine ⟨preferFalse_integrable _, preferFalse_integrable _, ?_⟩
  calc
    expectedUtility preferFalse .player
        (information.run
          (Profile.update (fixedProfile false) .player replacement) 2)
          (preferFalse_integrable _) ≤ 1 :=
      anyPlan_value_le_one _
    _ = expectedUtility preferFalse .player
        (information.run (fixedProfile false) 2)
          (preferFalse_integrable _) :=
      fixedFalse_value.symm

def halfMixedProfile : Profile game.strategicSignature.mixed :=
  fun who => by
    cases who
    exact
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (fixedPolicy false))
        (PMF.pure (fixedPolicy true))

theorem fixedMixedDeviation_value (action : Bool) :
    expectedUtility preferFalse .player
        ((game.toGameForm 2).mixed.play
          (Profile.update halfMixedProfile .player
            (PMF.pure (fixedPolicy action))))
          (preferFalse_integrable _) =
      (if action = false then 1 else 0) := by
  have hprofile :
      Profile.update halfMixedProfile .player
          (PMF.pure (fixedPolicy action)) =
        (game.toGameForm 2).purify (fixedProfile action) := by
    funext who
    cases who
    rw [Profile.update_same]
    rfl
  rw [hprofile, GameForm.mixed_play_purify, game.toGameForm_play]
  exact fixed_value action

theorem halfMixed_value :
    expectedUtility preferFalse .player
      (information.runMixed halfMixedProfile 2)
        (preferFalse_integrable _) = 1 / 2 := by
  rw [← game.toGameForm_mixed_play]
  let payoff := fun policy : game.ContingentPlan .player =>
    expectedUtility preferFalse .player
      ((game.toGameForm 2).mixed.play
        (Profile.update halfMixedProfile .player (PMF.pure policy)))
      (preferFalse_integrable _)
  have htower : expectedUtility preferFalse .player
      ((game.toGameForm 2).mixed.play halfMixedProfile)
        (preferFalse_integrable _) =
      expect (halfMixedProfile .player) payoff
        (payoffIntegrable_of_finite _ _) := by
    simpa only [payoff] using
      (expectedUtility_mixed_eq_expect (game.toGameForm 2)
        preferFalse halfMixedProfile .player
        (preferFalse_integrable _)
        (fun _ => preferFalse_integrable _))
  calc
    expectedUtility preferFalse .player
        ((game.toGameForm 2).mixed.play halfMixedProfile)
          (preferFalse_integrable _) =
      expect (halfMixedProfile .player) payoff
        (payoffIntegrable_of_finite _ _) := htower
    _ = 1 / 2 := by
      have hmix := expect_mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (fixedPolicy false)) (PMF.pure (fixedPolicy true)) payoff
        (payoffIntegrable_pure _ payoff) (payoffIntegrable_pure _ payoff)
      have hsplit :
          expect (halfMixedProfile .player) payoff
              (payoffIntegrable_of_finite _ _) =
            1 / 2 * payoff (fixedPolicy false) +
              (1 - 1 / 2) * payoff (fixedPolicy true) := by
        simpa only [halfMixedProfile, expect_pure] using hmix
      rw [hsplit, show payoff (fixedPolicy false) = 1 from
        fixedMixedDeviation_value false,
        show payoff (fixedPolicy true) = 0 from
          fixedMixedDeviation_value true]
      norm_num

theorem fixedFalseMixedDeviation_value :
    expectedUtility preferFalse .player
      (information.runMixed
        (Profile.update halfMixedProfile .player
          (PMF.pure (fixedPolicy false))) 2)
        (preferFalse_integrable _) = 1 := by
  rw [← game.toGameForm_mixed_play]
  simpa using fixedMixedDeviation_value false

theorem halfMixed_not_isNash :
    ¬ IsNash (game.toGameForm 2).mixed (euPreference preferFalse)
      halfMixedProfile := by
  rw [game.isNash_mixed_toGameForm_iff]
  intro hnash
  obtain ⟨_, _, hdeviation⟩ :=
    hnash .player (PMF.pure (fixedPolicy false))
  rw [fixedFalseMixedDeviation_value, halfMixed_value] at hdeviation
  norm_num at hdeviation

end GameTheory.Tests.EFGStrategic
