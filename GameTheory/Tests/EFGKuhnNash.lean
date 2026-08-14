/-
# Unilateral Kuhn and Nash-transfer witness

Two players move sequentially and the terminal history records both Boolean
actions.  Public state information gives perfect recall.  The fixture keeps a
genuine nondeviator in the law when the other player's strategy is converted,
then attaches coordination utility for the Nash-transfer consumer.
-/

import GameTheory.Languages.EFG.Kuhn

noncomputable section

namespace GameTheory.Tests.EFGKuhnNash

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol

abbrev Player := Bool

inductive State
  | first
  | second (firstAction : Bool)
  | done (firstAction secondAction : Bool)
  deriving DecidableEq, Fintype

def jointAt (who action : Bool) : Bool → Option Bool :=
  fun player => if player = who then some action else none

@[reducible]
def execution : ExecutionProtocol Player where
  State := State
  Action _ := Bool
  init := .first
  active state who :=
    match state with
    | .first => who = false
    | .second _ => who = true
    | .done _ _ => False
  available _ _ := Set.univ
  terminal
    | .done _ _ => True
    | _ => False
  step state joint :=
    match state with
    | .first => FinDist.pure (.second ((joint.1 false).getD false))
    | .second firstAction =>
        FinDist.pure (.done firstAction ((joint.1 true).getD false))
    | .done firstAction secondAction =>
        FinDist.pure (.done firstAction secondAction)
  progress := by
    intro state hterm
    cases state with
    | first =>
        refine ⟨jointAt false false, ?_⟩
        intro who
        cases who <;> simp [jointAt]
    | second firstAction =>
        refine ⟨jointAt true false, ?_⟩
        intro who
        cases who <;> simp [jointAt]
    | done firstAction secondAction =>
        exact False.elim (hterm trivial)

theorem first_not_terminal : ¬ execution.terminal .first := by simp

theorem second_not_terminal (firstAction : Bool) :
    ¬ execution.terminal (.second firstAction) := by simp

theorem jointAt_legal_first (action : Bool) :
    execution.Legal .first (jointAt false action) := by
  refine execution.legal_of_legalOption first_not_terminal ?_
  intro who
  cases who <;> simp [execution, LegalOption, jointAt]

theorem jointAt_legal_second (firstAction action : Bool) :
    execution.Legal (.second firstAction) (jointAt true action) := by
  refine execution.legal_of_legalOption (second_not_terminal firstAction) ?_
  intro who
  cases who <;> simp [execution, LegalOption, jointAt]

theorem legal_first_eq_jointAt {joint : Bool → Option Bool}
    (isLegal : execution.Legal .first joint) :
    ∃ action, joint = jointAt false action := by
  obtain ⟨action, haction⟩ :=
    LegalOption.exists_eq_some_of_active (joint false)
      (execution.legalOption_of_legal isLegal false)
      (show execution.active .first false from rfl)
  refine ⟨action, funext fun who => ?_⟩
  cases who
  · exact haction
  · exact LegalOption.eq_none_of_inactive
      (E := execution) (state := .first) (i := true) (joint true)
      (execution.legalOption_of_legal isLegal true) (by
        intro hactive
        cases hactive)

theorem legal_second_eq_jointAt {firstAction : Bool}
    {joint : Bool → Option Bool}
    (isLegal : execution.Legal (.second firstAction) joint) :
    ∃ action, joint = jointAt true action := by
  obtain ⟨action, haction⟩ :=
    LegalOption.exists_eq_some_of_active (joint true)
      (execution.legalOption_of_legal isLegal true)
      (show execution.active (.second firstAction) true from rfl)
  refine ⟨action, funext fun who => ?_⟩
  cases who
  · exact LegalOption.eq_none_of_inactive
      (E := execution) (state := .second firstAction) (i := false)
      (joint false) (execution.legalOption_of_legal isLegal false) (by
        intro hactive
        cases hactive)
  · exact haction

theorem init_not_mem_step (source : State)
    (joint : Bool → Option Bool) (isLegal : execution.Legal source joint) :
    State.first ∉ (execution.step source ⟨joint, isLegal⟩).support := by
  cases source with
  | first => simp
  | second firstAction => simp
  | done firstAction secondAction => exact False.elim (isLegal.1 trivial)

theorem step_predecessor_unique
    {target firstSource secondSource : State}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : execution.Legal firstSource firstJoint)
    (secondLegal : execution.Legal secondSource secondJoint)
    (firstRealized :
      target ∈ (execution.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized :
      target ∈ (execution.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  cases firstSource with
  | first =>
      obtain ⟨firstAction, hfirst⟩ := legal_first_eq_jointAt firstLegal
      subst firstJoint
      rw [FinDist.mem_support_pure] at firstRealized
      subst target
      cases secondSource with
      | first =>
          obtain ⟨secondAction, hsecond⟩ := legal_first_eq_jointAt secondLegal
          subst secondJoint
          rw [FinDist.mem_support_pure] at secondRealized
          simp [jointAt] at secondRealized
          subst secondAction
          exact ⟨rfl, rfl⟩
      | second secondFirst =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | done secondFirst secondSecond =>
          exact False.elim (secondLegal.1 trivial)
  | second firstAction =>
      obtain ⟨firstSecond, hfirst⟩ := legal_second_eq_jointAt firstLegal
      subst firstJoint
      rw [FinDist.mem_support_pure] at firstRealized
      subst target
      cases secondSource with
      | first =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | second secondFirst =>
          obtain ⟨secondSecond, hsecond⟩ := legal_second_eq_jointAt secondLegal
          subst secondJoint
          rw [FinDist.mem_support_pure] at secondRealized
          simp [jointAt] at secondRealized
          obtain ⟨rfl, rfl⟩ := secondRealized
          exact ⟨rfl, rfl⟩
      | done secondFirst secondSecond =>
          exact False.elim (secondLegal.1 trivial)
  | done firstAction secondAction =>
      exact False.elim (firstLegal.1 trivial)

theorem treeShaped : execution.IsTreeShaped :=
  execution.isTreeShaped_of_predecessor_unique init_not_mem_step
    (fun firstLegal secondLegal firstRealized secondRealized =>
      step_predecessor_unique firstLegal secondLegal
        firstRealized secondRealized)

theorem history_eq_of_state_eq {first second : execution.History}
    (hstate : first.state = second.state) : first = second := by
  rcases first with ⟨state, firstTrace⟩
  rcases second with ⟨_, secondTrace⟩
  simp only at hstate
  subst hstate
  congr
  exact (treeShaped state).elim firstTrace secondTrace

@[reducible]
def signals : InfoSignals execution where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .first
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

theorem infoOf_eq_state (who : Player) :
    ∀ {state : State} (trace : Trace execution state),
      signals.infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible]
def information : InformationModel execution where
  toInfoSignals := signals
  menu who state := {choice | LegalOption execution state who choice}
  menu_adequate := by
    intro who state trace choice
    rw [infoOf_eq_state who trace]
    exact Iff.rfl

theorem perfectRecall : information.PerfectRecall := by
  intro who firstState secondState firstTrace secondTrace hinfo
  rw [infoOf_eq_state who firstTrace, infoOf_eq_state who secondTrace] at hinfo
  subst secondState
  have htrace := (treeShaped firstState).elim firstTrace secondTrace
  subst secondTrace
  rfl

theorem singleMover (state : State) {first second : Player}
    (hfirst : execution.active state first)
    (hsecond : execution.active state second) : first = second := by
  cases state with
  | first =>
      simp at hfirst hsecond
      exact hfirst.trans hsecond.symm
  | second firstAction =>
      simp at hfirst hsecond
      exact hfirst.trans hsecond.symm
  | done firstAction secondAction =>
      simp at hfirst

@[reducible]
def game : Languages.EFG.Game Player where
  execution := execution
  information := information
  treeShaped := treeShaped
  singleMover := singleMover

def purePolicy (action : Bool) (who : Player) : information.Policy who :=
  by
    classical
    exact fun state =>
      if hactive : execution.active state who then
        ⟨some action, hactive, Set.mem_univ action⟩
      else
        ⟨none, hactive⟩

def actionProfile (firstAction secondAction : Bool) :
    Profile game.strategicSignature :=
  fun who => purePolicy (if who = false then firstAction else secondAction) who

def behavioralProfile (firstAction secondAction : Bool) :
    Profile game.behavioralSignature :=
  fun who => (actionProfile firstAction secondAction who).toBehavioral

def secondHistory (firstAction : Bool) : execution.History :=
  let isLegal := jointAt_legal_first firstAction
  execution.initHistory.extend isLegal (by
    exact FinDist.mem_support_pure.mpr rfl)

def terminalHistory (firstAction secondAction : Bool) : execution.History :=
  let isLegal := jointAt_legal_second firstAction secondAction
  (secondHistory firstAction).extend isLegal (by
    exact FinDist.mem_support_pure.mpr rfl)

def firstChoice (action : Bool) :
    {joint : Player → Option Bool //
      execution.Legal execution.initHistory.state joint} :=
  ⟨jointAt false action, jointAt_legal_first action⟩

def secondChoice (firstAction secondAction : Bool) :
    {joint : Player → Option Bool //
      execution.Legal (secondHistory firstAction).state joint} :=
  ⟨jointAt true secondAction,
    jointAt_legal_second firstAction secondAction⟩

theorem step_firstChoice (action : Bool) :
    execution.step execution.initHistory.state (firstChoice action) =
      FinDist.pure (.second action) := by
  rfl

theorem step_secondChoice (firstAction secondAction : Bool) :
    execution.step (secondHistory firstAction).state
        (secondChoice firstAction secondAction) =
      FinDist.pure (.done firstAction secondAction) := by
  rfl

theorem historyChooser_first (firstAction secondAction : Bool) :
    information.historyChooser (actionProfile firstAction secondAction)
        execution.initHistory first_not_terminal =
      firstChoice firstAction := by
  apply Subtype.ext
  funext who
  cases who <;>
    simp [InformationModel.historyChooser, InformationModel.jointAt,
      InformationModel.Policy.act, actionProfile, purePolicy, jointAt,
      firstChoice, infoOf_eq_state]

theorem historyChooser_second (firstAction secondAction : Bool) :
    information.historyChooser (actionProfile firstAction secondAction)
        (secondHistory firstAction) (second_not_terminal firstAction) =
      secondChoice firstAction secondAction := by
  apply Subtype.ext
  funext who
  cases who
  · simp only [InformationModel.historyChooser, InformationModel.jointAt,
      InformationModel.Policy.act, actionProfile, purePolicy, secondChoice]
    rw [infoOf_eq_state]
    simp [secondHistory, jointAt]
  · simp only [InformationModel.historyChooser, InformationModel.jointAt,
      InformationModel.Policy.act, actionProfile, purePolicy, secondChoice]
    rw [infoOf_eq_state]
    simp [secondHistory, jointAt]

theorem run_actionProfile (firstAction secondAction : Bool) :
    information.run (actionProfile firstAction secondAction) 2 =
      FinDist.pure (terminalHistory firstAction secondAction) := by
  rw [InformationModel.run, InformationModel.runFrom,
    execution.runHistoryFor_succ_of_not_terminal
      (information.historyChooser (actionProfile firstAction secondAction))
      1 first_not_terminal,
    historyChooser_first]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun _ => execution.runHistoryFor
      (information.historyChooser (actionProfile firstAction secondAction))
      1 (secondHistory firstAction))]
  · rw [step_firstChoice, FinDist.pure_bind]
    rw [execution.runHistoryFor_succ_of_not_terminal
      (information.historyChooser (actionProfile firstAction secondAction))
      0 (second_not_terminal firstAction), historyChooser_second]
    rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
      (g := fun _ => FinDist.pure
        (terminalHistory firstAction secondAction))]
    · rw [step_secondChoice, FinDist.pure_bind]
    · intro target realized
      have htarget : target = .done firstAction secondAction := by
        simpa [execution, secondChoice, secondHistory, jointAt] using realized
      subst target
      have hhistory :
          (secondHistory firstAction).extend
              (secondChoice firstAction secondAction).2 realized =
            terminalHistory firstAction secondAction :=
        history_eq_of_state_eq rfl
      rw [execution.runHistoryFor_zero, hhistory]
  · intro target realized
    have htarget : target = .second firstAction := by
      simpa [execution, firstChoice, jointAt] using realized
    subst target
    have hhistory :
        execution.initHistory.extend (firstChoice firstAction).2 realized =
          secondHistory firstAction :=
      history_eq_of_state_eq rfl
    rw [hhistory]

theorem runBehavioral_actionProfile (firstAction secondAction : Bool) :
    information.runBehavioral
        (behavioralProfile firstAction secondAction) 2 =
      FinDist.pure (terminalHistory firstAction secondAction) := by
  have hpure := information.runBehavioralFrom_toBehavioral
    (actionProfile firstAction secondAction) 2 execution.initHistory
  exact hpure.trans (run_actionProfile firstAction secondAction)

def coordinationUtility (history : execution.History) (_ : Player) : ℝ :=
  match history.state with
  | .done firstAction secondAction =>
      if firstAction = secondAction then 1 else 0
  | _ => 0

theorem coordinationUtility_le_one (history : execution.History)
    (who : Player) : coordinationUtility history who ≤ 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | first | second => simp [coordinationUtility]
  | done firstAction secondAction =>
      by_cases heq : firstAction = secondAction <;>
        simp [coordinationUtility, heq]

theorem coordinated_value (who : Player) :
    expectedUtility coordinationUtility who
        (information.runBehavioral (behavioralProfile true true) 2) = 1 := by
  rw [runBehavioral_actionProfile, expectedUtility_pure]
  rfl

/-- Coordination at `(true, true)` is a behavioral Nash equilibrium: its value
is one and no history can yield either player more than one. -/
theorem coordinated_behavioral_isNash :
    IsNash (game.toBehavioralGameForm 2)
      (euPreference coordinationUtility) (behavioralProfile true true) := by
  rw [game.isNash_toBehavioralGameForm_iff]
  intro who replacement
  rw [coordinated_value]
  exact FinDist.expect_le_of_forall
    (information.runBehavioral
      (Profile.update (behavioralProfile true true) who replacement) 2)
    (fun history => coordinationUtility history who) 1
    (fun history _ => coordinationUtility_le_one history who)

/-- The Nash-transfer theorem reaches an ordinary mixed Nash equilibrium of
the extracted strategic form, not merely equality of whole-profile laws. -/
theorem coordinated_mixed_isNash :
    IsNash (game.toGameForm 2).mixed (euPreference coordinationUtility)
      (fun who => (behavioralProfile true true who).toMixed) :=
  game.isNash_toMixed_of_isNash_behavioral perfectRecall
    coordinationUtility (behavioralProfile true true) 2
    coordinated_behavioral_isNash

/-- The converse transfer consumes that mixed equilibrium and returns a
behavioral Nash equilibrium through the canonical conditional reading. -/
theorem coordinated_roundTrip_behavioral_isNash :
    IsNash (game.toBehavioralGameForm 2) (euPreference coordinationUtility)
      (fun who => InformationModel.MixedPolicy.toBehavioral
        (M := information) (behavioralProfile true true who).toMixed) :=
  game.isNash_toBehavioral_of_isNash_mixed perfectRecall
    coordinationUtility
    (fun who => (behavioralProfile true true who).toMixed) 2
    coordinated_mixed_isNash

def coinMixed (who : Player) : game.MixedPlan who :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (purePolicy false who))
    (FinDist.pure (purePolicy true who))

/-- A genuinely mixed deviation by player `false` is realized behaviorally
while player `true` keeps the prescribed `false` policy. -/
theorem coinDeviation_unilateralLaw :
    information.runMixed
        (Profile.update (sig := information.strategicSignature.mixed)
          (fun who => (behavioralProfile true false who).toMixed)
          false (coinMixed false)) 2 =
      information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          (behavioralProfile true false) false
          (InformationModel.MixedPolicy.toBehavioral
            (M := information) (coinMixed false))) 2 :=
  game.kuhn_behavioral_update_toMixed perfectRecall
    (behavioralProfile true false) false (coinMixed false) 2

theorem coinDeviation_nonDeviator_fixed :
    (Profile.update (behavioralProfile true false) false
      (InformationModel.MixedPolicy.toBehavioral
        (M := information) (coinMixed false))) true =
      behavioralProfile true false true :=
  Profile.update_of_ne _ _ (by decide)

/-- The fixed-nondeviator clause is semantically load-bearing: changing the
second player's deterministic action changes the terminal history law. -/
theorem changing_nonDeviator_changes_law :
    information.runBehavioral (behavioralProfile true false) 2 ≠
      information.runBehavioral (behavioralProfile true true) 2 := by
  rw [runBehavioral_actionProfile, runBehavioral_actionProfile]
  intro heq
  have hsupport := congrArg FinDist.support heq
  have hmem : terminalHistory true false ∈
      (FinDist.pure (terminalHistory true true)).support := by
    rw [← hsupport]
    exact FinDist.mem_support_pure.mpr rfl
  rw [FinDist.mem_support_pure] at hmem
  have hstate := congrArg ExecutionProtocol.History.state hmem
  simp [terminalHistory, jointAt] at hstate

end GameTheory.Tests.EFGKuhnNash
