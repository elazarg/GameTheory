/-
# Historywise continuation optimality, including an off-path history

The incumbent exits immediately. Its threatened continuation is therefore
absent from the incumbent run law, but it is still a complete protocol history.
Rewarding is strictly better than punishing there, so initial optimality does
not imply optimality after every complete history.
-/

import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Tests.SubgamePerfect

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State
  | root
  | decision
  | exited
  | punished
  | rewarded
  deriving DecidableEq

inductive Action
  | exit
  | enter
  | punish
  | reward
  deriving DecidableEq

@[reducible]
def arena : ExecutionProtocol Unit where
  State := State
  Action _ := Action
  init := .root
  active state _ := state = .root ∨ state = .decision
  available state _ :=
    match state with
    | .root => {Action.exit, .enter}
    | .decision => {Action.punish, .reward}
    | _ => Set.univ
  terminal state :=
    state = .exited ∨ state = .punished ∨ state = .rewarded
  step state joint :=
    match state with
    | .root =>
        match joint.1 () with
        | some .enter => PMF.pure .decision
        | _ => PMF.pure .exited
    | .decision =>
        match joint.1 () with
        | some .reward => PMF.pure .rewarded
        | _ => PMF.pure .punished
    | .exited => PMF.pure .exited
    | .punished => PMF.pure .punished
    | .rewarded => PMF.pure .rewarded
  progress := by
    intro state hterm
    cases state with
    | root =>
        exact ⟨fun _ => some .exit,
          fun _ => ⟨Or.inl rfl, by simp⟩⟩
    | decision =>
        exact ⟨fun _ => some .punish,
          fun _ => ⟨Or.inr rfl, by simp⟩⟩
    | exited => exact False.elim (hterm (Or.inl rfl))
    | punished => exact False.elim (hterm (Or.inr (Or.inl rfl)))
    | rewarded => exact False.elim (hterm (Or.inr (Or.inr rfl)))

theorem root_not_terminal : ¬ arena.terminal .root := by simp

theorem decision_not_terminal : ¬ arena.terminal .decision := by simp

theorem terminal_exited : arena.terminal .exited := by simp

theorem terminal_punished : arena.terminal .punished := by simp

theorem terminal_rewarded : arena.terminal .rewarded := by simp

def enterJoint : Unit → Option Action := fun _ => some .enter

theorem enterLegal : arena.Legal .root enterJoint := by
  exact ⟨root_not_terminal, fun _ => ⟨Or.inl rfl, by simp⟩⟩

theorem decision_mem_enter :
    State.decision ∈
      (arena.step .root ⟨enterJoint, enterLegal⟩).support := by
  simp [arena, enterJoint]

def decisionTrace : arena.Trace .decision :=
  .extend .start enterJoint enterLegal decision_mem_enter

def decisionHistory : arena.History :=
  ⟨.decision, decisionTrace⟩

/-- Every transition announces the state it reached, so policies see the full
perfect-information state but not a hidden execution argument. -/
@[reducible]
def signals : InfoSignals arena where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .root
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem signals_infoOf_state :
    ∀ {state : State} (trace : arena.Trace state),
      signals.infoOf () trace = state
  | _, .start => rfl
  | _, .extend _prior _joint _isLegal _realized => rfl

def menu : State → Set (Option Action)
  | .root => {some .exit, some .enter}
  | .decision => {some .punish, some .reward}
  | .exited | .punished | .rewarded => {none}

@[reducible]
def model : InformationModel arena where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro who state trace choice
    rw [signals_infoOf_state]
    cases who
    cases state <;> cases choice with
    | none => simp [menu, LegalOption]
    | some action =>
        cases action <;> simp [menu, LegalOption]

def incumbentPolicy : model.Policy ()
  | .root => ⟨some .exit, by simp [menu]⟩
  | .decision => ⟨some .punish, by simp [menu]⟩
  | .exited => ⟨none, by simp [menu]⟩
  | .punished => ⟨none, by simp [menu]⟩
  | .rewarded => ⟨none, by simp [menu]⟩

def rewardingPolicy : model.Policy ()
  | .root => ⟨some .exit, by simp [menu]⟩
  | .decision => ⟨some .reward, by simp [menu]⟩
  | .exited => ⟨none, by simp [menu]⟩
  | .punished => ⟨none, by simp [menu]⟩
  | .rewarded => ⟨none, by simp [menu]⟩

def incumbentProfile : Profile model.strategicSignature :=
  fun _ => incumbentPolicy

def payoff (history : arena.History) (_ : Unit) : ℝ :=
  match history.state with
  | .exited => 2
  | .rewarded => 1
  | _ => 0

theorem payoff_bound (history : arena.History) :
    |payoff history ()| ≤ 2 := by
  rcases history with ⟨state, trace⟩
  cases state <;> norm_num [payoff]

theorem payoff_integrable (law : PMF arena.History) :
    PayoffIntegrable law (fun history => payoff history ()) :=
  payoffIntegrable_of_bounded law _ payoff_bound

def rank : State → ℕ
  | .root => 2
  | .decision => 1
  | .exited | .punished | .rewarded => 0

theorem rank_decreases
    (source target : State)
    (hsuccessor : arena.Successor target source) :
    rank target < rank source := by
  rcases hsuccessor with ⟨joint, hlegal, htarget⟩
  cases source with
  | root =>
      cases hchoice : joint () with
      | none =>
          simp [arena, hchoice] at htarget
          subst target
          norm_num [rank]
      | some action =>
          cases action <;>
            simp [arena, hchoice] at htarget <;>
            subst target <;>
            norm_num [rank]
  | decision =>
      cases hchoice : joint () with
      | none =>
          simp [arena, hchoice] at htarget
          subst target
          norm_num [rank]
      | some action =>
          cases action <;>
            simp [arena, hchoice] at htarget <;>
            subst target <;>
            norm_num [rank]
  | exited => exact False.elim (hlegal.1 terminal_exited)
  | punished => exact False.elim (hlegal.1 terminal_punished)
  | rewarded => exact False.elim (hlegal.1 terminal_rewarded)

theorem arena_wellFoundedPlay : arena.WellFoundedPlay :=
  wellFoundedPlay_of_rank rank rank_decreases

theorem rank_lt_of_mem_actedAt :
    ∀ {state : State} (trace : arena.Trace state)
      (info : State), info ∈ model.actedAt () trace →
        rank state < rank info
  | _, .start, info, hmem => by
      simp [InfoSignals.actedAt] at hmem
  | _, .extend (source := source) prior joint isLegal realized,
      info, hmem => by
      have hdecrease :=
        rank_decreases source _ ⟨joint, isLegal, realized⟩
      rw [InfoSignals.actedAt] at hmem
      cases hchoice : joint () with
      | none =>
          rw [hchoice] at hmem
          exact lt_trans hdecrease
            (rank_lt_of_mem_actedAt prior info hmem)
      | some action =>
          rw [hchoice] at hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          ·
            rw [signals_infoOf_state]
            exact hdecrease
          · exact lt_trans hdecrease
              (rank_lt_of_mem_actedAt prior _ htail)

theorem actedAt_nodup :
    ∀ {state : State} (trace : arena.Trace state),
      (model.actedAt () trace).Nodup
  | _, .start => by simp [InfoSignals.actedAt]
  | _, .extend (source := source) prior joint isLegal realized => by
      rw [InfoSignals.actedAt]
      cases hchoice : joint () with
      | none =>
          simp only
          exact actedAt_nodup prior
      | some action =>
          simp only [List.nodup_cons]
          constructor
          · intro hmem
            have hlt :=
              rank_lt_of_mem_actedAt prior
                (model.infoOf () prior) hmem
            rw [signals_infoOf_state] at hlt
            exact (lt_irrefl _ hlt)
          · exact actedAt_nodup prior

theorem model_actsOnceWhereItMatters :
    model.ActsOnceWhereItMatters :=
  model.actsOnceWhereItMatters_of_actsOnce fun who _ trace => by
    cases who
    exact actedAt_nodup trace

theorem incumbent_step_decision :
    arena.step decisionHistory.state
        (model.historyChooser incumbentProfile
          decisionHistory decision_not_terminal) =
      PMF.pure .punished := by
  rfl

theorem rewarding_step_decision :
    arena.step decisionHistory.state
        (model.historyChooser
          (Profile.update incumbentProfile () rewardingPolicy)
          decisionHistory decision_not_terminal) =
      PMF.pure .rewarded := by
  rfl

theorem incumbent_step_root :
    arena.step arena.initHistory.state
        (model.historyChooser incumbentProfile
          arena.initHistory root_not_terminal) =
      PMF.pure .exited := by
  rfl

theorem exited_mem_incumbent_step :
    State.exited ∈
      (arena.step arena.initHistory.state
        (model.historyChooser incumbentProfile
          arena.initHistory root_not_terminal)).support := by
  rw [incumbent_step_root]
  simp

def exitedHistory : arena.History :=
  arena.initHistory.extend
    (model.historyChooser incumbentProfile
      arena.initHistory root_not_terminal).2
    exited_mem_incumbent_step

theorem incumbent_run_one :
    model.run incumbentProfile 1 =
      PMF.pure exitedHistory := by
  have hinit : ¬ arena.terminal arena.initHistory.state := by
    simpa only [ExecutionProtocol.initHistory_state] using root_not_terminal
  rw [InformationModel.run, InformationModel.runFrom,
    ExecutionProtocol.runHistoryFor_succ_of_not_terminal
      _ 0 hinit]
  calc
    _ = (arena.step arena.initHistory.state
        (model.historyChooser incumbentProfile arena.initHistory hinit)).bind
          (fun _ => PMF.pure exitedHistory) := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro state hstate
      have hstate' : state = .exited := by
        rw [incumbent_step_root, PMF.mem_support_pure_iff] at hstate
        exact hstate
      subst state
      rw [ExecutionProtocol.runHistoryFor_zero]
      congr 1
    _ = PMF.pure exitedHistory := PMF.bind_const _ _

/-- The decision history is legal and reachable in the protocol, but the
incumbent profile exits before reaching it. -/
theorem decisionHistory_offPath :
    decisionHistory ∉
      (model.run incumbentProfile 1).support := by
  intro hmem
  rw [incumbent_run_one, PMF.mem_support_pure_iff] at hmem
  have hstate :=
    congrArg (fun history : arena.History => history.state) hmem
  simp [decisionHistory, exitedHistory] at hstate

private theorem backwardValue_of_constant_successors
    (chooser : arena.HistoryChooser) (history : arena.History)
    (hterm : ¬ arena.terminal history.state) (c : ℝ)
    (hchild : ∀ target
      (realized : target ∈ (arena.step history.state
        (chooser history hterm)).support)
      (hguard : PayoffIntegrable
        (arena.historyBackwardLaw arena_wellFoundedPlay chooser
          (history.extend (chooser history hterm).2 realized))
        (fun outcome => payoff outcome ())),
      arena.historyBackwardValue arena_wellFoundedPlay chooser
        (fun outcome => payoff outcome ())
        (history.extend (chooser history hterm).2 realized) hguard = c) :
    arena.historyBackwardValue arena_wellFoundedPlay chooser
      (fun outcome => payoff outcome ()) history
      (payoff_integrable _) = c := by
  obtain ⟨houter, heq⟩ := arena.historyBackwardValue_of_not_terminal
    hterm (payoff_integrable _) (fun _ => c)
      (by intro target realized hguard
          exact (hchild target realized hguard).symm)
  simpa only [expect_constant] using heq

theorem incumbent_value_decision :
    arena.historyBackwardValue arena_wellFoundedPlay
        (model.historyChooser incumbentProfile)
        (fun history => payoff history ()) decisionHistory
        (payoff_integrable _) = 0 := by
  apply backwardValue_of_constant_successors _ _ decision_not_terminal 0
  intro target realized hguard
  have htarget : target = .punished := by
    rw [incumbent_step_decision, PMF.mem_support_pure_iff] at realized
    exact realized
  subst target
  rw [arena.historyBackwardValue_of_terminal terminal_punished hguard]
  rfl

theorem rewarding_value_decision :
    arena.historyBackwardValue arena_wellFoundedPlay
        (model.historyChooser
          (Profile.update incumbentProfile () rewardingPolicy))
        (fun history => payoff history ()) decisionHistory
        (payoff_integrable _) = 1 := by
  apply backwardValue_of_constant_successors _ _ decision_not_terminal 1
  intro target realized hguard
  have htarget : target = .rewarded := by
    rw [rewarding_step_decision, PMF.mem_support_pure_iff] at realized
    exact realized
  subst target
  rw [arena.historyBackwardValue_of_terminal terminal_rewarded hguard]
  rfl

theorem payoff_le_two (history : arena.History) :
    payoff history () ≤ 2 := by
  rcases history with ⟨state, _trace⟩
  cases state <;> norm_num [payoff]

/-- No policy can earn more than the exit payoff `2` from any history. -/
theorem historyBackwardValue_le_two
    (chooser : arena.HistoryChooser) (history : arena.History) :
    arena.historyBackwardValue arena_wellFoundedPlay chooser
        (fun outcome => payoff outcome ()) history
        (payoff_integrable _) ≤ 2 := by
  unfold ExecutionProtocol.historyBackwardValue
  calc
    expect (arena.historyBackwardLaw arena_wellFoundedPlay chooser history)
        (fun outcome => payoff outcome ()) (payoff_integrable _) ≤
      expect (arena.historyBackwardLaw arena_wellFoundedPlay chooser history)
        (fun _ => 2) (payoffIntegrable_constant _ 2) := by
      apply expect_mono
      intro outcome _
      exact payoff_le_two outcome
    _ = 2 := expect_constant _ 2 _

theorem incumbent_value_root :
    arena.historyBackwardValue arena_wellFoundedPlay
        (model.historyChooser incumbentProfile)
        (fun history => payoff history ()) arena.initHistory
        (payoff_integrable _) = 2 := by
  have hinit : ¬ arena.terminal arena.initHistory.state := by
    simpa only [ExecutionProtocol.initHistory_state] using root_not_terminal
  apply backwardValue_of_constant_successors _ _ hinit 2
  intro target realized hguard
  have htarget : target = .exited := by
    rw [incumbent_step_root, PMF.mem_support_pure_iff] at realized
    exact realized
  subst target
  rw [arena.historyBackwardValue_of_terminal terminal_exited hguard]
  rfl

/-- From the initial history the incumbent is optimal against every whole
replacement policy; the failure below is therefore genuinely off path. -/
theorem incumbent_optimal_from_initial
    (alternative : model.Policy ()) :
    arena.historyBackwardValue arena_wellFoundedPlay
        (model.historyChooser
          (Profile.update incumbentProfile () alternative))
        (fun history => payoff history ()) arena.initHistory
        (payoff_integrable _) ≤
      arena.historyBackwardValue arena_wellFoundedPlay
        (model.historyChooser incumbentProfile)
        (fun history => payoff history ()) arena.initHistory
        (payoff_integrable _) := by
  rw [incumbent_value_root]
  exact historyBackwardValue_le_two
    (model.historyChooser
      (Profile.update incumbentProfile () alternative))
    arena.initHistory

/-- Both directions of the generic theorem specialize to the finite arena
without an EFG-specific solution concept. -/
theorem historywiseOptimal_iff_noProfitableOneShotDeviation :
    model.IsHistorywiseOptimal arena_wellFoundedPlay
        incumbentProfile payoff ↔
      model.HasNoProfitableOneShotDeviation
        arena_wellFoundedPlay incumbentProfile payoff :=
  model.isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    model_actsOnceWhereItMatters arena_wellFoundedPlay
    incumbentProfile payoff (fun _ _ _ => payoff_integrable _)

/-- The incumbent's bad continuation is rejected at the off-path decision
history, even though the incumbent exits before reaching it. -/
theorem incumbent_not_historywiseOptimal :
    ¬ model.IsHistorywiseOptimal arena_wellFoundedPlay
      incumbentProfile payoff := by
  intro hoptimal
  have hdecision := hoptimal () rewardingPolicy decisionHistory
  obtain ⟨hother, hinc, hdecision⟩ := hdecision
  have hreward : arena.historyBackwardValue arena_wellFoundedPlay
      (model.historyChooser (Profile.update incumbentProfile () rewardingPolicy))
      (fun history => payoff history ()) decisionHistory hother = 1 := by
    simpa only using rewarding_value_decision
  have hincumbent : arena.historyBackwardValue arena_wellFoundedPlay
      (model.historyChooser incumbentProfile)
      (fun history => payoff history ()) decisionHistory hinc = 0 := by
    simpa only using incumbent_value_decision
  rw [hreward, hincumbent] at hdecision
  norm_num at hdecision

/-- Equivalently, the bad off-path threat is a profitable one-shot deviation. -/
theorem incumbent_has_profitableOneShotDeviation :
    ¬ model.HasNoProfitableOneShotDeviation
      arena_wellFoundedPlay incumbentProfile payoff := by
  intro hnone
  exact incumbent_not_historywiseOptimal
    (historywiseOptimal_iff_noProfitableOneShotDeviation.mpr hnone)

end GameTheory.Tests.SubgamePerfect
