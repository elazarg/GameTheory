/-
# Where a player puts its randomness

The same player moves twice and cannot tell the two occasions apart: it observes
only whether play has stopped. That is enough to separate the two ways of
randomizing.

A behavioral policy draws afresh each time it is consulted, so it can play one
action and then the other. A mixed policy draws a whole deterministic policy
once, and that policy answers the one information state the one way, so the two
moves must agree. The laws therefore differ, and the difference is exactly a
pair of unequal moves.

This is why an equivalence between the two randomizations has to assume that
play never returns a player to an information state it has already acted at. The
protocol here is the smallest thing that violates that assumption, so it records
what such a hypothesis is buying.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Tests.Repeat

open GameTheory GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- The player's two options. -/
inductive Vote | up | down
  deriving DecidableEq, Repr

/-- Play records the votes cast so far. -/
inductive Round | start | after (first : Vote) | done (first second : Vote)
  deriving DecidableEq, Repr

/-- Whether play has stopped. This is the only thing the player observes, which
is what makes the two decision points indistinguishable to it. -/
def Round.stopped : Round → Bool
  | .done _ _ => true
  | _ => false

/-- Vote twice. -/
@[reducible]
def twice : ExecutionProtocol Unit where
  State := Round
  Action _ := Vote
  init := .start
  active state _ := state.stopped = false
  available _ _ := Set.univ
  terminal state := state.stopped = true
  step state joint :=
    match state with
    | .start =>
        match joint.1 () with
        | some vote => FinDist.pure (.after vote)
        | none => FinDist.pure (.after .up)
    | .after first =>
        match joint.1 () with
        | some vote => FinDist.pure (.done first vote)
        | none => FinDist.pure (.done first .up)
    | .done first second => FinDist.pure (.done first second)
  progress := by
    rintro state hterm
    refine ⟨fun _ => some .up, fun _ => ⟨?_, Set.mem_univ _⟩⟩
    cases hstopped : state.stopped
    · rfl
    · exact absurd hstopped hterm

/-- The player is told only whether play has stopped. -/
@[reducible]
def signals : InfoSignals twice where
  PublicSignal := Bool
  PrivateSignal _ := Unit
  initialPublic := false
  initialPrivate _ := ()
  publicSignal event := event.target.stopped
  privateSignal _ _ := ()
  InfoState _ := Bool
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

/-- The information state says exactly whether play has stopped — and nothing
about which round it is. -/
theorem infoOf_eq_stopped :
    ∀ {state : twice.State} (trace : Trace twice state),
      signals.infoOf () trace = state.stopped
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The menu: vote while play continues, do nothing once it has stopped. -/
def menuAt : Bool → Set (Option Vote)
  | false => {some .up, some .down}
  | true => {none}

/-- The information model. -/
@[reducible]
def model : InformationModel twice where
  toInfoSignals := signals
  menu _ info := menuAt info
  menu_adequate := by
    rintro ⟨⟩ state trace choice
    rw [infoOf_eq_stopped trace]
    cases hstopped : state.stopped
    · cases choice with
      | none => simp [menuAt, LegalOption, hstopped]
      | some vote => cases vote <;> simp [menuAt, LegalOption, hstopped]
    · cases choice with
      | none => simp [menuAt, LegalOption, hstopped]
      | some vote => simp [menuAt, LegalOption, hstopped]

theorem up_mem_menu : (some Vote.up) ∈ model.menu () false := by simp [menuAt]

theorem down_mem_menu : (some Vote.down) ∈ model.menu () false := by simp [menuAt]

theorem none_mem_menu : (none : Option Vote) ∈ model.menu () true := by simp [menuAt]

/-! ## The two randomizations -/

/-- A fair coin at the one decision-making information state. -/
def coinPolicy : model.BehavioralPolicy () := fun info =>
  match info with
  | false =>
      FinDist.mix (1 / 2) (by norm_num) (by norm_num)
        (FinDist.pure ⟨some .up, up_mem_menu⟩) (FinDist.pure ⟨some .down, down_mem_menu⟩)
  | true => FinDist.pure ⟨none, none_mem_menu⟩

theorem mem_support_coinPolicy_up :
    (⟨some Vote.up, up_mem_menu⟩ : model.Choice () false) ∈ (coinPolicy false).support := by
  refine FinDist.prob_pos_iff.mp ?_
  rw [show coinPolicy false = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure ⟨some .up, up_mem_menu⟩)
      (FinDist.pure ⟨some .down, down_mem_menu⟩) from rfl]
  simp [FinDist.prob_pure_eq_ite]

theorem mem_support_coinPolicy_down :
    (⟨some Vote.down, down_mem_menu⟩ : model.Choice () false) ∈ (coinPolicy false).support := by
  refine FinDist.prob_pos_iff.mp ?_
  rw [show coinPolicy false = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure ⟨some .up, up_mem_menu⟩)
      (FinDist.pure ⟨some .down, down_mem_menu⟩) from rfl]
  simp [FinDist.prob_pure_eq_ite]
  norm_num

/-! ## A mixed profile can only vote the same way twice

A deterministic policy answers the one continuing information state once and for
all, so both of its votes are that answer. Drawing such a policy at random
therefore never produces two different votes. -/

theorem legal_of_not_stopped {state : Round} (hstopped : state.stopped = false)
    (vote : Vote) : twice.Legal state (fun _ => some vote) :=
  ExecutionProtocol.legal_of_legalOption (by simp [hstopped])
    fun _ => ⟨hstopped, Set.mem_univ _⟩

/-- The state a vote leads to. -/
def stepTo : Round → Vote → Round
  | .start, vote => .after vote
  | .after first, vote => .done first vote
  | .done first second, _ => .done first second

theorem step_eq_pure (state : Round) (hstopped : state.stopped = false) (vote : Vote)
    (hlegal : twice.Legal state (fun _ => some vote)) :
    twice.step state ⟨fun _ => some vote, hlegal⟩ = FinDist.pure (stepTo state vote) := by
  cases state with
  | start => rfl
  | after first => rfl
  | done first second => exact absurd hstopped (by simp [Round.stopped])

/-- Whatever a deterministic policy answers at the continuing information state
is what it answers at both decision points. -/
theorem exists_vote (policy : model.Policy ()) : ∃ vote, (policy false).1 = some vote := by
  have hmem := (policy false).2
  simp only [menuAt, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  exacts [⟨.up, h⟩, ⟨.down, h⟩]

theorem step_historyChooser (policies : (i : Unit) → model.Policy i) (vote : Vote)
    (hvote : (policies () false).1 = some vote) (h : History twice)
    (hstopped : h.state.stopped = false) (hterm : ¬ twice.terminal h.state) :
    twice.step h.state (model.historyChooser policies h hterm) =
      FinDist.pure (stepTo h.state vote) := by
  obtain ⟨state, trace⟩ := h
  have hjoint : (model.jointAt policies trace) () = some vote := by
    simp only [InformationModel.jointAt, InformationModel.Policy.act]
    rw [show model.infoOf () trace = false from (infoOf_eq_stopped trace).trans hstopped]
    exact hvote
  cases state with
  | start =>
    show (match (model.jointAt policies trace) () with
      | some vote => FinDist.pure (Round.after vote)
      | none => FinDist.pure (Round.after Vote.up)) = _
    rw [hjoint]
    rfl
  | after first =>
    show (match (model.jointAt policies trace) () with
      | some vote => FinDist.pure (Round.done first vote)
      | none => FinDist.pure (Round.done first Vote.up)) = _
    rw [hjoint]
    rfl
  | done first second => exact absurd hstopped (by simp [Round.stopped])

/-- One step of deterministic play. -/
theorem map_state_runFrom_one (policies : (i : Unit) → model.Policy i) (vote : Vote)
    (hvote : (policies () false).1 = some vote) (h : History twice)
    (hstopped : h.state.stopped = false) :
    FinDist.map History.state (model.runFrom policies 1 h) =
      FinDist.pure (stepTo h.state vote) := by
  have hterm : ¬ twice.terminal h.state := by simp [hstopped]
  have hstep := step_historyChooser policies vote hvote h hstopped hterm
  rw [InformationModel.runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 0 hterm]
  refine FinDist.map_bindOnSupport_const _ fun target hrealized => ?_
  rw [hstep, FinDist.mem_support_pure] at hrealized
  subst hrealized
  rw [ExecutionProtocol.runHistoryFor_zero, FinDist.map_pure]
  rfl

/-- **A deterministic profile votes the same way twice**, because it meets the
same information state twice and a policy is a function of that. -/
theorem map_state_runFrom_two (policies : (i : Unit) → model.Policy i) (vote : Vote)
    (hvote : (policies () false).1 = some vote) :
    FinDist.map History.state (model.runFrom policies 2 twice.initHistory) =
      FinDist.pure (Round.done vote vote) := by
  have hterm : ¬ twice.terminal twice.initHistory.state := by
    simp [Round.stopped, ExecutionProtocol.initHistory]
  have hstep := step_historyChooser policies vote hvote twice.initHistory rfl hterm
  rw [InformationModel.runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 1 hterm]
  refine FinDist.map_bindOnSupport_const _ fun target hrealized => ?_
  rw [hstep, FinDist.mem_support_pure] at hrealized
  subst hrealized
  exact map_state_runFrom_one policies vote hvote _ rfl

/-- **The mixed law never shows two different votes.** Every deterministic
profile it draws answers the one continuing information state once, so both
votes are that answer. -/
theorem not_mem_support_runMixed :
    Round.done Vote.up Vote.down ∉
      (FinDist.map History.state
        (model.runMixed (fun _ => coinPolicy.toMixed) 2)).support := by
  rw [InformationModel.runMixed, InformationModel.runMixedFrom, FinDist.map_bind,
    FinDist.support_bind]
  intro hmem
  obtain ⟨policies, _, hin⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨vote, hvote⟩ := exists_vote (policies ())
  rw [map_state_runFrom_two policies vote hvote, FinDist.mem_support_pure] at hin
  cases vote <;> simp at hin

/-! ## The behavioral law does show two different votes

Each consultation is a fresh draw, so `up` then `down` is a possible play. -/

theorem mem_support_randomizedChooser {state : Round} (trace : Trace twice state)
    (hterm : ¬ twice.terminal (History.state ⟨state, trace⟩))
    (draws : (i : Unit) → model.Choice i (model.infoOf i trace))
    (hmem : ∀ i, draws i ∈ (coinPolicy (model.infoOf i trace)).support) :
    (⟨fun i => (draws i).1,
        ExecutionProtocol.legal_of_legalOption hterm fun i =>
          (model.menu_adequate i trace (draws i).1).mp (draws i).2⟩ :
      { joint : ∀ i, Option (twice.Action i) //
        twice.Legal (History.state ⟨state, trace⟩) joint }) ∈
      (model.randomizedChooser (fun _ => coinPolicy) ⟨state, trace⟩ hterm).support := by
  rw [InformationModel.randomizedChooser, InformationModel.behavioralJoint, FinDist.support_map]
  exact ⟨draws, FinDist.mem_support_pi.mpr hmem, rfl⟩

/-- **The behavioral law does.** Two independent draws can disagree, and this
one does. -/
theorem mem_support_runBehavioral :
    Round.done Vote.up Vote.down ∈
      (FinDist.map History.state (model.runBehavioral (fun _ => coinPolicy) 2)).support := by
  have hterm0 : ¬ twice.terminal (History.state twice.initHistory) := by
    simp [Round.stopped, ExecutionProtocol.initHistory]
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 1 hterm0,
    FinDist.map_bind, FinDist.support_bind]
  refine Set.mem_biUnion
    (mem_support_randomizedChooser _ hterm0 (fun _ => ⟨some Vote.up, up_mem_menu⟩)
      (fun _ => mem_support_coinPolicy_up)) ?_
  rw [FinDist.map_bindOnSupport, FinDist.support_bindOnSupport]
  refine Set.mem_iUnion.mpr ⟨Round.after Vote.up,
    Set.mem_iUnion.mpr ⟨FinDist.mem_support_pure.mpr rfl, ?_⟩⟩
  have hterm1 : ¬ twice.terminal
      (History.state (twice.initHistory.extend
        (ExecutionProtocol.legal_of_legalOption hterm0 fun i =>
          (model.menu_adequate i twice.initHistory.trace (some Vote.up)).mp up_mem_menu)
        (FinDist.mem_support_pure.mpr rfl))) := by
    simp [Round.stopped, ExecutionProtocol.History.extend]
  rw [ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 0 hterm1,
    FinDist.map_bind, FinDist.support_bind]
  refine Set.mem_biUnion
    (mem_support_randomizedChooser _ hterm1 (fun _ => ⟨some Vote.down, down_mem_menu⟩)
      (fun _ => mem_support_coinPolicy_down)) ?_
  rw [FinDist.map_bindOnSupport, FinDist.support_bindOnSupport]
  refine Set.mem_iUnion.mpr ⟨Round.done Vote.up Vote.down,
    Set.mem_iUnion.mpr ⟨FinDist.mem_support_pure.mpr rfl, ?_⟩⟩
  rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure, FinDist.mem_support_pure]
  rfl

/-- **Where a player puts its randomness matters.** Drawing at each information
state and drawing once over policies give different laws, and the separating
event is a pair of unequal votes at one information state visited twice.

An equivalence between the two must therefore rule this out, which is what a
hypothesis forbidding a player to revisit an information state it has acted at
is for. -/
theorem runBehavioral_ne_runMixed :
    FinDist.map History.state (model.runBehavioral (fun _ => coinPolicy) 2) ≠
      FinDist.map History.state (model.runMixed (fun _ => coinPolicy.toMixed) 2) := by
  intro hequal
  refine not_mem_support_runMixed ?_
  rw [← hequal]
  exact mem_support_runBehavioral

/-! ## The condition the counterexample violates

The separation above is not an accident of this protocol's shape: it is exactly
a player being asked to act twice at one information state. Naming that
condition and refuting it here keeps the two facts attached to each other. -/

theorem legalUpStart : twice.Legal Round.start (fun _ => some Vote.up) :=
  legal_of_not_stopped rfl .up

theorem realized_afterUp :
    Round.after Vote.up ∈ (twice.step Round.start ⟨_, legalUpStart⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem legalDownAfter : twice.Legal (Round.after Vote.up) (fun _ => some Vote.down) :=
  legal_of_not_stopped rfl .down

theorem realized_done :
    Round.done Vote.up Vote.down ∈
      (twice.step (Round.after Vote.up) ⟨_, legalDownAfter⟩).support :=
  FinDist.mem_support_pure.2 rfl

/-- The play that votes `up` and then `down`. -/
def votedTwice : Trace twice (Round.done Vote.up Vote.down) :=
  .extend (.extend .start _ legalUpStart realized_afterUp) _ legalDownAfter realized_done

/-- Along it, the player acted twice — and both times at the same information
state, because all it ever saw was that play had not stopped. -/
theorem actedAt_votedTwice : signals.actedAt () votedTwice = [false, false] := rfl

/-- **So this protocol fails the condition**, which is why the two
randomizations could come apart on it. -/
theorem not_actsOnceAtEachInfoState : ¬ signals.ActsOnceAtEachInfoState := by
  intro hactsOnce
  have hnodup := hactsOnce () votedTwice
  rw [actedAt_votedTwice] at hnodup
  simp at hnodup

end GameTheory.Tests.Repeat
