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

namespace GameTheory.Tests.Randomized

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- The player's two options. -/
inductive Vote | up | down
  deriving DecidableEq, Repr, Fintype

/-- Play records the votes made so far. -/
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

/-! ## The condition is satisfiable, and then the two agree

A theorem whose hypothesis nothing satisfies proves nothing. Voting once
satisfies it, so the equivalence applies to a real protocol — and the two
protocols here differ in exactly the feature the hypothesis is about. -/

/-- Play with a single vote. -/
inductive Single | start | voted (vote : Vote)
  deriving DecidableEq, Repr

/-- Whether play has stopped. -/
def Single.stopped : Single → Bool
  | .voted _ => true
  | .start => false

/-- Vote once. -/
@[reducible]
def once : ExecutionProtocol Unit where
  State := Single
  Action _ := Vote
  init := .start
  active state _ := state.stopped = false
  available _ _ := Set.univ
  terminal state := state.stopped = true
  step state joint :=
    match state with
    | .start =>
        match joint.1 () with
        | some vote => FinDist.pure (.voted vote)
        | none => FinDist.pure (.voted .up)
    | .voted vote => FinDist.pure (.voted vote)
  progress := by
    rintro state hterm
    refine ⟨fun _ => some .up, fun _ => ⟨?_, Set.mem_univ _⟩⟩
    cases hstopped : state.stopped
    · rfl
    · exact absurd hstopped hterm

/-- The same observation as before: only whether play has stopped. -/
@[reducible]
def singleSignals : InfoSignals once where
  PublicSignal := Bool
  PrivateSignal _ := Unit
  initialPublic := false
  initialPrivate _ := ()
  publicSignal event := event.target.stopped
  privateSignal _ _ := ()
  InfoState _ := Bool
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem singleInfoOf_eq_stopped :
    ∀ {state : once.State} (trace : Trace once state),
      singleSignals.infoOf () trace = state.stopped
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- Where play has not stopped, it has not started. -/
theorem eq_start_of_not_stopped {state : Single} (hstopped : ¬ state.stopped = true) :
    state = Single.start := by
  cases state with
  | start => rfl
  | voted vote => exact absurd rfl hstopped

/-- **A vote is made at most once.** Every history records at most one decision,
so no information state can carry two. -/
theorem actedAt_single {state : once.State} (trace : Trace once state) :
    singleSignals.actedAt () trace = List.replicate (if state.stopped then 1 else 0) false := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
    have hsource := eq_start_of_not_stopped isLegal.1
    subst hsource
    obtain ⟨vote, hvote⟩ := LegalOption.exists_eq_some_of_active (joint ())
      (ExecutionProtocol.legalOption_of_legal isLegal ()) rfl
    have hstep : once.step Single.start ⟨joint, isLegal⟩ = FinDist.pure (Single.voted vote) := by
      show (match joint () with
        | some v => FinDist.pure (Single.voted v)
        | none => FinDist.pure (Single.voted Vote.up)) = _
      rw [hvote]
    rw [hstep, FinDist.mem_support_pure] at realized
    subst realized
    rw [InfoSignals.actedAt, hvote, ih, singleInfoOf_eq_stopped]
    rfl

theorem single_actsOnceAtEachInfoState : singleSignals.ActsOnceAtEachInfoState := by
  rintro ⟨⟩ state trace
  rw [actedAt_single trace]
  cases state.stopped <;> simp

/-- The information model for a single vote; the menu is read off exactly as
before. -/
@[reducible]
def singleModel : InformationModel once where
  toInfoSignals := singleSignals
  menu _ info := menuAt info
  menu_adequate := by
    rintro ⟨⟩ state trace choice
    rw [singleInfoOf_eq_stopped trace]
    cases hstopped : state.stopped
    · cases choice with
      | none => simp [menuAt, LegalOption, hstopped]
      | some vote => cases vote <;> simp [menuAt, LegalOption, hstopped]
    · cases choice with
      | none => simp [menuAt, LegalOption, hstopped]
      | some vote => simp [menuAt, LegalOption, hstopped]

/-- **The equivalence, instantiated.** On a protocol where the condition holds,
the two randomizations really do induce the same law — so the theorem is not
vacuous, and the two protocols in this file differ in exactly the feature its
hypothesis names. -/
theorem runMixed_eq_runBehavioral_once (β : (i : Unit) → singleModel.BehavioralPolicy i)
    (fuel : ℕ) (h : History once) :
    singleModel.runMixedFrom (fun i => (β i).toMixed) fuel h =
      singleModel.runBehavioralFrom β fuel h :=
  singleModel.runMixedFrom_toMixed
    (singleModel.actsOnceWhereItMatters_of_actsOnce single_actsOnceAtEachInfoState) fuel β h

/-- The repeated information state offers a real choice, so weakening the
condition to ignore trivial menus does not rescue this protocol. -/
theorem not_subsingleton_choice : ¬ Subsingleton (model.Choice () false) := by
  intro hsub
  have hcollapse := hsub.elim (⟨some Vote.up, up_mem_menu⟩ : model.Choice () false)
    ⟨some Vote.down, down_mem_menu⟩
  simp at hcollapse

/-- **So the separation survives the weaker condition too.** -/
theorem not_actsOnceWhereItMatters : ¬ model.ActsOnceWhereItMatters := by
  intro hacts
  have hpairwise := hacts () votedTwice
  rw [show model.actedAt () votedTwice = [false, false] from actedAt_votedTwice] at hpairwise
  rcases (List.pairwise_cons.mp hpairwise).1 false (by simp) with hne | hsub
  · exact hne rfl
  · exact not_subsingleton_choice hsub

/-! ## Neither protocol here recalls its own moves

Both observe only whether play has stopped, so neither can tell what it did.
That refutes perfect recall on both, and it says what a slice for the recall
direction has to look like: the player must see its own actions, which is a
different signal design rather than a bigger game. -/

/-- One vote cast, play continuing. -/
def votedOnce : Trace twice (Round.after Vote.up) :=
  .extend .start _ legalUpStart realized_afterUp

/-- **The two-vote protocol forgets its own move.** Before voting and after
voting it is in the same information state, but it has not done the same
things. -/
theorem not_perfectRecall : ¬ signals.PerfectRecall := by
  intro hrecall
  have hsame := hrecall () Trace.start votedOnce rfl
  exact absurd hsame (by simp [InfoSignals.ownPlay, votedOnce])

theorem legalUpOnce : once.Legal Single.start (fun _ => some Vote.up) :=
  ExecutionProtocol.legal_of_legalOption (by simp [Single.stopped])
    fun _ => ⟨rfl, Set.mem_univ _⟩

theorem legalDownOnce : once.Legal Single.start (fun _ => some Vote.down) :=
  ExecutionProtocol.legal_of_legalOption (by simp [Single.stopped])
    fun _ => ⟨rfl, Set.mem_univ _⟩

theorem realized_up : Single.voted Vote.up ∈ (once.step .start ⟨_, legalUpOnce⟩).support :=
  FinDist.mem_support_pure.2 rfl

theorem realized_down : Single.voted Vote.down ∈ (once.step .start ⟨_, legalDownOnce⟩).support :=
  FinDist.mem_support_pure.2 rfl

/-- **And so does the one-vote protocol**, for the same reason: having stopped,
it cannot tell which way it voted. Satisfying the no-revisit condition is
therefore not the same as recalling, and this file now separates the two
conditions as well as the two randomizations. -/
theorem single_not_perfectRecall : ¬ singleSignals.PerfectRecall := by
  intro hrecall
  have hsame := hrecall ()
    (Trace.extend .start _ legalUpOnce realized_up)
    (Trace.extend .start _ legalDownOnce realized_down) rfl
  exact absurd hsame (by simp [InfoSignals.ownPlay])

/-! ## The same game, told to remember

Nothing below changes the game: the votes, the states and the transitions are
the ones already defined. Only what the player is told changes — it now sees its
own vote. That is enough to satisfy both conditions at once, and so to turn the
separation above into an equality on the very same protocol.

Recall is a property of the observation map, not of the game. -/

/-- What a player remembers when it remembers its own votes. -/
inductive Memory | fresh | one (first : Vote) | both (first second : Vote)
  deriving DecidableEq, Repr, Fintype

/-- What each state leaves the player remembering. -/
def Round.memory : Round → Memory
  | .start => .fresh
  | .after first => .one first
  | .done first second => .both first second

/-- Where the player has acted and what it did, read off what it remembers. -/
def Memory.record : Memory → List (Memory × Vote)
  | .fresh => []
  | .one first => [(.fresh, first)]
  | .both first second => [(.one first, second), (.fresh, first)]

/-- The same game, with the player told its own vote and nothing else. -/
@[reducible]
def recallSignals : InfoSignals twice where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Memory
  initInfo _ _ _ := .fresh
  pushInfo _ remembered action _ _ :=
    match action with
    | none => remembered
    | some vote =>
        match remembered with
        | .fresh => .one vote
        | .one first => .both first vote
        | .both first second => .both first second

theorem stopped_eq_false_of_legal {state : Round} {joint : ∀ i, Option (twice.Action i)}
    (isLegal : twice.Legal state joint) : state.stopped = false := by
  cases hstopped : state.stopped
  · rfl
  · exact absurd hstopped isLegal.1

/-- One realized step advances what the player remembers exactly as it advances
the state. -/
theorem memory_step {source target : Round} {joint : ∀ i, Option (twice.Action i)}
    (isLegal : twice.Legal source joint)
    (realized : target ∈ (twice.step source ⟨joint, isLegal⟩).support) :
    recallSignals.pushInfo () source.memory (joint ()) () () = target.memory ∧
      (source.memory, (joint ()).getD .up) :: source.memory.record = target.memory.record := by
  obtain ⟨vote, hvote⟩ := LegalOption.exists_eq_some_of_active (joint ())
    (ExecutionProtocol.legalOption_of_legal isLegal ()) (stopped_eq_false_of_legal isLegal)
  have hstopped := stopped_eq_false_of_legal isLegal
  cases source with
  | start =>
    have hstep : twice.step Round.start ⟨joint, isLegal⟩ = FinDist.pure (Round.after vote) := by
      show (match joint () with
        | some chosen => FinDist.pure (Round.after chosen)
        | none => FinDist.pure (Round.after Vote.up)) = _
      rw [hvote]
    rw [hstep, FinDist.mem_support_pure] at realized
    subst realized
    refine ⟨?_, ?_⟩ <;> · show _ = _; rw [hvote]; rfl
  | after first =>
    have hstep :
        twice.step (Round.after first) ⟨joint, isLegal⟩ =
          FinDist.pure (Round.done first vote) := by
      show (match joint () with
        | some chosen => FinDist.pure (Round.done first chosen)
        | none => FinDist.pure (Round.done first Vote.up)) = _
      rw [hvote]
    rw [hstep, FinDist.mem_support_pure] at realized
    subst realized
    refine ⟨?_, ?_⟩ <;> · show _ = _; rw [hvote]; rfl
  | done first second => exact absurd hstopped (by simp [Round.stopped])

/-- The information state is exactly what the state records. -/
theorem recallInfoOf_eq_memory {state : twice.State} (trace : Trace twice state) :
    recallSignals.infoOf () trace = state.memory := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
    rw [InfoSignals.infoOf_extend, ih]
    exact (memory_step isLegal realized).1

/-- And the player's own record is read off it. -/
theorem recallOwnPlay_eq_record {state : twice.State} (trace : Trace twice state) :
    recallSignals.ownPlay () trace = state.memory.record := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
    obtain ⟨vote, hvote⟩ := LegalOption.exists_eq_some_of_active (joint ())
      (ExecutionProtocol.legalOption_of_legal isLegal ()) (stopped_eq_false_of_legal isLegal)
    rw [InfoSignals.ownPlay_extend, hvote, ih, recallInfoOf_eq_memory prior]
    have hsecond := (memory_step isLegal realized).2
    rw [hvote] at hsecond
    exact hsecond

/-- **The player recalls its own play.** Two histories leaving it equally
informed leave it with the same record, because the information state *is* that
record. -/
theorem recall_perfectRecall : recallSignals.PerfectRecall := by
  rintro ⟨⟩ first second traceFirst traceSecond hinfo
  rw [recallOwnPlay_eq_record, recallOwnPlay_eq_record,
    ← recallInfoOf_eq_memory traceFirst, ← recallInfoOf_eq_memory traceSecond, hinfo]

/-- And it is still never asked twice at one information state — now for the
substantive reason that its two decisions are told apart. -/
theorem recall_actsOnceAtEachInfoState : recallSignals.ActsOnceAtEachInfoState := by
  rintro ⟨⟩ state trace
  rw [InfoSignals.actedAt_eq_map_ownPlay, recallOwnPlay_eq_record]
  cases state <;> simp [Round.memory, Memory.record]

/-- The menu, read off what the player remembers. -/
def recallMenuAt : Memory → Set (Option Vote)
  | .both _ _ => {none}
  | _ => {some .up, some .down}

/-- The information model in which the player recalls its own votes. -/
@[reducible]
def recallModel : InformationModel twice where
  toInfoSignals := recallSignals
  menu _ remembered := recallMenuAt remembered
  menu_adequate := by
    rintro ⟨⟩ state trace choice
    rw [recallInfoOf_eq_memory trace]
    cases state with
    | done first second =>
      cases choice with
      | none => simp [recallMenuAt, LegalOption, Round.memory, Round.stopped]
      | some vote => simp [recallMenuAt, LegalOption, Round.memory, Round.stopped]
    | start | after first =>
      cases choice with
      | none => simp [recallMenuAt, LegalOption, Round.memory, Round.stopped]
      | some vote =>
        cases vote <;> simp [recallMenuAt, LegalOption, Round.memory, Round.stopped]

/-- **The separation disappears when the player remembers.** On the very same
game, under signals that let it see its own vote, the two randomizations induce
the same law. Nothing about the game changed; only what the player was told. -/
theorem recall_runMixed_eq_runBehavioral (β : (i : Unit) → recallModel.BehavioralPolicy i)
    (fuel : ℕ) (h : History twice) :
    recallModel.runMixedFrom (fun i => (β i).toMixed) fuel h =
      recallModel.runBehavioralFrom β fuel h :=
  recallModel.runMixedFrom_toMixed
    (recallModel.actsOnceWhereItMatters_of_perfectRecall recall_perfectRecall) fuel β h

/-- **And the direction that needs recall, on the same slice.** Both halves of
the equivalence now hold on one protocol, under one signal design, with each
half's hypothesis discharged rather than assumed. -/
theorem recall_runMixed_toBehavioralWith (fallback : (i : Unit) → recallModel.Policy i)
    (fuel : ℕ) (mixed : (i : Unit) → recallModel.MixedPolicy i) :
    recallModel.runMixed mixed fuel =
      recallModel.runBehavioral (fun i => (mixed i).toBehavioralWith (fallback i)) fuel :=
  recallModel.runMixed_toBehavioralWith
    (InformationModel.constrainsAlike_of_perfectRecall recall_perfectRecall) fallback fuel mixed

/-- **Kuhn's theorem on this slice.** Both conditions hold under the design that
lets the player see its own vote, so the two randomizations describe exactly the
same laws over plays of this game. -/
theorem recall_kuhn (fuel : ℕ) :
    { law | ∃ β : (i : Unit) → recallModel.BehavioralPolicy i,
        recallModel.runBehavioral β fuel = law } =
      { law | ∃ mixed : (i : Unit) → recallModel.MixedPolicy i,
        recallModel.runMixed mixed fuel = law } :=
  recallModel.runBehavioral_image_eq_runMixed_image
    (recallModel.actsOnceWhereItMatters_of_perfectRecall recall_perfectRecall)
    (InformationModel.constrainsAlike_of_perfectRecall recall_perfectRecall) fuel

end GameTheory.Tests.Randomized
