/-
# Finite multi-round games with imperfect monitoring

This is a constructor for a common native shape, not a second sequential
semantics.  A monitoring game supplies action carriers, initial observations,
and the finite-support law of the public/private signals emitted after a joint
action.  It compiles directly to the accepted execution and information
interfaces.  Within this constructor, Protocol is therefore the sole owner of
histories, policies, run laws, and strategic-form compilation.  This claim does
not subsume `Repeated.PublicMonitoring`, whose native signal-history recursion
serves repeated-game continuation and PPE theory rather than this richer
own-action-recalling information model.

The execution state retains realized joint actions and all signals.  A player's
information state retains only that player's own previous choices and received
signals.  Thus previous-action recall and imperfect monitoring are enforced by
the target types rather than asserted as a locality condition on policies.
-/

import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Languages.MultiRound

open GameTheory GameTheory.Protocol GameTheory.Probability
open ExecutionProtocol

universe uι ua up uq

set_option linter.checkUnivs false in
/-- A finite-horizon game whose observations are emitted after each joint
action.  The signal law may depend on the complete prior joint-action history.
No finiteness, decidable equality, utility, or equilibrium data is stored. -/
structure MonitoringGame (ι : Type uι) where
  Action : ι → Type ua
  PublicSignal : Type up
  PrivateSignal : ι → Type uq
  horizon : ℕ
  initialPublic : PublicSignal
  initialPrivate : (i : ι) → PrivateSignal i
  signalLaw :
    List ((i : ι) → Action i) →
      ((i : ι) → Action i) →
        FinDist (PublicSignal × ((i : ι) → PrivateSignal i))

namespace MonitoringGame

variable {ι : Type uι} (G : MonitoringGame ι)

/-- One realized round in the hidden execution state. -/
structure RoundRecord where
  actions : (i : ι) → G.Action i
  publicSignal : G.PublicSignal
  privateSignal : (i : ι) → G.PrivateSignal i

/-- Hidden finite execution state, in chronological order. -/
abbrev State := List G.RoundRecord

/-- Prior realized joint actions, forgetting all monitoring signals. -/
def actionHistory (state : G.State) : List ((i : ι) → G.Action i) :=
  state.map RoundRecord.actions

/-- Append the sampled signals and the action that generated them. -/
def appendRound (state : G.State) (actions : (i : ι) → G.Action i)
    (signals : G.PublicSignal × ((i : ι) → G.PrivateSignal i)) :
    G.State :=
  state.concat
    { actions := actions
      publicSignal := signals.1
      privateSignal := signals.2 }

/-- One monitoring transition before Protocol legality is attached. -/
def nextLaw (state : G.State) (actions : (i : ι) → G.Action i) :
    FinDist G.State :=
  (G.signalLaw (G.actionHistory state) actions).map (G.appendRound state actions)

theorem exists_eq_appendRound_of_mem_nextLaw {state : G.State}
    {actions : (i : ι) → G.Action i} {target : G.State}
    (reached : target ∈ (G.nextLaw state actions).support) :
    ∃ signals ∈ (G.signalLaw (G.actionHistory state) actions).support,
      target = G.appendRound state actions signals := by
  rw [nextLaw, FinDist.support_map] at reached
  obtain ⟨signals, hsignals, rfl⟩ := reached
  exact ⟨signals, hsignals, rfl⟩

theorem length_appendRound (state : G.State)
    (actions : (i : ι) → G.Action i)
    (signals : G.PublicSignal × ((i : ι) → G.PrivateSignal i)) :
    (G.appendRound state actions signals).length = state.length + 1 := by
  simp [appendRound]

/-- Recover the actual action profile from an all-active legal joint option. -/
private def actionOfJoint (joint : (i : ι) → Option (G.Action i))
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint) :
    (i : ι) → G.Action i :=
  fun i =>
    match hchoice : joint i with
    | some action => action
    | none => False.elim (by
        have hi := hlegal i
        rw [hchoice] at hi
        exact hi trivial)

@[simp]
private theorem actionOfJoint_some (actions : (i : ι) → G.Action i)
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ)
      (fun i => some (actions i))) :
    G.actionOfJoint (fun i => some (actions i)) hlegal = actions := by
  funext i
  rfl

/-- Compile monitoring mechanics to the canonical execution protocol.  Every
player acts once per round; sampled monitoring signals live in the reached
hidden state. -/
@[reducible]
def execution [∀ i, Nonempty (G.Action i)] : ExecutionProtocol ι where
  State := G.State
  Action := G.Action
  init := []
  active state _ := state.length < G.horizon
  available _ _ := Set.univ
  terminal state := G.horizon ≤ state.length
  step state joint :=
    have hactive : state.length < G.horizon := Nat.lt_of_not_ge joint.2.1
    have hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint.1 := by
      intro i
      have hi := joint.2.2 i
      cases hchoice : joint.1 i with
      | none =>
          rw [hchoice] at hi
          exact False.elim (hi hactive)
      | some action => exact ⟨trivial, Set.mem_univ action⟩
    G.nextLaw state (G.actionOfJoint joint.1 hlegal)
  progress := by
    intro state hterm
    have hactive : state.length < G.horizon := Nat.lt_of_not_ge hterm
    refine ⟨fun i => some (Classical.choice (inferInstance : Nonempty (G.Action i))), ?_⟩
    intro i
    exact ⟨hactive, Set.mem_univ _⟩

/-- Supplying an ordinary action at every coordinate reduces the Protocol step
to the monitoring transition on that action profile. -/
theorem execution_step_some [∀ i, Nonempty (G.Action i)]
    (state : G.execution.State) (actions : (i : ι) → G.Action i)
    (legal : G.execution.Legal state (fun i => some (actions i))) :
    G.execution.step state ⟨fun i => some (actions i), legal⟩ =
      G.nextLaw state actions := by
  simp only [execution]
  rw [actionOfJoint_some]

/-- A player's observation of one completed round.  It contains the player's
own choice, never the opponents' action profile. -/
structure RoundObservation (i : ι) where
  ownChoice : Option (G.Action i)
  publicSignal : G.PublicSignal
  privateSignal : G.PrivateSignal i

/-- The local information supplied to policies: initial signals plus a
chronological list of own choices and received round signals. -/
structure InformationState (i : ι) where
  initialPublic : G.PublicSignal
  initialPrivate : G.PrivateSignal i
  rounds : List (G.RoundObservation i)

@[ext]
theorem InformationState.ext {i : ι} {first second : G.InformationState i}
    (initialPublic : first.initialPublic = second.initialPublic)
    (initialPrivate : first.initialPrivate = second.initialPrivate)
    (rounds : first.rounds = second.rounds) : first = second := by
  cases first
  cases second
  simp_all

/-- Most recent public signal in a hidden state, or the initial public signal
before the first round. -/
def latestPublic (state : G.State) : G.PublicSignal :=
  match state.getLast? with
  | none => G.initialPublic
  | some record => record.publicSignal

/-- Most recent private signal received by `i`, or its initial signal before
the first round. -/
def latestPrivate (i : ι) (state : G.State) : G.PrivateSignal i :=
  match state.getLast? with
  | none => G.initialPrivate i
  | some record => record.privateSignal i

@[simp]
theorem latestPublic_appendRound (state : G.State)
    (actions : (i : ι) → G.Action i)
    (signals : G.PublicSignal × ((i : ι) → G.PrivateSignal i)) :
    G.latestPublic (G.appendRound state actions signals) = signals.1 := by
  simp [latestPublic, appendRound]

@[simp]
theorem latestPrivate_appendRound (i : ι) (state : G.State)
    (actions : (i : ι) → G.Action i)
    (signals : G.PublicSignal × ((i : ι) → G.PrivateSignal i)) :
    G.latestPrivate i (G.appendRound state actions signals) = signals.2 i := by
  simp [latestPrivate, appendRound]

/-- Signals and information-memory update for the canonical information
model.  `pushInfo` is the only place own previous choices enter, and it receives
them from Protocol's realized joint action. -/
@[reducible]
def signals [∀ i, Nonempty (G.Action i)] : InfoSignals G.execution where
  PublicSignal := G.PublicSignal
  PrivateSignal := G.PrivateSignal
  initialPublic := G.initialPublic
  initialPrivate := G.initialPrivate
  publicSignal event := G.latestPublic event.target
  privateSignal i event := G.latestPrivate i event.target
  InfoState := G.InformationState
  initInfo _ privateSignal publicSignal :=
    { initialPublic := publicSignal
      initialPrivate := privateSignal
      rounds := [] }
  pushInfo _ prior ownChoice privateSignal publicSignal :=
    { initialPublic := prior.initialPublic
      initialPrivate := prior.initialPrivate
      rounds := prior.rounds.concat
        { ownChoice := ownChoice
          publicSignal := publicSignal
          privateSignal := privateSignal } }

/-- A realized monitoring transition increases the hidden round count by one. -/
theorem target_length_eq_succ [∀ i, Nonempty (G.Action i)]
    {source target : G.execution.State}
    (joint : (i : ι) → Option (G.Action i))
    (legal : G.execution.Legal source joint)
    (reached : target ∈ (G.execution.step source ⟨joint, legal⟩).support) :
    target.length = source.length + 1 := by
  have hactive : source.length < G.horizon := Nat.lt_of_not_ge legal.1
  have hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint := by
    intro i
    have hi := legal.2 i
    cases hchoice : joint i with
    | none =>
        rw [hchoice] at hi
        exact False.elim (hi hactive)
    | some action => exact ⟨trivial, Set.mem_univ action⟩
  have hnext :
      target ∈ (G.nextLaw source (G.actionOfJoint joint hlegal)).support :=
    reached
  obtain ⟨sampled, _, rfl⟩ := G.exists_eq_appendRound_of_mem_nextLaw hnext
  exact G.length_appendRound source _ sampled

/-- The number of locally remembered rounds equals the hidden execution round.
This is the invariant used to make the information-local menu exact. -/
theorem infoOf_rounds_length [∀ i, Nonempty (G.Action i)] (i : ι) :
    ∀ {state : G.execution.State} (trace : Trace G.execution state),
      ((G.signals).infoOf i trace).rounds.length = state.length
  := by
  intro state trace
  induction trace with
  | start => rfl
  | extend prior joint legal reached ih =>
      rw [InfoSignals.infoOf_extend]
      simp only [signals, List.length_concat]
      rw [ih, G.target_length_eq_succ joint legal reached]

/-- Monitoring information has perfect recall: equality of current local
information forces equality of the complete record of the player's earlier
information states and choices.  Opponents' actions may remain hidden. -/
theorem perfectRecall [∀ i, Nonempty (G.Action i)] :
    G.signals.PerfectRecall := by
  intro i first second traceFirst
  induction traceFirst generalizing second with
  | start =>
      intro traceSecond hinfo
      cases traceSecond with
      | start => rfl
      | extend prior joint legal reached =>
          have hlength := congrArg
            (fun info : G.InformationState i => info.rounds.length) hinfo
          simp [signals] at hlength
  | extend priorFirst jointFirst legalFirst reachedFirst ih =>
      intro traceSecond hinfo
      cases traceSecond with
      | start =>
          have hlength := congrArg
            (fun info : G.InformationState i => info.rounds.length) hinfo
          simp [signals] at hlength
      | extend priorSecond jointSecond legalSecond reachedSecond =>
          have hrounds := congrArg
            (fun info : G.InformationState i => info.rounds) hinfo
          have hpriorRounds := congrArg List.dropLast hrounds
          have hlast := congrArg List.getLast? hrounds
          simp [signals] at hpriorRounds hlast
          have hpublic := congrArg
            (fun info : G.InformationState i => info.initialPublic) hinfo
          have hprivate := congrArg
            (fun info : G.InformationState i => info.initialPrivate) hinfo
          have hpriorInfo :
              G.signals.infoOf i priorFirst =
                G.signals.infoOf i priorSecond := by
            apply InformationState.ext
            · simpa [signals] using hpublic
            · simpa [signals] using hprivate
            · exact hpriorRounds
          have hpriorPlay := ih priorSecond hpriorInfo
          rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend,
            hlast.1, hpriorPlay, hpriorInfo]

/-- Information-local menu: every player chooses a real action before the
horizon and contributes the canonical no-op afterwards. -/
def menu [∀ i, Nonempty (G.Action i)] (i : ι) :
    G.InformationState i → Set (Option (G.Action i))
  | info =>
      if info.rounds.length < G.horizon then
        {choice | ∃ action, choice = some action}
      else
        {none}

theorem menu_adequate [∀ i, Nonempty (G.Action i)] (i : ι)
    {state : G.execution.State} (trace : Trace G.execution state)
    (choice : Option (G.Action i)) :
    choice ∈ G.menu i ((G.signals).infoOf i trace) ↔
      LegalOption G.execution state i choice := by
  simp only [menu]
  rw [show ((G.signals).infoOf i trace).rounds.length = state.length from
    G.infoOf_rounds_length i trace]
  by_cases hactive : state.length < G.horizon <;>
    cases choice <;>
    simp [LegalOption, execution, hactive]

/-- Canonical information model for finite imperfect monitoring. -/
@[reducible]
def informationModel [∀ i, Nonempty (G.Action i)] :
    InformationModel G.execution where
  toInfoSignals := G.signals
  menu := G.menu
  menu_adequate := by
    intro i _ trace choice
    exact G.menu_adequate i trace choice

/-- Direct compilation to the accepted FOSG carrier. -/
@[reducible]
def toFOSG [∀ i, Nonempty (G.Action i)] : FOSG.Game ι where
  execution := G.execution
  information := G.informationModel

/-- Strategic-form compilation is exactly the canonical information-local
Protocol compiler; this module defines no evaluator of its own. -/
@[reducible]
def toGameForm [∀ i, Nonempty (G.Action i)] : GameForm ι :=
  G.informationModel.toGameForm G.horizon

@[simp]
theorem toGameForm_play [∀ i, Nonempty (G.Action i)]
    (profile : Profile G.informationModel.strategicSignature) :
    G.toGameForm.play profile = G.informationModel.run profile G.horizon :=
  rfl

end MonitoringGame

end GameTheory.Languages.MultiRound
