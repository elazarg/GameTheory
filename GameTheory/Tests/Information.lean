/-
# Hostile information tests

The design constraint under test is that the information strategy type must not
exposes hidden execution state at an information set, or if locality holds only
as a later proposition. These are the tests that would detect it.

The protocol below is the standard validation case: an imperfect-information
game with two execution states in one information set. Nature deals a card; the
`informed` seat is privately told which card it is, the `blind` seat is not; both
then call a card simultaneously, and the terminal state records the truth and
both calls.

Four things make it hostile rather than decorative.

* The two dealt states are genuinely different states with different
  continuations — the terminal state remembers which card was dealt — yet the
  blind seat's information state is the *same value* at both. So `congrArg` is
  enough to make every blind policy answer them identically
  (`every_blind_policy_agrees`). Nothing asserts constancy; the policy type has
  no state argument to vary.
* The same protocol contains a seat that *can* tell the two states apart, so
  equality of the blind seat's information states is real content and not the
  degeneracy of an `InfoState` like `Unit` that would make every such equation
  true. That is `informed_can_tell`, and it is the probe the whole file rests
  on.
* Three further probes rule out cheaper degeneracies: the blind seat's own call
  reaches its information state (`blind_remembers_own_call`, so `pushInfo`'s
  action argument is load-bearing), its information state moves when the deal is
  announced (`blind_sees_the_deal`, so it is not constant along a history), and
  the two merged states have different futures (`hidden_card_matters`). The menu
  is not `Set.univ` either: at the calling phase the blind seat must name a card
  and may not pass. Finally `blindPolicy` inhabits the policy type, so the
  `∀ policy` statements are not quantifying over nothing.
* Beliefs and legality are checked at the information *set*: a uniform posterior
  over the two dealt states is supported on it, and every blind policy's call is
  legal at both states — while the policy never received either.

`blind_policy_type` is the structural test: the public policy type is stated as
a `rfl`-checked type equation in which `hiddenCard.State` does not appear.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Probability

/-! ## Structural test: the policy type has no execution state

For *any* protocol and model, a policy is a function of the information state
and its menu. A policy that reads `E.State` is not this type, so a non-local
strategy is not merely unused — it cannot be written. -/

example {ι : Type} {E : ExecutionProtocol ι} (M : InformationModel E) (i : ι) :
    M.Policy i =
      ((info : M.InfoState i) →
        { choice : Option (E.Action i) // choice ∈ M.menu i info }) := rfl

/-! ## A hidden card, then simultaneous calls -/

/-- The two cards; also the two things a seat may call. -/
inductive Card
  | high
  | low
  deriving DecidableEq

/-- The two seats. Only one of them is told the deal. -/
inductive Seat
  | informed
  | blind
  deriving DecidableEq

/-- The publicly visible stage of play. Everyone can see it; nobody learns the
card from it. -/
inductive Phase
  | opening
  | calling
  | over
  deriving DecidableEq

/-- Execution states. `settled` remembers the dealt card as well as both calls,
so the two dealt states are genuinely different states with different
continuations. -/
inductive Table
  | shuffle
  | dealt (card : Card)
  | settled (card blindCall informedCall : Card)
  deriving DecidableEq

/-- The stage of play a state is at. -/
def Table.phase : Table → Phase
  | .shuffle => .opening
  | .dealt _ => .calling
  | .settled .. => .over

/-- The fair coin nature flips. -/
def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

/-- Both sides of the coin are realized, so both deals are histories. -/
theorem mem_support_fairCoin (side : Bool) : side ∈ fairCoin.support :=
  FinDist.prob_pos_iff.mp
    (by cases side <;> norm_num [fairCoin, FinDist.prob_pure_eq_ite])

/-- Which state each side of the coin deals. -/
def dealOf : Bool → Table
  | true => .dealt .high
  | false => .dealt .low

/-- The call a seat's contribution to a joint action makes. The `none` case is
unreachable at a decision state, where legality forces every seat to call; it is
here only to keep the transition total. -/
def callOf : Option Card → Card
  | some card => card
  | none => .high

/-- One deal, hidden from one of the two seats, then one simultaneous round of
calls.

Marked `@[reducible]` for the reason `coinThenMove` is: without it
`hiddenCard.State` does not reduce to `Table` at `instances` transparency, so
`decide`, instance search, and `simp` fail on the concrete protocol. -/
@[reducible]
def hiddenCard : ExecutionProtocol Seat where
  State := Table
  Action _ := Card
  init := .shuffle
  active state _ := state.phase = .calling
  available _ _ := Set.univ
  terminal state := state.phase = .over
  terminal_inactive := by
    intro state hover _ hcalling
    rw [hover] at hcalling
    simp at hcalling
  step state joint :=
    match state with
    | .shuffle => FinDist.map dealOf fairCoin
    | .dealt card =>
        FinDist.pure
          (.settled card (callOf (joint.1 .blind)) (callOf (joint.1 .informed)))
    | .settled card blindCall informedCall =>
        FinDist.pure (.settled card blindCall informedCall)
  progress := by
    intro state _
    by_cases hcalling : state.phase = Phase.calling
    · exact ⟨fun _ => some .high, fun _ => ⟨hcalling, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hcalling⟩

/-- A seat is active exactly at the calling phase: both seats call, and neither
can tell whose turn it is from anything but the phase. -/
theorem hiddenCard_active (state : Table) (seat : Seat) :
    hiddenCard.active state seat ↔ state.phase = Phase.calling := Iff.rfl

/-- Every card may be called. -/
theorem hiddenCard_available (state : Table) (seat : Seat) :
    hiddenCard.available state seat = Set.univ := rfl

/-- Play stops exactly at the settled phase. -/
theorem hiddenCard_terminal (state : Table) :
    hiddenCard.terminal state ↔ state.phase = Phase.over := Iff.rfl

/-! ### The two histories that share an information set -/

theorem shuffle_not_terminal : ¬ hiddenCard.terminal .shuffle := by decide

theorem shuffle_inactive (seat : Seat) : ¬ hiddenCard.active .shuffle seat := by
  simp [Table.phase]

/-- The deal is a chance step: nobody is active, so the no-op is legal. -/
theorem shuffle_noop_legal : hiddenCard.Legal .shuffle hiddenCard.noop :=
  hiddenCard.noop_isLegal shuffle_not_terminal shuffle_inactive

/-- Both deals are realized by the coin. -/
theorem dealt_mem_support (card : Card) :
    Table.dealt card ∈ (FinDist.map dealOf fairCoin).support := by
  rw [FinDist.support_map]
  cases card
  · exact ⟨true, mem_support_fairCoin true, rfl⟩
  · exact ⟨false, mem_support_fairCoin false, rfl⟩

/-- The history in which the coin has been flipped and `card` came up. -/
def dealHistory (card : Card) : Trace hiddenCard (.dealt card) :=
  .extend Trace.start hiddenCard.noop shuffle_noop_legal (dealt_mem_support card)

/-! ## The information model -/

/-- What every seat sees. The deal is announced; the card is not. -/
inductive Broadcast
  | opening
  | cardsDealt
  | callsMade (blindCall informedCall : Card)
  deriving DecidableEq

/-- The phase a broadcast puts play in. -/
def Broadcast.phase : Broadcast → Phase
  | .opening => .opening
  | .cardsDealt => .calling
  | .callsMade _ _ => .over

/-- The public signal of a realized transition. A step in which somebody called
announces both calls; any other step — in this protocol, only the deal —
announces that cards were dealt, and never which. -/
def broadcastOf (event : StepEvent hiddenCard) : Broadcast :=
  match event.joint .blind, event.joint .informed with
  | some blindCall, some informedCall => .callsMade blindCall informedCall
  | _, _ => .cardsDealt

/-- Only the informed seat is whispered anything. -/
def Whisper : Seat → Type
  | .informed => Option Card
  | .blind => Unit

/-- Nothing is whispered before play starts. -/
def initialWhisper : (seat : Seat) → Whisper seat
  | .informed => none
  | .blind => ()

/-- The private signal of a realized transition: the informed seat is told the
card whenever a deal lands, and the blind seat is told nothing, ever. -/
def whisperOf : (seat : Seat) → StepEvent hiddenCard → Whisper seat
  | .informed, event =>
      match event.target with
      | .dealt card => some card
      | _ => none
  | .blind, _ => ()

/-- A seat's local information: the phase it can see, plus the one card it
remembers — the dealt card for the informed seat, its own last call for the
blind seat. This is a compression of the observation history, not the history
itself. -/
@[reducible]
def Knowledge : Seat → Type := fun _ => Phase × Option Card

/-- Once a card is known it is not forgotten. -/
def remember : Option Card → Option Card → Option Card
  | some card, _ => some card
  | none, prior => prior

/-- The information state a seat starts from. -/
def initKnowledge : (seat : Seat) → Whisper seat → Broadcast → Knowledge seat
  | .informed, whisper, broadcast => (broadcast.phase, whisper)
  | .blind, _, broadcast => (broadcast.phase, none)

/-- How a transition updates a seat's information state. The informed seat
records what it was whispered; the blind seat records its own call. -/
def pushKnowledge : (seat : Seat) → Knowledge seat → Option Card → Whisper seat →
    Broadcast → Knowledge seat
  | .informed, prior, _, whisper, broadcast => (broadcast.phase, remember whisper prior.2)
  | .blind, prior, own, _, broadcast => (broadcast.phase, remember own prior.2)

/-- The observation half of the model. -/
@[reducible]
def dealSignals : InfoSignals hiddenCard where
  PublicSignal := Broadcast
  PrivateSignal := Whisper
  initialPublic := .opening
  initialPrivate := initialWhisper
  publicSignal := broadcastOf
  privateSignal := whisperOf
  InfoState := Knowledge
  initInfo := initKnowledge
  pushInfo := pushKnowledge

/-- Every realized legal transition broadcasts exactly the phase it reaches.
This is the one place the hidden card could have leaked and does not: the deal
broadcasts `cardsDealt` whichever card it dealt. -/
theorem broadcastOf_phase (event : StepEvent hiddenCard) :
    (broadcastOf event).phase = event.target.phase := by
  obtain ⟨source, joint, isLegal, target, realized⟩ := event
  cases source with
  | shuffle =>
      have hblind : joint Seat.blind = none :=
        LegalOption.eq_none_of_inactive (E := hiddenCard) (state := Table.shuffle)
          (i := Seat.blind) (joint Seat.blind)
          (ExecutionProtocol.legalOption_of_legal isLegal Seat.blind)
          (shuffle_inactive Seat.blind)
      have htarget : target ∈ (FinDist.map dealOf fairCoin).support := realized
      rw [FinDist.support_map] at htarget
      obtain ⟨side, _, rfl⟩ := htarget
      cases side <;> simp [broadcastOf, hblind, Broadcast.phase, dealOf, Table.phase]
  | dealt card =>
      have hactive : hiddenCard.active (Table.dealt card) Seat.blind := rfl
      obtain ⟨blindCall, hblind⟩ :=
        LegalOption.exists_eq_some_of_active (E := hiddenCard) (state := Table.dealt card)
          (i := Seat.blind) (joint Seat.blind)
          (ExecutionProtocol.legalOption_of_legal isLegal Seat.blind) hactive
      obtain ⟨informedCall, hinformed⟩ :=
        LegalOption.exists_eq_some_of_active (E := hiddenCard) (state := Table.dealt card)
          (i := Seat.informed) (joint Seat.informed)
          (ExecutionProtocol.legalOption_of_legal isLegal Seat.informed) hactive
      have htarget : target ∈ (FinDist.pure (Table.settled card
          (callOf (joint Seat.blind)) (callOf (joint Seat.informed)))).support := realized
      rw [FinDist.mem_support_pure] at htarget
      subst htarget
      simp [broadcastOf, hblind, hinformed, Broadcast.phase, Table.phase]
  | settled card blindCall informedCall => exact absurd rfl isLegal.1

/-- After any history, every seat's information state records the phase reached.
This is the invariant that makes the model adequate; it needs the analysis
above, because the phase is carried by broadcasts rather than read off the
state. -/
theorem knowledge_phase (seat : Seat) {state : hiddenCard.State}
    (history : Trace hiddenCard state) :
    (dealSignals.infoOf seat history).1 = state.phase := by
  induction history with
  | start => cases seat <;> rfl
  | extend prior joint isLegal realized _ih =>
      rw [InfoSignals.infoOf_extend]
      cases seat <;> exact broadcastOf_phase ⟨_, joint, isLegal, _, realized⟩

/-- The options a phase offers: at the calling phase a seat must name a card,
and everywhere else it must stay silent. -/
def phaseMenu : Phase → Set (Option Card)
  | .calling => { choice | ∃ card, choice = some card }
  | _ => {none}

/-- The model's menu: a function of the seat's own information state, and of
nothing else. -/
def dealMenu : (seat : Seat) → Knowledge seat → Set (Option Card) :=
  fun _ knowledge => phaseMenu knowledge.1

/-- Menu adequacy. The information-local menu agrees with the protocol's legal
options at every state any history producing that information state reaches. -/
theorem dealMenu_adequate (seat : Seat) {state : Table} (history : Trace hiddenCard state)
    (choice : Option Card) :
    choice ∈ dealMenu seat (dealSignals.infoOf seat history) ↔
      LegalOption hiddenCard state seat choice := by
  simp only [dealMenu]
  rw [knowledge_phase seat history]
  cases choice <;> cases hphase : state.phase <;> simp [phaseMenu, LegalOption, hphase]

/-- The information model. -/
@[reducible]
def dealModel : InformationModel hiddenCard where
  toInfoSignals := dealSignals
  menu := dealMenu
  menu_adequate := by
    intro seat _ history choice
    exact dealMenu_adequate seat history choice

/-! ## Test: two execution states, one information state -/

theorem infoOf_dealHistory_blind (card : Card) :
    dealSignals.infoOf .blind (dealHistory card) = (Phase.calling, none) := by
  rw [dealHistory, InfoSignals.infoOf_extend, InfoSignals.infoOf_start]
  rfl

theorem infoOf_dealHistory_informed (card : Card) :
    dealSignals.infoOf .informed (dealHistory card) = (Phase.calling, some card) := by
  rw [dealHistory, InfoSignals.infoOf_extend, InfoSignals.infoOf_start]
  rfl

/-- **The information set.** The two deals are different states, but the blind
seat's information state is the same *value* at both. -/
theorem blind_cannot_tell :
    dealSignals.infoOf .blind (dealHistory .high) =
      dealSignals.infoOf .blind (dealHistory .low) := by
  rw [infoOf_dealHistory_blind, infoOf_dealHistory_blind]

/-- **Locality, by construction.** Every information-local policy makes the same
call at both states, and the proof is `congrArg` — congruence of a function
application. There is no locality hypothesis to assume, because a policy has no
execution state to branch on. -/
theorem every_blind_policy_agrees (policy : dealModel.Policy .blind) :
    policy.act (dealSignals.infoOf .blind (dealHistory .high)) =
      policy.act (dealSignals.infoOf .blind (dealHistory .low)) :=
  congrArg policy.act blind_cannot_tell

/-- The same statement through the library's general law, which is proved the
same way for every protocol and model. -/
theorem every_blind_policy_agrees' (policy : dealModel.Policy .blind) :
    policy.act (dealSignals.infoOf .blind (dealHistory .high)) =
      policy.act (dealSignals.infoOf .blind (dealHistory .low)) :=
  policy.act_eq_of_infoOf_eq (dealHistory .high) (dealHistory .low) blind_cannot_tell

/-- **The structural test.** The blind seat's policy type, spelled out: its
argument is the seat's knowledge and its result is a member of the
knowledge-determined menu. `hiddenCard.State` — that is, `Table` — does not
occur anywhere in it. -/
theorem blind_policy_type :
    dealModel.Policy .blind =
      ((info : Knowledge Seat.blind) →
        { choice : Option Card // choice ∈ dealMenu Seat.blind info }) := rfl

/-! ### The policy type is inhabited

A `∀ policy` statement about an empty type proves nothing, so here is a blind
policy. It is built from the seat's knowledge and the menu, and it type-checks
without ever mentioning `Table`. -/

/-- The blind seat's call as a function of the phase it can see: name `high`
when a call is due, and stay silent otherwise. -/
def blindCallOf : Phase → Option Card
  | .calling => some .high
  | _ => none

theorem blindCallOf_mem_phaseMenu (phase : Phase) :
    blindCallOf phase ∈ phaseMenu phase := by
  cases phase
  · simp [blindCallOf, phaseMenu]
  · exact ⟨Card.high, rfl⟩
  · simp [blindCallOf, phaseMenu]

/-- A blind policy, so `every_blind_policy_agrees` is about a nonempty type. -/
def blindPolicy : dealModel.Policy .blind :=
  fun info => ⟨blindCallOf info.1, blindCallOf_mem_phaseMenu info.1⟩

/-- And it is constrained by the menu: at the deal it must call. -/
theorem blindPolicy_calls (card : Card) :
    blindPolicy.act (dealSignals.infoOf .blind (dealHistory card)) = some .high := by
  rw [InformationModel.Policy.act, infoOf_dealHistory_blind]
  rfl

/-! ## The discriminating probes

Without these the equalities above would be worthless: an `InfoState` of `Unit`,
or one that ignored its inputs, would satisfy every test so far. -/

/-- **Probe 1.** The informed seat, in the very same protocol and the very same
model, *can* tell the two states apart. So `blind_cannot_tell` is a fact about
what the blind seat observes, not an artifact of a degenerate `InfoState`. -/
theorem informed_can_tell :
    dealSignals.infoOf .informed (dealHistory .high) ≠
      dealSignals.infoOf .informed (dealHistory .low) := by
  rw [infoOf_dealHistory_informed, infoOf_dealHistory_informed]
  simp

/-- The joint action in which each seat calls a card. -/
def callJoint (blindCall informedCall : Card) : (seat : Seat) → Option Card
  | .blind => some blindCall
  | .informed => some informedCall

theorem dealt_not_terminal (card : Card) : ¬ hiddenCard.terminal (.dealt card) := by
  simp [Table.phase]

theorem callJoint_legal (card blindCall informedCall : Card) :
    hiddenCard.Legal (.dealt card) (callJoint blindCall informedCall) :=
  ExecutionProtocol.legal_of_legalOption (dealt_not_terminal card) (by
    intro seat
    cases seat <;> exact ⟨rfl, Set.mem_univ _⟩)

theorem callHistory_realized (card blindCall informedCall : Card) :
    Table.settled card blindCall informedCall ∈
      (FinDist.pure (Table.settled card blindCall informedCall)).support :=
  FinDist.mem_support_pure.mpr rfl

/-- The full history: the deal, then both calls. -/
def callHistory (card blindCall informedCall : Card) :
    Trace hiddenCard (.settled card blindCall informedCall) :=
  .extend (dealHistory card) (callJoint blindCall informedCall)
    (callJoint_legal card blindCall informedCall)
    (callHistory_realized card blindCall informedCall)

theorem infoOf_callHistory_blind (card blindCall informedCall : Card) :
    dealSignals.infoOf .blind (callHistory card blindCall informedCall) =
      (Phase.over, some blindCall) := by
  rw [callHistory, InfoSignals.infoOf_extend, infoOf_dealHistory_blind]
  rfl

/-- **Probe 2.** The blind seat's *own* call reaches its information state, so
`pushInfo`'s action argument is load-bearing and the blind seat's knowledge is
not a constant. -/
theorem blind_remembers_own_call (card informedCall : Card) :
    dealSignals.infoOf .blind (callHistory card .high informedCall) ≠
      dealSignals.infoOf .blind (callHistory card .low informedCall) := by
  rw [infoOf_callHistory_blind, infoOf_callHistory_blind]
  simp

/-- **Probe 3.** The blind seat's information state moves when the deal is
announced, so public signals reach it too. -/
theorem blind_sees_the_deal (card : Card) :
    dealSignals.infoOf .blind (Trace.start : Trace hiddenCard hiddenCard.init) ≠
      dealSignals.infoOf .blind (dealHistory card) := by
  rw [infoOf_dealHistory_blind, InfoSignals.infoOf_start]
  decide

/-- **Probe 4.** The menu is not `Set.univ`: at the calling phase the blind seat
must name a card and may not pass. So a policy is genuinely constrained by its
information state, and `blind_policy_type` is not a vacuous type. -/
theorem blind_menu_excludes_passing (card : Card) :
    (none : Option Card) ∉
      dealMenu .blind (dealSignals.infoOf .blind (dealHistory card)) := by
  rw [infoOf_dealHistory_blind]
  simp [dealMenu, phaseMenu]

theorem blind_menu_includes_high (card : Card) :
    some Card.high ∈ dealMenu .blind (dealSignals.infoOf .blind (dealHistory card)) := by
  rw [infoOf_dealHistory_blind]
  exact ⟨Card.high, rfl⟩

/-- **Probe 5.** The two merged states are not interchangeable for the protocol
either: after the low deal, the same pair of calls cannot reach the terminal
state the high deal reaches. So the information set genuinely hides something
that matters, rather than merging two states with the same future. -/
theorem hidden_card_matters (blindCall informedCall : Card) :
    Table.settled .high blindCall informedCall ∉
      (hiddenCard.step (.dealt .low)
        ⟨callJoint blindCall informedCall,
          callJoint_legal .low blindCall informedCall⟩).support := by
  intro hmem
  have hpure : Table.settled Card.high blindCall informedCall ∈
      (FinDist.pure (Table.settled Card.low blindCall informedCall)).support := hmem
  rw [FinDist.mem_support_pure] at hpure
  simp at hpure

/-! ## Beliefs and legality at the information set

Conditional reasoning happens over the information set, and it needs no
state-indexed menu and no equivalence relation on execution states. -/

/-- Both deals lie in the blind seat's information set. -/
theorem dealt_mem_infoSet (card : Card) :
    Table.dealt card ∈
      dealModel.InfoSet .blind (dealSignals.infoOf .blind (dealHistory .high)) :=
  ⟨dealHistory card, by rw [infoOf_dealHistory_blind, infoOf_dealHistory_blind]⟩

/-- A conditional belief at that information state: the uniform posterior, which
here is the chance law itself. -/
def blindBelief : FinDist Table := FinDist.map dealOf fairCoin

theorem blindBelief_onInfoSet :
    dealModel.BeliefOn .blind
      (dealSignals.infoOf .blind (dealHistory .high)) blindBelief := by
  intro state hstate
  rw [blindBelief, FinDist.support_map] at hstate
  obtain ⟨side, _, rfl⟩ := hstate
  cases side with
  | true => exact dealt_mem_infoSet .high
  | false => exact dealt_mem_infoSet .low

/-- Sequential feasibility: whatever a blind policy calls, it is legal at *both*
states the belief considers possible — and the policy received neither. -/
theorem blind_policy_legal_on_belief (policy : dealModel.Policy .blind) (card : Card) :
    LegalOption hiddenCard (.dealt card) .blind
      (policy.act (dealSignals.infoOf .blind (dealHistory .high))) :=
  dealModel.legalOption_of_beliefOn blindBelief_onInfoSet policy (dealt_mem_support card)

/-- And information-local policies still drive execution: their joint action is
legal wherever play has not stopped. -/
theorem jointAt_legal_at_deal (policies : (seat : Seat) → dealModel.Policy seat)
    (card : Card) :
    hiddenCard.Legal (.dealt card) (dealModel.jointAt policies (dealHistory card)) :=
  dealModel.jointAt_legal policies (dealHistory card) (dealt_not_terminal card)

end GameTheory.Tests
