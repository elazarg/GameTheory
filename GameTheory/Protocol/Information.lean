/-
# Information models

The information half of D6. `GameTheory.Protocol.Execution` owns transitions;
this module owns *who sees what*. It never redefines a transition: every
observation is emitted by a `StepEvent`, which is exactly the data of one
realized legal step, and the initial views are the only other source.

RFC 9.1.7 makes it a core-invalidating failure if the information strategy type
exposes hidden execution state at an information set or relies only on a later
locality proposition. Three design choices answer that.

* **Locality is typing, not a law.** `Policy` is a function of `InfoState`
  alone. Two histories carrying the same information state therefore receive the
  same answer by `congrArg`, with no constancy hypothesis to assume and no state
  argument a proof could vary. There is deliberately no `Policy` field, lemma,
  or constructor taking `E.State`.
* **The menu is information-local; adequacy is the law.** A policy chooses from
  `menu i info`, a value determined by the information state. The model's
  `menu_adequate` field then *proves* that this menu is the protocol's legal
  option set at every history producing that information state. The direction is
  the point: the menu is not computed from a hidden state and afterwards
  asserted to be local. `menu` therefore also decides *whether* a player moves,
  which is why it ranges over `Option (E.Action i)` — a player who cannot tell
  whose turn it is could not act at all.
* **Beliefs may see states; policies may not.** `InfoSet` and `BeliefOn` are
  analyst-level and mention `E.State` freely, and
  `legalOption_of_mem_menu` transports the one information-local menu to every
  state a belief considers possible. So conditional reasoning at an information
  set needs no second, state-indexed menu — and no native information
  equivalence on states.

Two smaller decisions are worth recording.

`LegalOption` names the single-player conjunct of `IsLegalJoint`, so that the
information layer can speak about one player without quantifying over a joint
action. `IsLegalJoint` is its pointwise conjunction, but only propositionally:
both sides are a `match` stuck on the same discriminant, and two distinct
stuck matchers are not definitionally equal, so
`isLegalJoint_iff_legalOption` does the case split once and the rest of the
module goes through `legal_of_legalOption`.

The information state accumulates along a `Trace`, not over states. An
information set is a set of *histories* a player cannot tell apart; indexing it
by states instead would presuppose that a state summarizes everything a player
remembers, which is exactly perfect recall.

The signal fields and the menu law are split into two structures because the
adequacy law must mention `infoOf`, and `infoOf` is a recursion over the signal
fields. `InformationModel extends InfoSignals` keeps that a private detail:
`M.InfoState`, `M.pushInfo`, and `M.infoOf` all resolve through the parent.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Protocol

open Probability ExecutionProtocol

universe uι us ua up uq uk ur

variable {ι : Type uι}

/-! ## Per-player legality

A joint action is legal when every coordinate is, and the information layer only
ever constrains one coordinate at a time. -/

/-- What one player may contribute to a legal joint action at `state`: an
available action when active, and nothing when inactive. -/
def LegalOption (E : ExecutionProtocol ι) (state : E.State) (i : ι)
    (choice : Option (E.Action i)) : Prop :=
  match choice with
  | some action => E.active state i ∧ action ∈ E.available state i
  | none => ¬ E.active state i

variable {E : ExecutionProtocol ι}

/-- Joint legality is the pointwise conjunction of `LegalOption`. -/
theorem isLegalJoint_iff_legalOption (state : E.State)
    (joint : ∀ i, Option (E.Action i)) :
    IsLegalJoint (E.active state) (E.available state) joint ↔
      ∀ i, LegalOption E state i (joint i) := by
  unfold IsLegalJoint LegalOption
  refine forall_congr' fun i => ?_
  cases joint i <;> exact Iff.rfl

/-- Hence a legal joint action is a non-terminality proof together with one
`LegalOption` per player. -/
theorem ExecutionProtocol.legal_of_legalOption {state : E.State}
    {joint : ∀ i, Option (E.Action i)} (hterm : ¬ E.terminal state)
    (hlegal : ∀ i, LegalOption E state i (joint i)) : E.Legal state joint :=
  ⟨hterm, (isLegalJoint_iff_legalOption state joint).mpr hlegal⟩

/-- And conversely, a legal joint action is legal in every coordinate. -/
theorem ExecutionProtocol.legalOption_of_legal {state : E.State}
    {joint : ∀ i, Option (E.Action i)} (hlegal : E.Legal state joint) (i : ι) :
    LegalOption E state i (joint i) :=
  (isLegalJoint_iff_legalOption state joint).mp hlegal.2 i

/-- An inactive player contributes nothing. -/
theorem LegalOption.eq_none_of_inactive {state : E.State} {i : ι}
    (choice : Option (E.Action i)) (hlegal : LegalOption E state i choice)
    (hinactive : ¬ E.active state i) : choice = none := by
  cases choice with
  | none => rfl
  | some action => exact absurd hlegal.1 hinactive

/-- An active player contributes an action. -/
theorem LegalOption.exists_eq_some_of_active {state : E.State} {i : ι}
    (choice : Option (E.Action i)) (hlegal : LegalOption E state i choice)
    (hactive : E.active state i) : ∃ action, choice = some action := by
  cases choice with
  | none => exact absurd hactive hlegal
  | some action => exact ⟨action, rfl⟩

/-! ## Observations and information states -/

set_option linter.checkUnivs false in
/-- What each player observes, and how it is remembered. The signal alphabets,
the initial views, the per-transition signals, and the possibly compressed
player-local information state — everything except the legality promise, which
`InformationModel` adds on top.

Nothing here can change a transition: `publicSignal` and `privateSignal` consume
a `StepEvent`, which is a transition that already happened. -/
structure InfoSignals (E : ExecutionProtocol ι) where
  /-- The commonly observed signal alphabet. -/
  PublicSignal : Type up
  /-- Each player's private signal alphabet. -/
  PrivateSignal : ι → Type uq
  /-- What everyone sees before the first transition. -/
  initialPublic : PublicSignal
  /-- What each player privately sees before the first transition. -/
  initialPrivate : (i : ι) → PrivateSignal i
  /-- The public signal emitted by one realized legal transition. -/
  publicSignal : StepEvent E → PublicSignal
  /-- The private signal that transition emits to player `i`. -/
  privateSignal : (i : ι) → StepEvent E → PrivateSignal i
  /-- A player's local information state. It may compress the observation
  history; nothing forces it to be the history itself. -/
  InfoState : ι → Type uk
  /-- The information state a player starts from. -/
  initInfo : (i : ι) → PrivateSignal i → PublicSignal → InfoState i
  /-- How one transition updates a player's information state: from its own
  contribution to the joint action and from the signals it received. -/
  pushInfo : (i : ι) → InfoState i → Option (E.Action i) → PrivateSignal i →
    PublicSignal → InfoState i

namespace InfoSignals

/-- The information state a history leaves player `i` in. This is the only
bridge from execution data to information data, and it is a recursion over the
history rather than a function of the state reached: two different histories
reaching the same state may leave a player differently informed, and two
histories reaching different states may leave it identically informed. -/
def infoOf (S : InfoSignals E) (i : ι) :
    {state : E.State} → Trace E state → S.InfoState i
  | _, .start => S.initInfo i (S.initialPrivate i) S.initialPublic
  | _, .extend prior joint isLegal realized =>
      S.pushInfo i (infoOf S i prior) (joint i)
        (S.privateSignal i ⟨_, joint, isLegal, _, realized⟩)
        (S.publicSignal ⟨_, joint, isLegal, _, realized⟩)

variable (S : InfoSignals E)

@[simp]
theorem infoOf_start (i : ι) :
    S.infoOf i (Trace.start : Trace E E.init) =
      S.initInfo i (S.initialPrivate i) S.initialPublic := by
  rw [infoOf]

@[simp]
theorem infoOf_extend (i : ι) {source target : E.State} (prior : Trace E source)
    (joint : ∀ j, Option (E.Action j)) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    S.infoOf i (.extend prior joint isLegal realized) =
      S.pushInfo i (S.infoOf i prior) (joint i)
        (S.privateSignal i ⟨source, joint, isLegal, target, realized⟩)
        (S.publicSignal ⟨source, joint, isLegal, target, realized⟩) := by
  rw [infoOf]

end InfoSignals

set_option linter.checkUnivs false in
/-- An information model: observations, information states, and the legal menu
each information state determines.

`menu_adequate` is the load-bearing field. It says the information-local menu is
*exactly* the protocol's legal option set at every history producing that
information state — so a policy that respects the menu is legal, and a policy
never has to consult the execution state to find out what it may do. -/
structure InformationModel (E : ExecutionProtocol ι) extends InfoSignals E where
  /-- The options a player faces, as a function of its information state alone.
  `none` means "do not move", so this also encodes whether the player is
  active. -/
  menu : (i : ι) → InfoState i → Set (Option (E.Action i))
  /-- Menu adequacy: after any history, the information-local menu and the
  protocol's per-player legal options agree. Quantifying over hidden states is
  what a *law* is for; the `menu` field itself never receives one. -/
  menu_adequate : ∀ (i : ι) {state : E.State} (trace : Trace E state)
      (choice : Option (E.Action i)),
    choice ∈ menu i (toInfoSignals.infoOf i trace) ↔ LegalOption E state i choice

namespace InformationModel

variable (M : InformationModel E)

/-! ## Information-local policies

The whole point of the module is the type below: it has no `E.State` argument,
so information locality is not a theorem about policies — it is the reason a
non-local policy cannot be written. -/

/-- A player's policy: a choice from its own menu, given only its own
information state. -/
def Policy (i : ι) : Type _ :=
  (info : M.InfoState i) → { choice : Option (E.Action i) // choice ∈ M.menu i info }

/-- A policy that also reads a correlated device's recommendation. The
recommendation is one more information-local input; it is still not the
execution state. -/
def RecommendedPolicy (Recommendation : ι → Type ur) (i : ι) : Type _ :=
  Recommendation i → M.Policy i

variable {M}

/-- The action a policy takes, forgetting the menu certificate. Its codomain
does not depend on the information state, which is what makes locality a plain
`congrArg`. -/
def Policy.act {i : ι} (policy : M.Policy i) (info : M.InfoState i) :
    Option (E.Action i) := (policy info).1

/-- A policy's action is always in its menu. -/
theorem Policy.act_mem_menu {i : ι} (policy : M.Policy i) (info : M.InfoState i) :
    policy.act info ∈ M.menu i info := (policy info).2

/-- **Locality, by construction.** Two histories a player cannot tell apart get
the same action from *every* policy, and the proof is congruence of a function
application. No policy can be given that violates this, because no policy has a
state to branch on. -/
theorem Policy.act_eq_of_infoOf_eq {i : ι} (policy : M.Policy i)
    {first second : E.State} (traceFirst : Trace E first) (traceSecond : Trace E second)
    (hinfo : M.infoOf i traceFirst = M.infoOf i traceSecond) :
    policy.act (M.infoOf i traceFirst) = policy.act (M.infoOf i traceSecond) :=
  congrArg policy.act hinfo

variable (M)

/-- The joint action a profile of information-local policies takes after a
history: each coordinate is computed from that player's own information state,
and the state the history reached is never passed to a policy. -/
def jointAt (policies : (i : ι) → M.Policy i) {state : E.State} (trace : Trace E state) :
    ∀ i, Option (E.Action i) :=
  fun i => (policies i).act (M.infoOf i trace)

/-- Information-local policies still drive execution: wherever play has not
stopped, their joint action is legal. Menu adequacy is exactly what turns local
choices into a legal joint action, so no policy needs a state to stay legal. -/
theorem jointAt_legal (policies : (i : ι) → M.Policy i) {state : E.State}
    (trace : Trace E state) (hterm : ¬ E.terminal state) :
    E.Legal state (M.jointAt policies trace) :=
  ExecutionProtocol.legal_of_legalOption hterm fun i =>
    (M.menu_adequate i trace ((policies i).act (M.infoOf i trace))).mp
      ((policies i).act_mem_menu (M.infoOf i trace))

/-! ## Information sets and beliefs

Beliefs are analyst-level objects: unlike policies they may name execution
states, because that is what a belief is about. -/

/-- The execution states a player can be at while holding `info`: those reached
by some history that produces `info`. This is the information set, derived from
histories rather than postulated as a partition of states. -/
def InfoSet (i : ι) (info : M.InfoState i) : Set E.State :=
  { state | ∃ trace : Trace E state, M.infoOf i trace = info }

/-- A history's own state lies in the information set it produces. -/
theorem mem_infoSet {i : ι} {state : E.State} (trace : Trace E state) :
    state ∈ M.InfoSet i (M.infoOf i trace) := ⟨trace, rfl⟩

/-- The one information-local menu is the legal option set at *every* state the
player considers possible. This is what conditional reasoning at an information
set needs, and it needs no state-indexed menu and no equivalence relation on
states. -/
theorem legalOption_of_mem_menu {i : ι} (info : M.InfoState i) {state : E.State}
    (hstate : state ∈ M.InfoSet i info) (choice : Option (E.Action i)) :
    choice ∈ M.menu i info ↔ LegalOption E state i choice := by
  obtain ⟨trace, rfl⟩ := hstate
  exact M.menu_adequate i trace choice

/-- A belief at an information state is a finite-support law on the states that
information state leaves open. -/
def BeliefOn (i : ι) (info : M.InfoState i) (belief : FinDist E.State) : Prop :=
  belief.support ⊆ M.InfoSet i info

/-- Sequential feasibility: a policy's action is legal at every state a
supported belief considers possible. The policy still never saw one. -/
theorem legalOption_of_beliefOn {i : ι} {info : M.InfoState i} {belief : FinDist E.State}
    (hbelief : M.BeliefOn i info belief) (policy : M.Policy i) {state : E.State}
    (hstate : state ∈ belief.support) :
    LegalOption E state i (policy.act info) :=
  (M.legalOption_of_mem_menu info (hbelief hstate) (policy.act info)).mp
    (policy.act_mem_menu info)

end InformationModel

end GameTheory.Protocol
