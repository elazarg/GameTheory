/-
# Information models

The information layer. `GameTheory.Protocol.Execution` owns transitions;
this module owns *who sees what*. It never redefines a transition: every
observation is emitted by a `StepEvent`, which is exactly the data of one
realized legal step, and the initial views are the only other source.

A strategy must not be able to see hidden execution state at an information
set, and locality must not rest on a proposition proved after the fact. Three
design choices secure that.

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
  Adequacy ranges over terminal histories too.  Although execution never asks
  for an action after stopping, terminal activity still determines
  `LegalOption`; histories sharing an information state must therefore agree on
  that activity/menu shape, including terminal histories.
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
remembers.  That is a history-sufficiency or Markov property, distinct from
perfect recall: perfect recall constrains how a player's information evolves
across its own earlier observations and actions.

The signal fields and the menu law are split into two structures because the
adequacy law must mention `infoOf`, and `infoOf` is a recursion over the signal
fields. `InformationModel extends InfoSignals` keeps that a private detail:
`M.InfoState`, `M.pushInfo`, and `M.infoOf` all resolve through the parent.
-/

import GameTheory.Protocol.Randomized
import GameTheory.Core.Signature
import GameTheory.Math.Probability.Product

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability ExecutionProtocol

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

-- Public signals, private signals, information states, and protocol actions are
-- independently sized; the linter sees them only through this combined record.

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

/-! ### Being asked twice at one information state

A player asked to act twice at one information state cannot be committed by a
single draw made in advance: a policy answers that information state once and
for all, while a player randomizing locally draws again. The predicate below
names the condition that rules this out.

This is stated separately from recall because later correspondence theorems
need precisely the no-revisit consequence. With the own-play formulation
below, perfect recall implies it; the converse need not hold. -/

/-- The information states at which a player has acted along a history, most
recent first. Passing through an information state without moving does not
count: only a contribution of `some` action is a decision. -/
def actedAt (S : InfoSignals E) (i : ι) :
    {state : E.State} → Trace E state → List (S.InfoState i)
  | _, .start => []
  | _, .extend prior joint _ _ =>
      match joint i with
      | some _ => S.infoOf i prior :: S.actedAt i prior
      | none => S.actedAt i prior

@[simp]
theorem actedAt_start (S : InfoSignals E) (i : ι) :
    S.actedAt i (Trace.start : Trace E E.init) = [] := rfl

/-- What a player has done, and where: the information state it held and the
action it took, at each of its own moves, most recent first. -/
def ownPlay (S : InfoSignals E) (i : ι) :
    {state : E.State} → Trace E state → List (S.InfoState i × E.Action i)
  | _, .start => []
  | _, .extend prior joint _ _ =>
      match joint i with
      | some action => (S.infoOf i prior, action) :: S.ownPlay i prior
      | none => S.ownPlay i prior

@[simp]
theorem ownPlay_extend (S : InfoSignals E) (i : ι) {source target : E.State}
    (prior : Trace E source) (joint : ∀ j, Option (E.Action j))
    (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    S.ownPlay i (.extend prior joint isLegal realized) =
      match joint i with
      | some action => (S.infoOf i prior, action) :: S.ownPlay i prior
      | none => S.ownPlay i prior := by
  rw [ownPlay]

/-- The record of *where* a player acted is that record with the actions
forgotten. -/
theorem actedAt_eq_map_ownPlay (S : InfoSignals E) (i : ι) :
    ∀ {state : E.State} (trace : Trace E state),
      S.actedAt i trace = (S.ownPlay i trace).map Prod.fst
  | _, .start => rfl
  | _, .extend prior joint _ _ => by
    show (match joint i with
        | some _ => S.infoOf i prior :: S.actedAt i prior
        | none => S.actedAt i prior) =
      List.map Prod.fst (match joint i with
        | some action => (S.infoOf i prior, action) :: S.ownPlay i prior
        | none => S.ownPlay i prior)
    cases joint i with
    | none => exact S.actedAt_eq_map_ownPlay i prior
    | some action => rw [List.map_cons, S.actedAt_eq_map_ownPlay i prior]

/-- Every recorded information state comes from an earlier trace, before a
strictly shorter record of the player's own actions. -/
private theorem exists_prior_ownPlay_length_lt_of_mem_actedAt
    (S : InfoSignals E) (i : ι) :
    ∀ {state : E.State} (trace : Trace E state) {info : S.InfoState i},
      info ∈ S.actedAt i trace →
        ∃ (priorState : E.State) (prior : Trace E priorState),
          S.infoOf i prior = info ∧
            (S.ownPlay i prior).length < (S.ownPlay i trace).length
  | _, .start, _, hmem => by simp only [actedAt_start, List.not_mem_nil] at hmem
  | _, .extend prior joint isLegal realized, info, hmem => by
      cases hchoice : joint i with
      | none =>
          simp only [actedAt, hchoice] at hmem
          obtain ⟨priorState, earlier, hinfo, hlength⟩ :=
            S.exists_prior_ownPlay_length_lt_of_mem_actedAt i prior hmem
          refine ⟨priorState, earlier, hinfo, ?_⟩
          simpa only [ownPlay, hchoice] using hlength
      | some action =>
          simp only [actedAt, hchoice, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · refine ⟨_, prior, rfl, ?_⟩
            simp only [ownPlay, hchoice, List.length_cons]
            omega
          · obtain ⟨priorState, earlier, hinfo, hlength⟩ :=
              S.exists_prior_ownPlay_length_lt_of_mem_actedAt i prior hmem
            refine ⟨priorState, earlier, hinfo, ?_⟩
            simp only [ownPlay, hchoice, List.length_cons]
            omega

/-- **Perfect recall.** A player reaching one information state by two histories
has done the same things along both: the same information states, the same
actions, in the same order. What it may forget is what others did, never its own
part of the play.

This is a property of `infoOf`, not a field, and it is stated over the record a
player's own moves leave rather than over the histories themselves. That is what
makes a set of policies consistent with an information state a function of that
information state alone. -/
def PerfectRecall : Prop :=
  ∀ (i : ι) {first second : E.State} (traceFirst : Trace E first)
    (traceSecond : Trace E second),
    S.infoOf i traceFirst = S.infoOf i traceSecond →
      S.ownPlay i traceFirst = S.ownPlay i traceSecond

/-- Recalling the actions implies recalling where they were taken. -/
theorem actedAt_eq_of_perfectRecall (hrecall : S.PerfectRecall) (i : ι)
    {first second : E.State} (traceFirst : Trace E first) (traceSecond : Trace E second)
    (hinfo : S.infoOf i traceFirst = S.infoOf i traceSecond) :
    S.actedAt i traceFirst = S.actedAt i traceSecond := by
  rw [S.actedAt_eq_map_ownPlay i traceFirst, S.actedAt_eq_map_ownPlay i traceSecond,
    hrecall i traceFirst traceSecond hinfo]

/-- **No player is ever asked to act twice at one information state.** Stated
over histories, so it constrains realized play rather than the syntax of the
protocol: a state may recur freely as long as the player's information about it
does not. -/
def ActsOnceAtEachInfoState : Prop :=
  ∀ (i : ι) {state : E.State} (trace : Trace E state), (S.actedAt i trace).Nodup

/-- Perfect recall prevents a player from acting twice at the same information
state: revisiting it after an action would require its current own-play record
to equal a strictly shorter earlier record. -/
theorem PerfectRecall.actsOnceAtEachInfoState (hrecall : S.PerfectRecall) :
    S.ActsOnceAtEachInfoState := by
  intro i state trace
  induction trace with
  | start => simp [actedAt]
  | @extend source target prior joint isLegal realized ih =>
      cases hchoice : joint i with
      | none => simpa only [actedAt, hchoice] using ih
      | some action =>
          simp only [actedAt, hchoice, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hmem
          obtain ⟨priorState, earlier, hinfo, hlength⟩ :=
            S.exists_prior_ownPlay_length_lt_of_mem_actedAt i prior hmem
          have hequal := hrecall i earlier prior hinfo
          rw [hequal] at hlength
          exact (Nat.lt_irrefl _ hlength)

end InfoSignals

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
  /-- Menu adequacy: after any history, including a terminal history, the
  information-local menu and the protocol's per-player legal options agree.
  Quantifying over hidden states is what a *law* is for; the `menu` field itself
  never receives one.  Consequently, histories with the same information state
  must agree on activity even after execution has stopped. -/
  menu_adequate : ∀ (i : ι) {state : E.State} (trace : Trace E state)
      (choice : Option (E.Action i)),
    choice ∈ menu i (toInfoSignals.infoOf i trace) ↔ LegalOption E state i choice

-- The model preserves every independent universe inherited from `InfoSignals`
-- and `ExecutionProtocol`; the linter sees them only through this extension.

namespace InformationModel

variable (M : InformationModel E)

/-! ## Information-local policies

The whole point of the module is the type below: it has no `E.State` argument,
so information locality is not a theorem about policies — it is the reason a
non-local policy cannot be written. -/

/-- What a player may do at an information state. Legality rides on the type, so
nothing built from `Choice` — deterministic, randomizing, or correlated — can
name an action outside the menu. -/
abbrev Choice (i : ι) (info : M.InfoState i) : Type _ :=
  { choice : Option (E.Action i) // choice ∈ M.menu i info }

/-- A menu with at most one option leaves no meaningful policy choice at that
information state.  This is stated directly over the information-local menu so
bridges need not recover inactivity merely to use a singleton-menu fact. -/
theorem subsingleton_choice_of_menu_subsingleton {i : ι} (info : M.InfoState i)
    (hmenu : (M.menu i info).Subsingleton) : Subsingleton (M.Choice i info) :=
  ⟨fun first second => Subtype.ext (hmenu first.2 second.2)⟩

/-- A player's policy: a choice from its own menu, given only its own
information state.  This is a transparent presentation so generic product
constructions can reuse the canonical dependent-function instances. -/
abbrev Policy (i : ι) : Type _ := (info : M.InfoState i) → M.Choice i info

/-- Turn one information-local choice by the unique mover into a legal joint
action.  Every other coordinate is inactive and therefore contributes `none`.
-/
def jointOfChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} := by
  let joint := E.singletonJoint who choice.1
  refine ⟨joint, ExecutionProtocol.legal_of_legalOption hterm fun i => ?_⟩
  by_cases hi : i = who
  · subst i
    simpa [joint] using
      (M.menu_adequate who history.trace choice.1).mp choice.2
  · have hinactive : ¬ E.active history.state i := fun hactive' =>
      hi (singleMover history.state hactive' hactive)
    simpa [joint, hi, LegalOption] using hinactive

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

/-- Change one information-local choice and leave every other information state
untouched. The dependent coordinate is split and reassembled by an equivalence,
so no transport appears in the public operation. -/
def Policy.replaceAt {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.Policy i) (info : M.InfoState i) (choice : M.Choice i info) :
    M.Policy i :=
  (Equiv.piSplitAt info fun w => M.Choice i w).symm
    (choice, fun w => policy w.1)

@[simp]
theorem Policy.replaceAt_self {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.Policy i) (info : M.InfoState i) (choice : M.Choice i info) :
    policy.replaceAt info choice info = choice := by
  simp [Policy.replaceAt]

@[simp]
theorem Policy.replaceAt_of_ne {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.Policy i) (info : M.InfoState i) (choice : M.Choice i info)
    {other : M.InfoState i} (hne : other ≠ info) :
    policy.replaceAt info choice other = policy other := by
  simp [Policy.replaceAt, hne]

@[simp]
theorem Policy.replaceAt_eq_self {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.Policy i) (info : M.InfoState i) :
    policy.replaceAt info (policy info) = policy := by
  funext other
  by_cases hsame : other = info
  · subst other
    exact policy.replaceAt_self info (policy info)
  · exact policy.replaceAt_of_ne info (policy info) hsame

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

/-- A player's own record only grows as play continues. -/
theorem ownPlay_isSuffix_of_reachesWithin (i : ι) :
    ∀ {fuel : ℕ} {h target : E.History}, ExecutionProtocol.ReachesWithin E fuel h target →
      (M.ownPlay i h.trace) <:+ (M.ownPlay i target.trace) := by
  intro fuel h target hreach
  induction hreach with
  | refl => exact List.suffix_refl _
  | step joint isLegal realized rest ih =>
    refine List.IsSuffix.trans ?_ ih
    show (M.ownPlay i _) <:+ M.ownPlay i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.ownPlay_extend]
    cases joint i with
    | none => exact List.suffix_refl _
    | some action => exact List.suffix_cons _ _

/-- Under perfect recall, an information state at which the player acts cannot
reappear after that action.  This is the history-antichain fact needed to
interpret normalized reach mass as conditional probability rather than an
occupancy frequency. -/
theorem infoOf_ne_of_perfectRecall_after_step
    (hrecall : M.PerfectRecall) (i : ι)
    {h later : E.History} {fuel : ℕ}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    {reached : E.State}
    (realized : reached ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    (hactive : E.active h.state i)
    (hreach : E.ReachesWithin fuel (h.extend isLegal realized) later) :
    M.infoOf i later.trace ≠ M.infoOf i h.trace := by
  intro hinfo
  obtain ⟨action, haction⟩ :=
    (E.legalOption_of_legal isLegal i).exists_eq_some_of_active (joint i) hactive
  have hsuffix := M.ownPlay_isSuffix_of_reachesWithin i hreach
  have hlength := hsuffix.length_le
  have hown := hrecall i h.trace later.trace hinfo.symm
  simp only [History.extend, InfoSignals.ownPlay_extend, haction,
    List.length_cons] at hlength
  rw [← hown] at hlength
  omega

/-! ## Playing a profile

A profile of information-local policies can be *run*, because the runner it
drives is indexed by history — the same thing the policies read. A state-indexed
runner could not take one, since two histories reaching one state may leave the
players knowing different things and so calling for different actions. -/

/-- A profile of information-local policies, as a chooser. The state a history
reached is available here and is deliberately not passed on. -/
def historyChooser (policies : (i : ι) → M.Policy i) : E.HistoryChooser :=
  fun h hterm => ⟨M.jointAt policies h.trace, M.jointAt_legal policies h.trace hterm⟩

/-- The law over histories a profile induces from a given history. -/
def runFrom (policies : (i : ι) → M.Policy i) (fuel : ℕ) (h : E.History) : PMF E.History :=
  E.runHistoryFor (M.historyChooser policies) fuel h

/-- The law over histories a profile induces from the start of play. -/
def run (policies : (i : ι) → M.Policy i) (fuel : ℕ) : PMF E.History :=
  M.runFrom policies fuel E.initHistory

/-- Only the actions a profile takes matter, not the certificates witnessing
that they were on the menu. -/
theorem runFrom_congr {first second : (i : ι) → M.Policy i}
    (hagree : ∀ (i : ι) (info : M.InfoState i), (first i).act info = (second i).act info)
    (fuel : ℕ) (h : E.History) : M.runFrom first fuel h = M.runFrom second fuel h :=
  ExecutionProtocol.runHistoryFor_congr
    (fun _ _ => Subtype.ext (funext fun i => hagree i _)) fuel h

/-! ### What a run can consult

A profile is consulted at every player and every history the run passes
through, but where a player is inactive its menu is the single option `none`, so
only the information states at which it *acts* can affect anything. The theorem
below is the corresponding congruence: agreeing where the run can reach is
enough, and behaviour elsewhere is unobservable rather than merely unused. -/

/-- Profiles that answer alike at every history a run of this length can pass
through induce the same law. -/
theorem runFrom_congr_of_act_eq {first second : (i : ι) → M.Policy i} :
    ∀ (fuel : ℕ) (h : E.History),
      (∀ (h' : E.History), ExecutionProtocol.ReachesWithin E fuel h h' → ¬ E.terminal h'.state →
        ∀ i, (first i).act (M.infoOf i h'.trace) = (second i).act (M.infoOf i h'.trace)) →
      M.runFrom first fuel h = M.runFrom second fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h _; rfl
  | succ fuel ih =>
    intro h hagree
    by_cases hterm : E.terminal h.state
    · rw [runFrom, runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm,
        ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
    · have hhere : M.historyChooser first h hterm = M.historyChooser second h hterm :=
        Subtype.ext (funext fun i => hagree h (.refl _ _) hterm i)
      rw [runFrom, runFrom,
        ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm,
        ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm, hhere]
      refine bindOnSupport_congr _ fun target realized => ?_
      exact ih _ fun h' hreach hterm' i => hagree h' (.step _ _ realized hreach) hterm' i

/-! ### Acting twice, and what forbids it

`ActsOnceAtEachInfoState` is stated as a list being duplicate-free. The two
facts below turn that into the form an argument uses: a player's record of where
it has acted only grows along play, and so an information state it has already
acted at never comes back. -/

/-- A player's record of where it has acted only grows as play continues. -/
theorem actedAt_isSuffix_of_reachesWithin (i : ι) :
    ∀ {fuel : ℕ} {h target : E.History}, ExecutionProtocol.ReachesWithin E fuel h target →
      (M.actedAt i h.trace) <:+ (M.actedAt i target.trace) := by
  intro fuel h target hreach
  induction hreach with
  | refl => exact List.suffix_refl _
  | step joint isLegal realized rest ih =>
    refine List.IsSuffix.trans ?_ ih
    show (M.actedAt i _) <:+ M.actedAt i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.actedAt]
    cases joint i with
    | none => exact List.suffix_refl _
    | some action => exact List.suffix_cons _ _

/-- **No player is asked twice at one information state where the choice
matters.** A repeat is harmless when the menu there holds a single option:
there is nothing to draw, so drawing again cannot differ from drawing once.

The condition is stated over the menu rather than over the action carrier,
which is both the semantically right site and strictly finer — an information
state can offer a rich set of actions and still leave the player one legal
option. -/
def ActsOnceWhereItMatters : Prop :=
  ∀ (i : ι) {state : E.State} (trace : Trace E state),
    (M.actedAt i trace).Pairwise fun later earlier =>
      later ≠ earlier ∨ Subsingleton (M.Choice i earlier)

/-- Never acting twice at one information state is the special case that ignores
the menu. -/
theorem actsOnceWhereItMatters_of_actsOnce (hactsOnce : M.ActsOnceAtEachInfoState) :
    M.ActsOnceWhereItMatters := fun i _ trace =>
  (hactsOnce i trace).imp fun hne => Or.inl hne

variable {M} in
/-- Perfect recall supplies the no-revisit condition needed to pre-draw local
behavioral choices. -/
theorem actsOnceWhereItMatters_of_perfectRecall (hrecall : M.PerfectRecall) :
    M.ActsOnceWhereItMatters :=
  M.actsOnceWhereItMatters_of_actsOnce hrecall.actsOnceAtEachInfoState

/-- **An information state a player has acted at does not return, unless there
was nothing to choose there.** This is the form the condition is used in: having
moved at `h`, the player either never meets that information state again while
moving, or meets it with a single option on the menu. -/
theorem infoOf_ne_or_subsingleton_of_actsOnce (hactsOnce : M.ActsOnceWhereItMatters) (i : ι)
    {h later : E.History} {fuel : ℕ}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    {reached : E.State} (realized : reached ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    (hacts : (joint i).isSome)
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    {laterJoint : ∀ j, Option (E.Action j)} (laterLegal : E.Legal later.state laterJoint)
    {laterReached : E.State}
    (laterRealized : laterReached ∈ (E.step later.state ⟨laterJoint, laterLegal⟩).support)
    (hactsLater : (laterJoint i).isSome) :
    M.infoOf i later.trace ≠ M.infoOf i h.trace ∨
      Subsingleton (M.Choice i (M.infoOf i h.trace)) := by
  have hpairwise := hactsOnce i (later.extend laterLegal laterRealized).trace
  have hstep : M.actedAt i (later.extend laterLegal laterRealized).trace =
      M.infoOf i later.trace :: M.actedAt i later.trace := by
    show M.actedAt i (Trace.extend _ laterJoint laterLegal laterRealized) = _
    rw [InfoSignals.actedAt]
    cases hcase : laterJoint i with
    | none => rw [hcase] at hactsLater; exact absurd hactsLater (by simp)
    | some action => rfl
  rw [hstep] at hpairwise
  refine (List.pairwise_cons.mp hpairwise).1 _ ?_
  have hsuffix := M.actedAt_isSuffix_of_reachesWithin i hreach
  have hhead : M.infoOf i h.trace ∈ M.actedAt i (h.extend isLegal realized).trace := by
    show M.infoOf i h.trace ∈ M.actedAt i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.actedAt]
    cases hcase : joint i with
    | none => rw [hcase] at hacts; exact absurd hacts (by simp)
    | some action => exact List.mem_cons_self
  exact hsuffix.subset hhead

/-- **An inactive player has nothing to choose.** Its menu is the single option
`none`, so every law over its choices at that information state is the same law.
A commitment made there is therefore invisible without any argument about what
play does next — which is what covers the players a step did not ask to move. -/
theorem subsingleton_choice_of_not_active {i : ι} {state : E.State} (trace : Trace E state)
    (hinactive : ¬ E.active state i) : Subsingleton (M.Choice i (M.infoOf i trace)) :=
  ⟨fun first second => Subtype.ext <| by
    rw [LegalOption.eq_none_of_inactive first.1
        ((M.menu_adequate i trace first.1).mp first.2) hinactive,
      LegalOption.eq_none_of_inactive second.1
        ((M.menu_adequate i trace second.1).mp second.2) hinactive]⟩

/-! ## Randomizing

There are two places a player can put its randomness: at each information state
separately, or once over whole policies. Both are built from the same `Choice`,
so neither can name an illegal action, and both agree with a deterministic
policy when every law is a point mass.

Whether the two agree with *each other* is a different question, and it turns on
whether play can return a player to an information state it has already acted
at. A behavioral policy draws afresh on the second visit; a mixed policy is
committed by its single draw. -/

/-- Local randomization: one law over its own menu at each information state.
This is transparent for the same reason as `Policy`: coordinatewise product
constructions should inherit the canonical dependent-function API. -/
abbrev BehavioralPolicy (i : ι) : Type _ :=
  (info : M.InfoState i) → PMF (M.Choice i info)

/-- The signature for local randomization at information states. It has the
same history outcomes as the pure-policy strategic form. -/
abbrev behavioralSignature : GameSignature ι where
  Strategy := M.BehavioralPolicy
  Outcome := E.History

/-- Global randomization: one law over deterministic policies. -/
abbrev MixedPolicy (i : ι) : Type _ := PMF (M.Policy i)

variable {M} in
/-- A deterministic policy read as a behavioral one that never really
randomizes. -/
def Policy.toBehavioral {i : ι} (policy : M.Policy i) : M.BehavioralPolicy i :=
  fun info => PMF.pure (policy info)

/-- Hence any two behavioral policies agree there. -/
theorem behavioral_eq_of_not_active {i : ι} (first second : M.BehavioralPolicy i)
    {state : E.State} (trace : Trace E state) (hinactive : ¬ E.active state i) :
    first (M.infoOf i trace) = second (M.infoOf i trace) := by
  have := M.subsingleton_choice_of_not_active trace hinactive
  obtain ⟨choice⟩ : Nonempty (M.Choice i (M.infoOf i trace)) :=
    ⟨⟨none, (M.menu_adequate i trace none).mpr hinactive⟩⟩
  rw [eq_pure_of_subsingleton (first (M.infoOf i trace)) choice,
    eq_pure_of_subsingleton (second (M.infoOf i trace)) choice]

section Profiles

variable [Fintype ι]

/-- The law over legal joint actions a behavioral profile induces after a
history: every player draws from its own menu, and the draws are independent
because nothing couples them. Menu adequacy is what makes each drawn joint
action legal, so randomizing needs no legality argument the deterministic case
did not already have. -/
def behavioralJoint (policies : (i : ι) → M.BehavioralPolicy i) {state : E.State}
    (trace : Trace E state) (hterm : ¬ E.terminal state) :
    PMF { joint : ∀ i, Option (E.Action i) // E.Legal state joint } :=
  PMF.map
    (fun draws => ⟨fun i => (draws i).1,
      ExecutionProtocol.legal_of_legalOption hterm fun i =>
        (M.menu_adequate i trace (draws i).1).mp (draws i).2⟩)
    (independentProduct fun i => policies i (M.infoOf i trace))

/-- Behavioral profiles that agree at one information history induce the same
local joint-action law there.  This is the one-step congruence used by the
global runner theorem below. -/
theorem behavioralJoint_congr {first second : (i : ι) → M.BehavioralPolicy i}
    {state : E.State} (trace : Trace E state) (hterm : ¬ E.terminal state)
    (hagree : ∀ i, first i (M.infoOf i trace) = second i (M.infoOf i trace)) :
    M.behavioralJoint first trace hterm = M.behavioralJoint second trace hterm := by
  rw [behavioralJoint, behavioralJoint]
  exact congrArg _ (congrArg independentProduct (funext hagree))

/-- A legal joint action belongs to the behavioral joint support whenever each
of its local choices belongs to the corresponding behavioral support. -/
theorem mem_support_behavioralJoint
    (policies : (i : ι) → M.BehavioralPolicy i)
    {state : E.State} (trace : Trace E state)
    (hterm : ¬ E.terminal state)
    (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal state joint)
    (hsupport : ∀ i,
      (⟨joint i, (M.menu_adequate i trace (joint i)).mpr
        (E.legalOption_of_legal isLegal i)⟩ :
        M.Choice i (M.infoOf i trace)) ∈
          (policies i (M.infoOf i trace)).support) :
    (⟨joint, isLegal⟩ : { action : ∀ i, Option (E.Action i) //
      E.Legal state action }) ∈
        (M.behavioralJoint policies trace hterm).support := by
  let draws : (i : ι) → M.Choice i (M.infoOf i trace) :=
    fun i => ⟨joint i, (M.menu_adequate i trace (joint i)).mpr
      (E.legalOption_of_legal isLegal i)⟩
  rw [behavioralJoint, PMF.support_map]
  refine ⟨draws,
    (independentProduct_support_iff
      (fun i => policies i (M.infoOf i trace)) draws).mpr ?_, ?_⟩
  · exact hsupport
  · apply Subtype.ext
    rfl

section SingleMoverBehavioralJoint

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- If nobody acts, the behavioral product is the unique all-`none` joint
action. -/
theorem behavioralJoint_eq_pure_of_no_active
    (policies : (i : ι) → M.BehavioralPolicy i)
    {state : E.State} (trace : E.Trace state)
    (hterminal : ¬ E.terminal state)
    (hinactive : ∀ i, ¬ E.active state i) :
    M.behavioralJoint policies trace hterminal =
      PMF.pure
        ⟨fun _ => none,
          ExecutionProtocol.legal_of_legalOption hterminal
            hinactive⟩ := by
  let idle :
      (i : ι) → M.Choice i (M.infoOf i trace) :=
    fun i => ⟨none, (M.menu_adequate i trace none).mpr
      (hinactive i)⟩
  have hpolicy (i : ι) :
      policies i (M.infoOf i trace) =
        PMF.pure (idle i) := by
    have : Subsingleton (M.Choice i (M.infoOf i trace)) :=
      M.subsingleton_choice_of_not_active trace (hinactive i)
    exact eq_pure_of_subsingleton _ (idle i)
  unfold behavioralJoint
  simp_rw [hpolicy]
  rw [independentProduct_pure, PMF.pure_map]

/-- If at most one player can act, the behavioral product is that player's
local law embedded in the only possibly active joint coordinate. -/
theorem behavioralJoint_eq_map_of_at_most_one_active
    (policies : (i : ι) → M.BehavioralPolicy i)
    {state : E.State} (trace : E.Trace state)
    (hterminal : ¬ E.terminal state)
    (active : ι)
    (hunique : ∀ i, E.active state i → i = active) :
    M.behavioralJoint policies trace hterminal =
      PMF.map
        (fun choice : M.Choice active (M.infoOf active trace) =>
          ⟨E.singletonJoint active choice.1,
            ExecutionProtocol.legal_of_legalOption hterminal
              fun other => by
                by_cases howner : other = active
                · subst other
                  simpa using
                    (M.menu_adequate active trace choice.1).mp
                      choice.2
                · have hinactive : ¬ E.active state other := by
                    intro hother
                    exact howner (hunique other hother)
                  simpa only [ExecutionProtocol.singletonJoint, howner,
                    dite_false, LegalOption]
                    using hinactive⟩)
        (policies active (M.infoOf active trace)) := by
  let embed : M.Choice active (M.infoOf active trace) →
      { joint : ∀ i, Option (E.Action i) // E.Legal state joint } :=
    fun choice =>
      ⟨E.singletonJoint active choice.1,
        ExecutionProtocol.legal_of_legalOption hterminal fun other => by
          by_cases howner : other = active
          · subst other
            simpa using (M.menu_adequate active trace choice.1).mp choice.2
          · have hinactive : ¬ E.active state other := by
              intro hother
              exact howner (hunique other hother)
            simpa only [ExecutionProtocol.singletonJoint, howner,
              dite_false, LegalOption] using hinactive⟩
  let assemble : ((i : ι) → M.Choice i (M.infoOf i trace)) →
      { joint : ∀ i, Option (E.Action i) // E.Legal state joint } :=
    fun draws => ⟨fun i => (draws i).1,
      ExecutionProtocol.legal_of_legalOption hterminal fun i =>
        (M.menu_adequate i trace (draws i).1).mp (draws i).2⟩
  have hcollapse (draws : (i : ι) → M.Choice i (M.infoOf i trace)) :
      assemble draws = embed (draws active) := by
    apply Subtype.ext
    funext other
    by_cases howner : other = active
    · subst other
      simp [assemble, embed, ExecutionProtocol.singletonJoint]
    · have hinactive : ¬ E.active state other := by
        intro hother
        exact howner (hunique other hother)
      have hnone := LegalOption.eq_none_of_inactive (draws other).1
        ((M.menu_adequate other trace (draws other).1).mp (draws other).2)
        hinactive
      simp [assemble, embed, ExecutionProtocol.singletonJoint, howner, hnone]
  have hfunctions : assemble = embed ∘ (fun draws => draws active) := by
    funext draws
    exact hcollapse draws
  calc
    M.behavioralJoint policies trace hterminal =
        PMF.map assemble
          (independentProduct fun i => policies i (M.infoOf i trace)) := rfl
    _ = PMF.map (embed ∘ fun draws => draws active)
          (independentProduct fun i => policies i (M.infoOf i trace)) := by
      rw [hfunctions]
    _ = PMF.map embed
          ((independentProduct fun i => policies i (M.infoOf i trace)).map
            (fun draws => draws active)) := (PMF.map_comp _ _ _).symm
    _ = PMF.map embed (policies active (M.infoOf active trace)) := by
      rw [independentProduct_map_eval]
    _ = _ := rfl

end SingleMoverBehavioralJoint

/-- A behavioral profile, as a chooser. -/
def randomizedChooser (policies : (i : ι) → M.BehavioralPolicy i) : E.RandomizedChooser :=
  fun h hterm => M.behavioralJoint policies h.trace hterm

/-- The law over histories a behavioral profile induces from a given history. -/
def runBehavioralFrom (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) (h : E.History) :
    PMF E.History :=
  E.runRandomizedFor (M.randomizedChooser policies) fuel h

/-- Behavioral play started from a terminal history is absorbed there for
every fuel amount. -/
@[simp]
theorem runBehavioralFrom_of_terminal
    (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) {h : E.History}
    (hterm : E.terminal h.state) :
    M.runBehavioralFrom policies fuel h = PMF.pure h :=
  E.runRandomizedFor_of_terminal (M.randomizedChooser policies) fuel hterm

/-- One nonterminal behavioral step first draws the information-local joint
action, then follows the execution transition.  Keeping this unfolding at the
behavioral layer avoids repeating the chooser expansion at every bridge. -/
theorem runBehavioralFrom_succ_of_not_terminal
    (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) {h : E.History}
    (hterm : ¬ E.terminal h.state) :
    M.runBehavioralFrom policies (fuel + 1) h =
      (M.behavioralJoint policies h.trace hterm).bind fun draw =>
        (E.step h.state draw).bindOnSupport fun _ realized =>
          M.runBehavioralFrom policies fuel (h.extend draw.2 realized) :=
  E.runRandomizedFor_succ_of_not_terminal (M.randomizedChooser policies) fuel hterm

/-- The law over histories a behavioral profile induces from the start. -/
def runBehavioral (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) : PMF E.History :=
  M.runBehavioralFrom policies fuel E.initHistory

/-- A behavioral profile with full local support reaches every semantically
possible bounded history at some elapsed time within the same fuel budget. -/
theorem exists_mem_support_runBehavioralFrom_of_reachesWithin
    (policies : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i info (choice : M.Choice i info),
      choice ∈ (policies i info).support)
    {fuel : ℕ} {start later : E.History}
    (hreach : E.ReachesWithin fuel start later) :
    ∃ elapsed, elapsed ≤ fuel ∧
      later ∈ (M.runBehavioralFrom policies elapsed start).support := by
  induction hreach with
  | refl fuel history =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      simp [runBehavioralFrom]
  | @step fuel history target joint isLegal reached realized rest ih =>
      obtain ⟨elapsed, helapsed, hlater⟩ := ih
      have hterm : ¬ E.terminal history.state := isLegal.1
      have hdraw :
          (⟨joint, isLegal⟩ : { action : ∀ i, Option (E.Action i) //
            E.Legal history.state action }) ∈
            (M.behavioralJoint policies history.trace hterm).support :=
        M.mem_support_behavioralJoint policies history.trace hterm joint
          isLegal fun i => hfull i _ _
      let next := history.extend isLegal realized
      have hnext :
          next ∈ (M.runBehavioralFrom policies 1 history).support := by
        rw [M.runBehavioralFrom_succ_of_not_terminal policies 0 hterm,
          PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨⟨joint, isLegal⟩, hdraw, ?_⟩
        rw [PMF.support_bindOnSupport]
        refine Set.mem_iUnion₂.mpr ⟨reached, realized, ?_⟩
        simp [next, runBehavioralFrom]
      refine ⟨1 + elapsed, by omega, ?_⟩
      rw [show M.runBehavioralFrom policies (1 + elapsed) history =
          (M.runBehavioralFrom policies 1 history).bind
            (M.runBehavioralFrom policies elapsed) from
        E.runRandomizedFor_add (M.randomizedChooser policies)
          1 elapsed history,
        PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨next, hnext, hlater⟩

/-- Behavioral play composes across adjacent fuel blocks. -/
theorem runBehavioralFrom_add
    (policies : (i : ι) → M.BehavioralPolicy i)
    (firstFuel secondFuel : ℕ) (history : E.History) :
    M.runBehavioralFrom policies (firstFuel + secondFuel) history =
      (M.runBehavioralFrom policies firstFuel history).bind
        (M.runBehavioralFrom policies secondFuel) :=
  E.runRandomizedFor_add (M.randomizedChooser policies)
    firstFuel secondFuel history

/-- A certified horizon reaches only terminal histories, from any starting
history. The horizon bounds total trace length, so it also suffices when some
transitions have already occurred. -/
theorem runBehavioralFrom_terminal_of_bound
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (start next : E.History)
    (hnext : next ∈ (M.runBehavioralFrom profile bound start).support) :
    E.terminal next.state := by
  rcases E.runRandomizedFor_terminal_or_length
      (M.randomizedChooser profile) bound start next hnext with hterminal | hlength
  · exact hterminal
  · exact hbound next.state next.trace (by omega)

/-- Fuel beyond a certified horizon leaves the complete history law unchanged. -/
theorem runBehavioralFrom_bound_add
    (profile : (who : ι) → M.BehavioralPolicy who) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (extra : ℕ) (start : E.History) :
    M.runBehavioralFrom profile (bound + extra) start =
      M.runBehavioralFrom profile bound start := by
  rw [M.runBehavioralFrom_add]
  refine Eq.trans (bind_congr_on_support _ fun next hnext => ?_) (PMF.bind_pure _)
  exact M.runBehavioralFrom_of_terminal profile extra
    (M.runBehavioralFrom_terminal_of_bound profile hbound start next hnext)

/-- Behavioral profiles that answer alike at every history a run of this length
can pass through induce the same law. This is what makes a change to a
coordinate the continuation never consults invisible. -/
theorem runBehavioralFrom_congr {first second : (i : ι) → M.BehavioralPolicy i} :
    ∀ (fuel : ℕ) (h : E.History),
      (∀ (h' : E.History), ExecutionProtocol.ReachesWithin E fuel h h' → ¬ E.terminal h'.state →
        ∀ i, first i (M.infoOf i h'.trace) = second i (M.infoOf i h'.trace)) →
      M.runBehavioralFrom first fuel h = M.runBehavioralFrom second fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h _; rfl
  | succ fuel ih =>
    intro h hagree
    by_cases hterm : E.terminal h.state
    · rw [runBehavioralFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
    · have hhere : M.behavioralJoint first h.trace hterm =
          M.behavioralJoint second h.trace hterm :=
        M.behavioralJoint_congr h.trace hterm fun i => hagree h (.refl _ _) hterm i
      rw [M.runBehavioralFrom_succ_of_not_terminal first fuel hterm,
        M.runBehavioralFrom_succ_of_not_terminal second fuel hterm, hhere]
      refine bind_congr_on_support _ fun draw _ => bindOnSupport_congr _ fun target realized => ?_
      exact ih _ fun h' hreach hterm' i => hagree h' (.step _ _ realized hreach) hterm' i

/-- Behavioral runner congruence on the supports actually exposed by one
bounded run. Unlike `runBehavioralFrom_congr`, this does not quantify over every
legally reachable counterfactual history. -/
theorem runBehavioralFrom_congr_on_support
    {first second : (i : ι) → M.BehavioralPolicy i} :
    ∀ (fuel : ℕ) (start : E.History),
      (∀ elapsed, elapsed ≤ fuel → ∀ later,
        later ∈ (M.runBehavioralFrom first elapsed start).support →
        ¬ E.terminal later.state → ∀ i,
          first i (M.infoOf i later.trace) =
            second i (M.infoOf i later.trace)) →
      M.runBehavioralFrom first fuel start =
        M.runBehavioralFrom second fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _
      rfl
  | succ fuel ih =>
      intro start hagree
      by_cases hterm : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal first _ hterm,
          M.runBehavioralFrom_of_terminal second _ hterm]
      · have hstart :
            start ∈ (M.runBehavioralFrom first 0 start).support := by
          simp [runBehavioralFrom]
        have hhere : M.behavioralJoint first start.trace hterm =
            M.behavioralJoint second start.trace hterm :=
          M.behavioralJoint_congr start.trace hterm fun i =>
            hagree 0 (by omega) start hstart hterm i
        rw [M.runBehavioralFrom_succ_of_not_terminal first fuel hterm,
          M.runBehavioralFrom_succ_of_not_terminal second fuel hterm,
          hhere]
        refine bind_congr_on_support _ fun draw hdraw =>
          bindOnSupport_congr _ fun target realized => ?_
        let next := start.extend draw.2 realized
        have hdrawFirst :
            draw ∈ (M.behavioralJoint first start.trace hterm).support := by
          rw [hhere]
          exact hdraw
        have hnext :
            next ∈ (M.runBehavioralFrom first 1 start).support := by
          rw [M.runBehavioralFrom_succ_of_not_terminal first 0 hterm,
            PMF.support_bind]
          refine Set.mem_iUnion₂.mpr ⟨draw, hdrawFirst, ?_⟩
          rw [PMF.support_bindOnSupport]
          refine Set.mem_iUnion₂.mpr ⟨target, realized, ?_⟩
          simp [next, runBehavioralFrom]
        apply ih next
        intro elapsed helapsed later hlater hlaterTerm i
        apply hagree (1 + elapsed) (by omega) later
        rw [M.runBehavioralFrom_add first 1 elapsed start,
          PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨next, hnext, hlater⟩
        exact hlaterTerm

/-- The law a mixed profile induces: draw a deterministic profile once, then
play it. The single draw is the whole difference from the behavioral case. -/
def runMixedFrom (mixed : (i : ι) → M.MixedPolicy i) (fuel : ℕ) (h : E.History) :
    PMF E.History :=
  (independentProduct mixed).bind fun policies => M.runFrom policies fuel h

/-- The law a mixed profile induces from the start. -/
def runMixed (mixed : (i : ι) → M.MixedPolicy i) (fuel : ℕ) : PMF E.History :=
  M.runMixedFrom mixed fuel E.initHistory

/-- **Behavioral play extends deterministic play.** Reading a deterministic
profile as behavioral changes nothing about the law it induces. -/
theorem runBehavioralFrom_toBehavioral (policies : (i : ι) → M.Policy i)
    (fuel : ℕ) (h : E.History) :
    M.runBehavioralFrom (fun i => (policies i).toBehavioral) fuel h =
      M.runFrom policies fuel h := by
  have hchooser : M.randomizedChooser (fun i => (policies i).toBehavioral) =
      (M.historyChooser policies).toRandomized := by
    funext h' hterm
    rw [randomizedChooser, behavioralJoint, ExecutionProtocol.HistoryChooser.toRandomized]
    simp only [Policy.toBehavioral, independentProduct_pure, PMF.pure_map]
    rfl
  rw [runBehavioralFrom, hchooser, runFrom, ExecutionProtocol.runRandomizedFor_toRandomized]

/-- **Mixed play extends deterministic play**, for the same reason and by the
other route. -/
theorem runMixedFrom_pure (policies : (i : ι) → M.Policy i)
    (fuel : ℕ) (h : E.History) :
    M.runMixedFrom (fun i => PMF.pure (policies i)) fuel h = M.runFrom policies fuel h := by
  rw [runMixedFrom, independentProduct_pure, PMF.pure_bind]

end Profiles

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

/-- A belief at an information state is a PMF on the states that
information state leaves open. -/
def BeliefOn (i : ι) (info : M.InfoState i) (belief : PMF E.State) : Prop :=
  belief.support ⊆ M.InfoSet i info

/-- Sequential feasibility: a policy's action is legal at every state a
supported belief considers possible. The policy still never saw one. -/
theorem legalOption_of_beliefOn {i : ι} {info : M.InfoState i} {belief : PMF E.State}
    (hbelief : M.BeliefOn i info belief) (policy : M.Policy i) {state : E.State}
    (hstate : state ∈ belief.support) :
    LegalOption E state i (policy.act info) :=
  (M.legalOption_of_mem_menu info (hbelief hstate) (policy.act info)).mp
    (policy.act_mem_menu info)

end InformationModel

end GameTheory.Protocol
