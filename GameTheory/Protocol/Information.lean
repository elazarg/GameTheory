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

import GameTheory.Protocol.Randomized

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

/-! ### Being asked twice at one information state

A player asked to act twice at one information state cannot be committed by a
single draw made in advance: a policy answers that information state once and
for all, while a player randomizing locally draws again. The predicate below
names the condition that rules this out.

It is not recall. Recall is about what a player *remembers*; this is about
whether it is *asked twice*, and a game can fail it while every player
remembers everything. -/

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

/-- What a player may do at an information state. Legality rides on the type, so
nothing built from `Choice` — deterministic, randomizing, or correlated — can
name an action outside the menu. -/
abbrev Choice (i : ι) (info : M.InfoState i) : Type _ :=
  { choice : Option (E.Action i) // choice ∈ M.menu i info }

/-- A player's policy: a choice from its own menu, given only its own
information state. -/
def Policy (i : ι) : Type _ := (info : M.InfoState i) → M.Choice i info

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
def runFrom (policies : (i : ι) → M.Policy i) (fuel : ℕ) (h : E.History) : FinDist E.History :=
  E.runHistoryFor (M.historyChooser policies) fuel h

/-- The law over histories a profile induces from the start of play. -/
def run (policies : (i : ι) → M.Policy i) (fuel : ℕ) : FinDist E.History :=
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
      refine FinDist.bindOnSupport_congr fun target realized => ?_
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
    (M.actedAt i trace).Pairwise fun earlier later =>
      earlier ≠ later ∨ Subsingleton (M.Choice i later)

/-- Never acting twice at one information state is the special case that ignores
the menu. -/
theorem actsOnceWhereItMatters_of_actsOnce (hactsOnce : M.ActsOnceAtEachInfoState) :
    M.ActsOnceWhereItMatters := fun i _ trace =>
  (hactsOnce i trace).imp fun hne => Or.inl hne

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

/-- Local randomization: one law over its own menu at each information state. -/
def BehavioralPolicy (i : ι) : Type _ :=
  (info : M.InfoState i) → FinDist (M.Choice i info)

/-- Global randomization: one law over deterministic policies. -/
def MixedPolicy (i : ι) : Type _ := FinDist (M.Policy i)

variable {M} in
/-- A deterministic policy read as a behavioral one that never really
randomizes. -/
def Policy.toBehavioral {i : ι} (policy : M.Policy i) : M.BehavioralPolicy i :=
  fun info => FinDist.pure (policy info)

/-- Hence any two behavioral policies agree there. -/
theorem behavioral_eq_of_not_active {i : ι} (first second : M.BehavioralPolicy i)
    {state : E.State} (trace : Trace E state) (hinactive : ¬ E.active state i) :
    first (M.infoOf i trace) = second (M.infoOf i trace) := by
  have := M.subsingleton_choice_of_not_active trace hinactive
  obtain ⟨choice⟩ : Nonempty (M.Choice i (M.infoOf i trace)) :=
    ⟨⟨none, (M.menu_adequate i trace none).mpr hinactive⟩⟩
  rw [FinDist.eq_pure_of_subsingleton (first (M.infoOf i trace)) choice,
    FinDist.eq_pure_of_subsingleton (second (M.infoOf i trace)) choice]

section Profiles

variable [Fintype ι]

/-- The law over legal joint actions a behavioral profile induces after a
history: every player draws from its own menu, and the draws are independent
because nothing couples them. Menu adequacy is what makes each drawn joint
action legal, so randomizing needs no legality argument the deterministic case
did not already have. -/
def behavioralJoint (policies : (i : ι) → M.BehavioralPolicy i) {state : E.State}
    (trace : Trace E state) (hterm : ¬ E.terminal state) :
    FinDist { joint : ∀ i, Option (E.Action i) // E.Legal state joint } :=
  FinDist.map
    (fun draws => ⟨fun i => (draws i).1,
      ExecutionProtocol.legal_of_legalOption hterm fun i =>
        (M.menu_adequate i trace (draws i).1).mp (draws i).2⟩)
    (FinDist.pi fun i => policies i (M.infoOf i trace))

/-- Behavioral profiles that agree at one information history induce the same
local joint-action law there.  This is the one-step congruence used by the
global runner theorem below. -/
theorem behavioralJoint_congr {first second : (i : ι) → M.BehavioralPolicy i}
    {state : E.State} (trace : Trace E state) (hterm : ¬ E.terminal state)
    (hagree : ∀ i, first i (M.infoOf i trace) = second i (M.infoOf i trace)) :
    M.behavioralJoint first trace hterm = M.behavioralJoint second trace hterm := by
  rw [behavioralJoint, behavioralJoint]
  exact congrArg _ (congrArg FinDist.pi (funext hagree))

section SingleMoverBehavioralJoint

variable [DecidableEq ι]

/-- If nobody acts, the behavioral product is the unique all-`none` joint
action. -/
theorem behavioralJoint_eq_pure_of_no_active
    (policies : (i : ι) → M.BehavioralPolicy i)
    {state : E.State} (trace : E.Trace state)
    (hterminal : ¬ E.terminal state)
    (hinactive : ∀ i, ¬ E.active state i) :
    M.behavioralJoint policies trace hterminal =
      FinDist.pure
        ⟨fun _ => none,
          ExecutionProtocol.legal_of_legalOption hterminal
            hinactive⟩ := by
  let idle :
      (i : ι) → M.Choice i (M.infoOf i trace) :=
    fun i => ⟨none, (M.menu_adequate i trace none).mpr
      (hinactive i)⟩
  have hpolicy (i : ι) :
      policies i (M.infoOf i trace) =
        FinDist.pure (idle i) := by
    haveI : Subsingleton (M.Choice i (M.infoOf i trace)) :=
      M.subsingleton_choice_of_not_active trace (hinactive i)
    exact FinDist.eq_pure_of_subsingleton _ (idle i)
  unfold behavioralJoint
  simp_rw [hpolicy]
  rw [FinDist.pi_pure, FinDist.map_pure]

/-- If at most one player can act, the behavioral product is that player's
local law embedded in the only possibly active joint coordinate. -/
theorem behavioralJoint_eq_map_of_at_most_one_active
    (policies : (i : ι) → M.BehavioralPolicy i)
    {state : E.State} (trace : E.Trace state)
    (hterminal : ¬ E.terminal state)
    (active : ι)
    (hunique : ∀ i, E.active state i → i = active) :
    M.behavioralJoint policies trace hterminal =
      FinDist.map
        (fun choice : M.Choice active (M.infoOf active trace) =>
          ⟨(fun other =>
              if howner : other = active then by
                subst other
                exact choice.1
              else none),
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
                  simpa only [howner, dite_false, LegalOption]
                    using hinactive⟩)
        (policies active (M.infoOf active trace)) := by
  let idle :
      (other : {other : ι // other ≠ active}) →
        M.Choice other.1 (M.infoOf other.1 trace) :=
    fun other => ⟨none,
      (M.menu_adequate other.1 trace none).mpr <| by
        intro hother
        exact other.2 (hunique other.1 hother)⟩
  have hpolicy (other : {other : ι // other ≠ active}) :
      policies other.1 (M.infoOf other.1 trace) =
        FinDist.pure (idle other) := by
    have hinactive : ¬ E.active state other.1 := by
      intro hother
      exact other.2 (hunique other.1 hother)
    haveI :
        Subsingleton
          (M.Choice other.1 (M.infoOf other.1 trace)) :=
      M.subsingleton_choice_of_not_active trace hinactive
    exact FinDist.eq_pure_of_subsingleton _ (idle other)
  unfold behavioralJoint
  rw [FinDist.pi_eq_map_product active, FinDist.map_comp]
  simp_rw [hpolicy]
  rw [FinDist.pi_pure]
  unfold FinDist.product
  simp only [FinDist.map_eq_bind,
    FinDist.bind_bind, FinDist.pure_bind]
  apply FinDist.bind_congr
  intro choice _
  apply congrArg FinDist.pure
  apply Subtype.ext
  funext other
  by_cases howner : other = active
  · subst other
    simp
  · simp [howner, idle]

end SingleMoverBehavioralJoint

/-- A behavioral profile, as a chooser. -/
def randomizedChooser (policies : (i : ι) → M.BehavioralPolicy i) : E.RandomizedChooser :=
  fun h hterm => M.behavioralJoint policies h.trace hterm

/-- The law over histories a behavioral profile induces from a given history. -/
def runBehavioralFrom (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) (h : E.History) :
    FinDist E.History :=
  E.runRandomizedFor (M.randomizedChooser policies) fuel h

/-- Behavioral play started from a terminal history is absorbed there for
every fuel amount. -/
@[simp]
theorem runBehavioralFrom_of_terminal
    (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) {h : E.History}
    (hterm : E.terminal h.state) :
    M.runBehavioralFrom policies fuel h = FinDist.pure h :=
  E.runRandomizedFor_of_terminal (M.randomizedChooser policies) fuel hterm

/-- The law over histories a behavioral profile induces from the start. -/
def runBehavioral (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) : FinDist E.History :=
  M.runBehavioralFrom policies fuel E.initHistory

/-- Behavioral play composes across adjacent fuel blocks. -/
theorem runBehavioralFrom_add
    (policies : (i : ι) → M.BehavioralPolicy i)
    (firstFuel secondFuel : ℕ) (history : E.History) :
    M.runBehavioralFrom policies (firstFuel + secondFuel) history =
      (M.runBehavioralFrom policies firstFuel history).bind
        (M.runBehavioralFrom policies secondFuel) :=
  E.runRandomizedFor_add (M.randomizedChooser policies)
    firstFuel secondFuel history

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
    · have hhere : M.randomizedChooser first h hterm = M.randomizedChooser second h hterm := by
        rw [randomizedChooser, randomizedChooser]
        exact M.behavioralJoint_congr h.trace hterm fun i => hagree h (.refl _ _) hterm i
      rw [runBehavioralFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm, hhere]
      refine FinDist.bind_congr fun draw _ => FinDist.bindOnSupport_congr fun target realized => ?_
      exact ih _ fun h' hreach hterm' i => hagree h' (.step _ _ realized hreach) hterm' i

/-- The law a mixed profile induces: draw a deterministic profile once, then
play it. The single draw is the whole difference from the behavioral case. -/
def runMixedFrom (mixed : (i : ι) → M.MixedPolicy i) (fuel : ℕ) (h : E.History) :
    FinDist E.History :=
  (FinDist.pi mixed).bind fun policies => M.runFrom policies fuel h

/-- The law a mixed profile induces from the start. -/
def runMixed (mixed : (i : ι) → M.MixedPolicy i) (fuel : ℕ) : FinDist E.History :=
  M.runMixedFrom mixed fuel E.initHistory

/-- **Behavioral play extends deterministic play.** Reading a deterministic
profile as behavioral changes nothing about the law it induces. -/
theorem runBehavioralFrom_toBehavioral [DecidableEq ι] (policies : (i : ι) → M.Policy i)
    (fuel : ℕ) (h : E.History) :
    M.runBehavioralFrom (fun i => (policies i).toBehavioral) fuel h =
      M.runFrom policies fuel h := by
  have hchooser : M.randomizedChooser (fun i => (policies i).toBehavioral) =
      (M.historyChooser policies).toRandomized := by
    funext h' hterm
    rw [randomizedChooser, behavioralJoint, ExecutionProtocol.HistoryChooser.toRandomized]
    simp only [Policy.toBehavioral, FinDist.pi_pure, FinDist.map_pure]
    rfl
  rw [runBehavioralFrom, hchooser, runFrom, ExecutionProtocol.runRandomizedFor_toRandomized]

/-- **Mixed play extends deterministic play**, for the same reason and by the
other route. -/
theorem runMixedFrom_pure [DecidableEq ι] (policies : (i : ι) → M.Policy i)
    (fuel : ℕ) (h : E.History) :
    M.runMixedFrom (fun i => FinDist.pure (policies i)) fuel h = M.runFrom policies fuel h := by
  rw [runMixedFrom, FinDist.pi_pure, FinDist.pure_bind]

end Profiles

/-! ### Reading a single draw back as local randomization

A mixed policy answers an information state once, so the local law it induces
there is the law of that answer *given* that the draw could have brought play to
that information state. The condition is a statement about the player's own
record, and recall is what makes that record a function of the information state
rather than of a particular history in it. -/

open Classical in
/-- The record a player's own moves leave at an information state, read off some
history that produces it. Which history is read does not matter under recall,
which is the theorem below; without recall this is merely some choice. -/
noncomputable def recordAt (i : ι) (info : M.InfoState i) :
    List (M.InfoState i × E.Action i) :=
  if hreached : ∃ h : E.History, M.infoOf i h.trace = info then
    M.ownPlay i (Classical.choose hreached).trace
  else []

/-- **What recall is for.** With it, the record at an information state is the
record along *every* history that produces it, so the arbitrary choice above is
no choice at all. -/
theorem recordAt_eq_ownPlay (hrecall : M.PerfectRecall) (i : ι) (h : E.History) :
    M.recordAt i (M.infoOf i h.trace) = M.ownPlay i h.trace := by
  have hreached : ∃ g : E.History, M.infoOf i g.trace = M.infoOf i h.trace := ⟨h, rfl⟩
  rw [recordAt, dif_pos hreached]
  exact hrecall i _ _ (Classical.choose_spec hreached)

/-- The pure policies whose own choices match a record of past moves. -/
def Consistent (i : ι) (record : List (M.InfoState i × E.Action i)) : Set (M.Policy i) :=
  { policy | ∀ step ∈ record, (policy step.1).1 = some step.2 }

/-- The pure policies that could have brought play to an information state. -/
def ConsistentAt (i : ι) (info : M.InfoState i) : Set (M.Policy i) :=
  M.Consistent i (M.recordAt i info)

/-- **What the recall direction actually needs.** Two histories a player cannot
tell apart constrain its policy the same way.

This is weaker than recall, and the gap is not an artefact: recall compares the
*records* two histories leave, while nothing downstream reads a record except
through the set of policies it rules out. A player that forgets the order of its
own past moves, or how many times it repeated one, still constrains its policy
identically — so it fails recall and satisfies this. -/
def ConstrainsAlike : Prop :=
  ∀ (i : ι) {first second : E.State} (traceFirst : Trace E first) (traceSecond : Trace E second),
    M.infoOf i traceFirst = M.infoOf i traceSecond →
      M.Consistent i (M.ownPlay i traceFirst) = M.Consistent i (M.ownPlay i traceSecond)

variable {M} in
/-- Recall is the special case that compares the records themselves. -/
theorem constrainsAlike_of_perfectRecall (hrecall : M.PerfectRecall) : M.ConstrainsAlike := by
  intro i _ _ traceFirst traceSecond hinfo
  rw [hrecall i traceFirst traceSecond hinfo]

variable {M} in
/-- **And the gap is real.** Records differing only in the order of a player's
own moves rule out the same policies, so a player that forgets the order fails
recall and still constrains alike. -/
theorem consistent_eq_of_perm {i : ι} {first second : List (M.InfoState i × E.Action i)}
    (hperm : first.Perm second) : M.Consistent i first = M.Consistent i second := by
  ext policy
  exact ⟨fun hpolicy step hstep => hpolicy step (hperm.mem_iff.mpr hstep),
    fun hpolicy step hstep => hpolicy step (hperm.mem_iff.mp hstep)⟩

variable {M} in
/-- Under it, the constraint attached to an information state is the constraint
along every history producing it — which is all the argument ever asks of the
arbitrary choice inside `recordAt`. -/
theorem consistentAt_eq_consistent_ownPlay (hconstrain : M.ConstrainsAlike) (i : ι)
    (h : E.History) :
    M.ConsistentAt i (M.infoOf i h.trace) = M.Consistent i (M.ownPlay i h.trace) := by
  have hreached : ∃ g : E.History, M.infoOf i g.trace = M.infoOf i h.trace := ⟨h, rfl⟩
  rw [ConsistentAt, recordAt, dif_pos hreached]
  exact hconstrain i _ _ (Classical.choose_spec hreached)

/-- A longer record is a stronger constraint. -/
theorem consistent_subset_of_isSuffix {i : ι}
    {shorter longer : List (M.InfoState i × E.Action i)} (hsuffix : shorter <:+ longer) :
    M.Consistent i longer ⊆ M.Consistent i shorter :=
  fun _ hpolicy step hstep => hpolicy step (hsuffix.subset hstep)

/-- **What a step commits the player to, for the rest of play.** Having answered
one information state, every policy still consistent with any later history
answers it the same way. -/
theorem consistentAt_subset_of_step (hconstrain : M.ConstrainsAlike) (i : ι) {h : E.History}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {action : E.Action i} (hjoint : joint i = some action)
    {fuel : ℕ} {later : E.History}
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later) :
    M.ConsistentAt i (M.infoOf i later.trace) ⊆
      { policy : M.Policy i | (policy (M.infoOf i h.trace)).1 = some action } := by
  intro policy hpolicy
  have hstep : (M.infoOf i h.trace, action) ∈
      M.ownPlay i (h.extend isLegal realized).trace := by
    show _ ∈ M.ownPlay i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.ownPlay_extend, hjoint]
    exact List.mem_cons_self
  rw [M.consistentAt_eq_consistent_ownPlay hconstrain i later] at hpolicy
  exact hpolicy _ ((M.ownPlay_isSuffix_of_reachesWithin i hreach).subset hstep)

variable {M} in
open Classical in
/-- A mixed policy read as a behavioral one: at each information state, the law
of the action it prescribes there, conditioned on the policies that could have
brought play to that information state.

Where no such policy has positive mass the conditioning is undefined, and the
reading falls back on a policy supplied for the purpose. A policy is the right
thing to fall back on: it already chooses legally at every information state,
including ones no history produces, where the menu law says nothing and the menu
could otherwise be empty.

The fallback is a parameter rather than a canonical choice because it must be
*stable*: an argument that conditions the law as play advances compares the
readings of a law and of that law conditioned, and a fallback read off the law's
own support would move when the support shrinks. Holding one fixed says the
reading is determined up to its behaviour where play never goes. -/
noncomputable def MixedPolicy.toBehavioralWith {i : ι} (mixed : M.MixedPolicy i)
    (fallback : M.Policy i) : M.BehavioralPolicy i := fun info =>
  if hreachable : ∃ policy ∈ M.ConsistentAt i info, policy ∈ mixed.support then
    FinDist.map (fun policy => policy info) (mixed.condOn (M.ConsistentAt i info) hreachable)
  else FinDist.pure (fallback info)

variable {M} in
/-- The reading with nothing supplied: fall back on a policy the law itself gives
mass to. -/
noncomputable def MixedPolicy.toBehavioral {i : ι} (mixed : M.MixedPolicy i) :
    M.BehavioralPolicy i :=
  mixed.toBehavioralWith mixed.support_nonempty.choose

variable {M} in
/-- The degenerate case: a single draw that is not really random reads back as
the policy it draws. Both branches give that answer, so nothing here depends on
whether the information state was reachable at all. -/
theorem MixedPolicy.toBehavioral_pure {i : ι} (policy : M.Policy i) :
    MixedPolicy.toBehavioral (M := M) (FinDist.pure policy) = policy.toBehavioral := by
  classical
  funext info
  rw [MixedPolicy.toBehavioral, MixedPolicy.toBehavioralWith]
  split
  · rw [FinDist.condOn_pure, FinDist.map_pure]
    rfl
  · have hchosen := (FinDist.pure policy : M.MixedPolicy i).support_nonempty.choose_spec
    rw [FinDist.mem_support_pure] at hchosen
    rw [hchosen]
    rfl

variable {M} in
/-- A behavioral policy as a mixed one: draw the action for every information
state in advance, independently. Whether the two laws agree is exactly the
question above, and this construction is where it is asked.

Scope: this draws for *every* information state, so it asks the player's
information states to be finite in number. Play with a bounded horizon visits
only finitely many of them whether or not the rest are finite, so the weaker
hypothesis would suffice; it is not taken here, because nothing yet needs it. -/
def BehavioralPolicy.toMixed {i : ι} [Fintype (M.InfoState i)]
    (policy : M.BehavioralPolicy i) : M.MixedPolicy i :=
  FinDist.pi policy

variable {M} in
/-- The behavioral profile that has committed to one choice at one information
state and is unchanged elsewhere.

It is built from the same coordinate decomposition the product factorization
uses, rather than by updating a dependent function pointwise. That is not only
tidier: updating pointwise would transport a value along an equality of
information states, and this layer keeps such transports out. -/
def BehavioralPolicy.commit {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info) :
    M.BehavioralPolicy i :=
  (Equiv.piSplitAt info fun w => FinDist (M.Choice i w)).symm
    (FinDist.pure choice, fun w => policy w.1)

variable {M} in
@[simp]
theorem BehavioralPolicy.commit_self {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info) :
    policy.commit info choice info = FinDist.pure choice := by
  simp [commit]

variable {M} in
@[simp]
theorem BehavioralPolicy.commit_of_ne {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info)
    {other : M.InfoState i} (hne : other ≠ info) :
    policy.commit info choice other = policy other := by
  simp [commit, hne]

variable {M} in
/-- **Committing keeps the profile mixed.** Re-extending the rest of a drawn
policy with a fixed choice at one information state is again the mixed reading
of a behavioral profile — the one that has committed there.

This is what lets an induction over play stay on full profiles: a coordinate
already consulted becomes a point mass rather than disappearing from the index,
and point masses need no bookkeeping. -/
theorem BehavioralPolicy.toMixed_commit {i : ι} [Fintype (M.InfoState i)]
    [DecidableEq (M.InfoState i)] (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (choice : M.Choice i info) :
    (policy.commit info choice).toMixed =
      FinDist.map
        (fun rest => (Equiv.piSplitAt info fun w => M.Choice i w).symm (choice, rest))
        (FinDist.pi fun w : {w // w ≠ info} => policy w.1) := by
  rw [toMixed, FinDist.pi_eq_map_product info,
    show (fun w : {w // w ≠ info} => policy.commit info choice w.1) =
      (fun w : {w // w ≠ info} => policy w.1) from
        funext fun w => policy.commit_of_ne info choice w.2,
    commit_self, FinDist.product, FinDist.pure_bind, FinDist.map_comp]
  rfl

variable {M} in
/-- The construction is the right one in the degenerate case: a deterministic
policy, randomized nowhere, comes back as the point mass at itself. -/
theorem Policy.toBehavioral_toMixed {i : ι} [Fintype (M.InfoState i)]
    [DecidableEq (M.InfoState i)] (policy : M.Policy i) :
    policy.toBehavioral.toMixed = FinDist.pure policy :=
  FinDist.pi_pure policy

/-! ## When the two randomizations agree

Drawing at each information state and drawing once over policies give the same
law exactly when the single draw is never asked to answer twice. The proof
follows play: at each step the drawn policy is factored at the information
states about to be consulted, its first factor is matched against the local
draw, and the rest is re-read as a mixed profile that has committed there. The
commitment is then invisible, because the coordinate is never consulted again —
or, where the player does not move, because there was nothing to choose. -/

/-- Reassembling a policy from its value at one information state and its values
elsewhere returns that value there. -/
theorem piSplitAt_symm_self {i : ι} [DecidableEq (M.InfoState i)] (info : M.InfoState i)
    (q : M.Choice i info × ∀ w : {w // w ≠ info}, M.Choice i w.1) :
    (Equiv.piSplitAt info fun w => M.Choice i w).symm q info = q.1 := by
  simp

/-- Unfolding one step of deterministic play against a chooser value already
known. Naming the value keeps the rewrite out of the dependent position it would
otherwise land in. -/
theorem runFrom_succ_of_chooser_eq (policies : (i : ι) → M.Policy i) {h : E.History}
    (hterm : ¬ E.terminal h.state)
    (chosen : { joint : ∀ i, Option (E.Action i) // E.Legal h.state joint })
    (hchosen : M.historyChooser policies h hterm = chosen) (fuel : ℕ) :
    M.runFrom policies (fuel + 1) h =
      (E.step h.state chosen).bindOnSupport fun _ realized =>
        M.runFrom policies fuel (h.extend chosen.2 realized) := by
  subst hchosen
  rw [runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm]
  rfl

/-- A commitment made at one step is invisible from the next one on: either the
player never meets that information state again while moving, or it does not
move there and had nothing to choose. -/
theorem commit_agree_of_actsOnce [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (β : (i : ι) → M.BehavioralPolicy i) {h : E.History}
    (draw : (i : ι) → M.Choice i (M.infoOf i h.trace))
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal h.state joint)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {fuel : ℕ} (later : E.History)
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    (hlater : ¬ E.terminal later.state) (i : ι) :
    (β i).commit (M.infoOf i h.trace) (draw i) (M.infoOf i later.trace) =
      β i (M.infoOf i later.trace) := by
  by_cases hne : M.infoOf i later.trace ≠ M.infoOf i h.trace
  · exact BehavioralPolicy.commit_of_ne _ _ _ hne
  push Not at hne
  by_cases hactiveLater : E.active later.state i
  · by_cases hactiveHere : E.active h.state i
    · have hdisj : M.infoOf i later.trace ≠ M.infoOf i h.trace ∨
          Subsingleton (M.Choice i (M.infoOf i h.trace)) := by
        obtain ⟨laterJoint, hlaterJoint⟩ := E.progress later.state hlater
        have hlaterLegal : E.Legal later.state laterJoint := ⟨hlater, hlaterJoint⟩
        obtain ⟨laterTarget, hlaterRealized⟩ :=
          (E.step later.state ⟨laterJoint, hlaterLegal⟩).support_nonempty
        obtain ⟨_, hsome⟩ := LegalOption.exists_eq_some_of_active (joint i)
          (ExecutionProtocol.legalOption_of_legal isLegal i) hactiveHere
        obtain ⟨_, hlaterSome⟩ := LegalOption.exists_eq_some_of_active (laterJoint i)
          (ExecutionProtocol.legalOption_of_legal hlaterLegal i) hactiveLater
        exact M.infoOf_ne_or_subsingleton_of_actsOnce hactsOnce i isLegal realized
          (by rw [hsome]; rfl) hreach hlaterLegal hlaterRealized (by rw [hlaterSome]; rfl)
      rcases hdisj with hne' | hsubsingleton
      · exact absurd hne hne'
      · rw [hne, BehavioralPolicy.commit_self]
        exact (FinDist.eq_pure_of_subsingleton _ (draw i)).symm
    · have : Subsingleton (M.Choice i (M.infoOf i h.trace)) :=
        M.subsingleton_choice_of_not_active h.trace hactiveHere
      rw [hne, BehavioralPolicy.commit_self]
      exact (FinDist.eq_pure_of_subsingleton _ (draw i)).symm
  · exact M.behavioral_eq_of_not_active _ _ later.trace hactiveLater

section Equivalence

variable [Fintype ι] [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]

/-- **The equivalence.** With no player ever asked to act twice at one
information state, randomizing locally and randomizing once over policies induce
the same law over histories. -/
theorem runMixedFrom_toMixed (hactsOnce : M.ActsOnceWhereItMatters) :
    ∀ (fuel : ℕ) (β : (i : ι) → M.BehavioralPolicy i) (h : E.History),
      M.runMixedFrom (fun i => (β i).toMixed) fuel h = M.runBehavioralFrom β fuel h := by
  intro fuel
  induction fuel with
  | zero => intro β h; exact FinDist.bind_const _ _
  | succ fuel ih =>
    intro β h
    by_cases hterm : E.terminal h.state
    · rw [runMixedFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
      refine Eq.trans (FinDist.bind_congr fun policies _ => ?_) (FinDist.bind_const _ _)
      rw [runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
    · -- The information states about to be consulted, and the two halves of a
      -- drawn policy: its value there, and its values everywhere else.
      set info : (i : ι) → M.InfoState i := fun i => M.infoOf i h.trace with hinfo
      set assemble : (i : ι) →
          M.Choice i (info i) × (∀ w : {w // w ≠ info i}, M.Choice i w.1) → M.Policy i :=
        fun i q => (Equiv.piSplitAt (info i) fun w => M.Choice i w).symm q with hassemble
      set elsewhere : (i : ι) → FinDist (∀ w : {w // w ≠ info i}, M.Choice i w.1) :=
        fun i => FinDist.pi fun w => β i w.1 with helsewhere
      have hfactor : (FinDist.pi fun i => (β i).toMixed) =
          FinDist.map (fun q i => assemble i (q.1 i, q.2 i))
            (FinDist.product (FinDist.pi fun i => β i (info i)) (FinDist.pi elsewhere)) := by
        rw [show (fun i => (β i).toMixed) =
            (fun i => FinDist.map (assemble i)
              (FinDist.product (β i (info i)) (elsewhere i))) from
          funext fun i => FinDist.pi_eq_map_product (info i) (β i),
          FinDist.pi_map, FinDist.pi_product, FinDist.map_comp]
        rfl
      rw [runMixedFrom, hfactor, FinDist.bind_map, FinDist.product, FinDist.bind_bind,
        runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm,
        randomizedChooser, behavioralJoint, FinDist.bind_map]
      refine FinDist.bind_congr fun draw _ => ?_
      rw [FinDist.bind_map]
      -- Both sides now take the same joint action.
      have hchosen : ∀ rest : ∀ i, ∀ w : {w // w ≠ info i}, M.Choice i w.1,
          M.historyChooser (fun i => assemble i (draw i, rest i)) h hterm =
            ⟨fun i => (draw i).1,
              ExecutionProtocol.legal_of_legalOption hterm fun i =>
                (M.menu_adequate i h.trace (draw i).1).mp (draw i).2⟩ := by
        intro rest
        refine Subtype.ext (funext fun i => ?_)
        show ((Equiv.piSplitAt (info i) fun w => M.Choice i w).symm (draw i, rest i)
            (info i)).1 = (draw i).1
        rw [piSplitAt_symm_self]
      rw [show (fun rest => M.runFrom (fun i => assemble i (draw i, rest i)) (fuel + 1) h) =
          (fun rest =>
            (E.step h.state ⟨fun i => (draw i).1, _⟩).bindOnSupport fun _ realized =>
              M.runFrom (fun i => assemble i (draw i, rest i)) fuel
                (h.extend (ExecutionProtocol.legal_of_legalOption hterm fun i =>
                  (M.menu_adequate i h.trace (draw i).1).mp (draw i).2) realized)) from
        funext fun rest =>
          M.runFrom_succ_of_chooser_eq _ hterm _ (hchosen rest) fuel,
        FinDist.bind_bindOnSupport_comm]
      refine FinDist.bindOnSupport_congr fun target realized => ?_
      -- The rest of the drawn policy is again a mixed profile: the committed one.
      rw [show (FinDist.pi elsewhere).bind (fun rest =>
            M.runFrom (fun i => assemble i (draw i, rest i)) fuel _) =
          M.runMixedFrom (fun i => ((β i).commit (info i) (draw i)).toMixed) fuel _ from by
        rw [runMixedFrom,
          show (fun i => ((β i).commit (info i) (draw i)).toMixed) =
              (fun i => FinDist.map (fun rr => assemble i (draw i, rr)) (elsewhere i)) from
            funext fun i => BehavioralPolicy.toMixed_commit (β i) (info i) (draw i),
          FinDist.pi_map, FinDist.bind_map],
        ih (fun i => (β i).commit (info i) (draw i)) _]
      refine M.runBehavioralFrom_congr fuel _ fun later hreach hlater i => ?_
      exact M.commit_agree_of_actsOnce hactsOnce β draw _ realized later hreach hlater i

/-- The from-start form: the two randomizations induce the same law over plays.
This is the shape a statement about a whole game quotes. -/
theorem runMixed_toMixed (hactsOnce : M.ActsOnceWhereItMatters)
    (β : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) :
    M.runMixed (fun i => (β i).toMixed) fuel = M.runBehavioral β fuel :=
  M.runMixedFrom_toMixed hactsOnce fuel β E.initHistory

/-- And hence the same law over the states play reaches, which is the shape an
outcome-level statement quotes. Nothing is lost by forgetting the history here,
because the laws agreed on histories in the first place. -/
theorem map_state_runMixed_toMixed (hactsOnce : M.ActsOnceWhereItMatters)
    (β : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) :
    FinDist.map ExecutionProtocol.History.state (M.runMixed (fun i => (β i).toMixed) fuel) =
      FinDist.map ExecutionProtocol.History.state (M.runBehavioral β fuel) :=
  congrArg _ (M.runMixed_toMixed hactsOnce β fuel)

end Equivalence

/-! ## When a single draw is local randomization

Reading a mixed profile back as a behavioral one preserves the law it induces,
provided every player recalls its own play. The induction follows play: at each
step the single draw is disintegrated along the joint action it prescribes, the
observed part matches the behavioral draw exactly, and the remainder is the
profile conditioned on having answered that way. What is conditioned stays
conditioned, and the tower property makes the accumulated conditioning invisible
to the behavioral reading. -/

/-- Where every drawn policy could already have brought play here, the
behavioral reading is the plain marginal. -/
theorem toBehavioralWith_eq_map_of_support_subset {i : ι} (mixed : M.MixedPolicy i)
    (fallback : M.Policy i) (info : M.InfoState i)
    (hsub : mixed.support ⊆ M.ConsistentAt i info) :
    mixed.toBehavioralWith fallback info = FinDist.map (fun policy => policy info) mixed := by
  classical
  obtain ⟨policy, hpolicy⟩ := mixed.support_nonempty
  rw [MixedPolicy.toBehavioralWith, dif_pos ⟨policy, hsub hpolicy, hpolicy⟩,
    FinDist.condOn_of_support_subset _ _ _ hsub]

section Recall

variable [Fintype ι] [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]

/-- The joint answer a drawn profile gives at a history. -/
def answerAt (h : E.History) (policies : (i : ι) → M.Policy i) :
    (i : ι) → M.Choice i (M.infoOf i h.trace) := fun i => policies i (M.infoOf i h.trace)

/-- The policies that answer a history the way `answer` does, player by
player. -/
def AnsweredBy (h : E.History) (answer : (i : ι) → M.Choice i (M.infoOf i h.trace)) (i : ι) :
    Set (M.Policy i) :=
  { policy | policy (M.infoOf i h.trace) = answer i }

omit [Fintype ι] [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
theorem answerAt_preimage_eq (h : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i h.trace)) :
    M.answerAt h ⁻¹' {answer} = { p | ∀ i, p i ∈ M.AnsweredBy h answer i } := by
  ext policies
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, answerAt,
    AnsweredBy, funext_iff]

omit [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- **The single draw splits by player.** Conditioning a profile on the answer it
gave is conditioning each player's draw on its own answer, because nothing
couples the players. -/
theorem condOn_answerAt (mixed : (i : ι) → M.MixedPolicy i) (h : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i h.trace))
    (hjoint : ∃ p ∈ M.answerAt h ⁻¹' {answer}, p ∈ (FinDist.pi mixed).support)
    (hcoord : ∀ i, ∃ q ∈ M.AnsweredBy h answer i, q ∈ (mixed i).support) :
    (FinDist.pi mixed).condOn (M.answerAt h ⁻¹' {answer}) hjoint =
      FinDist.pi fun i => (mixed i).condOn (M.AnsweredBy h answer i) (hcoord i) := by
  have hset := M.answerAt_preimage_eq h answer
  rw [FinDist.condOn_congr _ hset _ (by rw [← hset]; exact hjoint)]
  exact FinDist.condOn_pi mixed (M.AnsweredBy h answer) hcoord _

omit [Fintype ι] [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- **A commitment is invisible to the reading afterwards.** Conditioning on the
answer a step gave changes neither branch at any later reachable history: where
consistent mass exists it survives the conditioning and the double conditioning
collapses, and where it does not, both readings fall back on the same policy. -/
theorem toBehavioralWith_condOn_answered (hconstrain : M.ConstrainsAlike) (i : ι) {h : E.History}
    {answer : (j : ι) → M.Choice j (M.infoOf j h.trace)}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    (hanswer : ∀ j, joint j = (answer j).1)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {action : E.Action i} (hact : joint i = some action)
    {fuel : ℕ} {later : E.History}
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    (mixed : M.MixedPolicy i) (fallback : M.Policy i)
    (hmass : ∃ q ∈ M.AnsweredBy h answer i, q ∈ mixed.support) :
    MixedPolicy.toBehavioralWith (M := M) (mixed.condOn (M.AnsweredBy h answer i) hmass)
        fallback (M.infoOf i later.trace) =
      mixed.toBehavioralWith fallback (M.infoOf i later.trace) := by
  classical
  have hnarrow : M.ConsistentAt i (M.infoOf i later.trace) ⊆ M.AnsweredBy h answer i := by
    intro policy hpolicy
    refine Subtype.ext ?_
    rw [M.consistentAt_subset_of_step hconstrain i isLegal realized hact hreach hpolicy,
      ← hanswer i, hact]
  simp only [MixedPolicy.toBehavioralWith]
  by_cases hex : ∃ policy ∈ M.ConsistentAt i (M.infoOf i later.trace), policy ∈ mixed.support
  · obtain ⟨policy, hpolicy, hmem⟩ := hex
    have hcond : ∃ p ∈ M.ConsistentAt i (M.infoOf i later.trace),
        p ∈ (mixed.condOn (M.AnsweredBy h answer i) hmass).support :=
      ⟨policy, hpolicy, FinDist.mem_support_condOn _ _ _ (hnarrow hpolicy) hmem⟩
    rw [dif_pos hcond, dif_pos ⟨policy, hpolicy, hmem⟩,
      FinDist.condOn_condOn mixed hmass ⟨policy, hpolicy, hmem⟩
        (Set.inter_subset_left.trans hnarrow) hcond]
  · have hcond : ¬ ∃ p ∈ M.ConsistentAt i (M.infoOf i later.trace),
        p ∈ (mixed.condOn (M.AnsweredBy h answer i) hmass).support := by
      rintro ⟨p, hp, hmem⟩
      exact hex ⟨p, hp, (FinDist.support_condOn _ _ hmass hmem).2⟩
    rw [dif_neg hcond, dif_neg hex]

omit [Fintype ι] [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- Conditioning on the answer changes nothing for a player that did not move:
its menu there was a single option, so every policy answered the same way. -/
theorem condOn_answeredBy_eq_self (i : ι) {h : E.History}
    {answer : (j : ι) → M.Choice j (M.infoOf j h.trace)}
    (hlegal : E.Legal h.state fun j => (answer j).1) (hidle : (answer i).1 = none)
    (mixed : M.MixedPolicy i) (hmass : ∃ q ∈ M.AnsweredBy h answer i, q ∈ mixed.support) :
    mixed.condOn (M.AnsweredBy h answer i) hmass = mixed := by
  have hinactive : ¬ E.active h.state i := by
    have hopt := ExecutionProtocol.legalOption_of_legal hlegal i
    rw [hidle] at hopt
    exact hopt
  have := M.subsingleton_choice_of_not_active h.trace hinactive
  exact FinDist.condOn_of_support_subset _ _ _ fun q _ => Subsingleton.elim _ _

omit [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- **The equivalence, in the direction that needs recall.** Where every player
recalls its own play, drawing a whole policy once induces the same law as
randomizing afresh at each information state.

The hypothesis is that the draw could already have brought play to where it
starts, which at the start of play is no hypothesis at all. -/
theorem runMixedFrom_toBehavioralWith (hconstrain : M.ConstrainsAlike)
    (fallback : (i : ι) → M.Policy i) :
    ∀ (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i) (h : E.History),
      (∀ i, (mixed i).support ⊆ M.ConsistentAt i (M.infoOf i h.trace)) →
      M.runMixedFrom mixed fuel h =
        M.runBehavioralFrom (fun i => (mixed i).toBehavioralWith (fallback i)) fuel h := by
  classical
  intro fuel
  induction fuel with
  | zero => intro mixed h _; exact FinDist.bind_const _ _
  | succ fuel ih =>
    intro mixed h hsub
    by_cases hterm : E.terminal h.state
    · rw [runMixedFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
      refine Eq.trans (FinDist.bind_congr fun policies _ => ?_) (FinDist.bind_const _ _)
      rw [runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
    · have hdraw : (FinDist.pi fun i =>
            (mixed i).toBehavioralWith (fallback i) (M.infoOf i h.trace)) =
          FinDist.map (M.answerAt h) (FinDist.pi mixed) := by
        rw [show (fun i => (mixed i).toBehavioralWith (fallback i) (M.infoOf i h.trace)) =
            (fun i => FinDist.map (fun policy => policy (M.infoOf i h.trace)) (mixed i)) from
          funext fun i =>
            M.toBehavioralWith_eq_map_of_support_subset (mixed i) (fallback i) _ (hsub i),
          FinDist.pi_map]
        rfl
      conv_lhs => rw [runMixedFrom,
        FinDist.eq_bind_condOnFibre (FinDist.pi mixed) (M.answerAt h), FinDist.bind_bind,
        FinDist.bind_map]
      rw [runBehavioralFrom, ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm,
        randomizedChooser, behavioralJoint, hdraw]
      conv_rhs => rw [FinDist.map_comp, FinDist.bind_map]
      refine FinDist.bind_congr fun p hp => ?_
      have hfib : ∃ q ∈ M.answerAt h ⁻¹' {M.answerAt h p}, q ∈ (FinDist.pi mixed).support :=
        ⟨p, rfl, hp⟩
      have hcoord : ∀ i, ∃ q ∈ M.AnsweredBy h (M.answerAt h p) i, q ∈ (mixed i).support :=
        fun i => ⟨p i, rfl, FinDist.mem_support_pi.mp hp i⟩
      have hlegal : E.Legal h.state (fun i => ((M.answerAt h p) i).1) :=
        ExecutionProtocol.legal_of_legalOption hterm fun i =>
          (M.menu_adequate i h.trace ((M.answerAt h p) i).1).mp ((M.answerAt h p) i).2
      rw [FinDist.condOnFibre, dif_pos hfib,
        M.condOn_answerAt mixed h (M.answerAt h p) hfib hcoord]
      have hstep : (FinDist.pi fun i =>
            (mixed i).condOn (M.AnsweredBy h (M.answerAt h p) i) (hcoord i)).bind
              (fun q => M.runFrom q (fuel + 1) h) =
          (FinDist.pi fun i =>
            (mixed i).condOn (M.AnsweredBy h (M.answerAt h p) i) (hcoord i)).bind
              (fun q => (E.step h.state ⟨fun i => ((M.answerAt h p) i).1, hlegal⟩).bindOnSupport
                fun _ realized => M.runFrom q fuel (h.extend hlegal realized)) :=
        FinDist.bind_congr fun q hq =>
          M.runFrom_succ_of_chooser_eq q hterm ⟨_, hlegal⟩
            (Subtype.ext (funext fun i => by
              show ((q i) (M.infoOf i h.trace)).1 = _
              rw [(FinDist.support_condOn _ _ (hcoord i)
                (FinDist.mem_support_pi.mp hq i)).1])) fuel
      rw [hstep, FinDist.bind_bindOnSupport_comm]
      · refine FinDist.bindOnSupport_congr fun reached realized => ?_
        have hsub' : ∀ i,
            ((mixed i).condOn (M.AnsweredBy h (M.answerAt h p) i) (hcoord i)).support ⊆
              M.ConsistentAt i (M.infoOf i (h.extend hlegal realized : E.History).trace) := by
          intro i q hq
          obtain ⟨hqanswer, hqmixed⟩ := FinDist.support_condOn _ _ (hcoord i) hq
          have hprior := hsub i hqmixed
          rw [M.consistentAt_eq_consistent_ownPlay hconstrain i] at hprior ⊢
          intro step hstep
          rw [show M.ownPlay i (h.extend hlegal realized : E.History).trace =
              M.ownPlay i (Trace.extend h.trace (fun j => ((M.answerAt h p) j).1) hlegal realized)
              from rfl, InfoSignals.ownPlay_extend] at hstep
          revert hstep
          cases hcase : ((M.answerAt h p) i).1 with
          | none => exact fun hstep => hprior step hstep
          | some action =>
            intro hstep
            rcases List.mem_cons.mp hstep with hhead | htail
            · subst hhead
              show (q (M.infoOf i h.trace)).1 = _
              rw [hqanswer, hcase]
            · exact hprior step htail
        rw [show (FinDist.pi fun i =>
                (mixed i).condOn (M.AnsweredBy h (M.answerAt h p) i) (hcoord i)).bind
              (fun r => M.runFrom r fuel (h.extend hlegal realized)) =
            M.runMixedFrom
              (fun i => (mixed i).condOn (M.AnsweredBy h (M.answerAt h p) i) (hcoord i)) fuel
              (h.extend hlegal realized) from rfl,
          ih _ _ hsub']
        refine M.runBehavioralFrom_congr fuel _ fun later hreach _ i => ?_
        cases hcase : ((M.answerAt h p) i).1 with
        | none => rw [M.condOn_answeredBy_eq_self i hlegal hcase (mixed i) (hcoord i)]
        | some action =>
          exact M.toBehavioralWith_condOn_answered hconstrain i hlegal (fun _ => rfl) realized
            hcase hreach (mixed i) (fallback i) (hcoord i)

omit [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- **From the start of play**, where the hypothesis is no hypothesis: nobody
has moved yet, so every policy is still possible. -/
theorem runMixed_toBehavioralWith (hconstrain : M.ConstrainsAlike)
    (fallback : (i : ι) → M.Policy i) (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i) :
    M.runMixed mixed fuel =
      M.runBehavioral (fun i => (mixed i).toBehavioralWith (fallback i)) fuel := by
  refine M.runMixedFrom_toBehavioralWith hconstrain fallback fuel mixed E.initHistory
    fun i q _ => ?_
  rw [M.consistentAt_eq_consistent_ownPlay hconstrain i,
    show M.ownPlay i (E.initHistory : E.History).trace = [] from rfl]
  exact fun step hstep => absurd hstep (by simp)

/-! ## The two randomizations describe the same laws

Each direction carries its own condition, and they are genuinely different
conditions. Turning local randomization into a single draw asks only that no
player be consulted twice where the choice matters; going back asks each player
to recall its own play. Neither implies the other. -/

omit [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)] in
/-- The reading with nothing supplied satisfies the theorem too: the fallback is
fixed across the induction whatever it is, and a law's own support witness is
one such choice. So the parameter is an internal device, not part of the
result. -/
theorem runMixed_toBehavioral (hconstrain : M.ConstrainsAlike) (fuel : ℕ)
    (mixed : (i : ι) → M.MixedPolicy i) :
    M.runMixed mixed fuel = M.runBehavioral (fun i => (mixed i).toBehavioral) fuel :=
  M.runMixed_toBehavioralWith hconstrain (fun i => (mixed i).support_nonempty.choose) fuel mixed

/-- **The two randomizations describe the same laws over plays.** Every law a
profile of locally randomizing players induces is induced by a single draw over
policies, and conversely. -/
theorem runBehavioral_image_eq_runMixed_image (hactsOnce : M.ActsOnceWhereItMatters)
    (hconstrain : M.ConstrainsAlike) (fuel : ℕ) :
    { law | ∃ β : (i : ι) → M.BehavioralPolicy i, M.runBehavioral β fuel = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i, M.runMixed mixed fuel = law } := by
  ext law
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨fun i => (β i).toMixed, M.runMixed_toMixed hactsOnce β fuel⟩
  · rintro ⟨mixed, rfl⟩
    exact ⟨fun i => (mixed i).toBehavioral, (M.runMixed_toBehavioral hconstrain fuel mixed).symm⟩

end Recall

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
