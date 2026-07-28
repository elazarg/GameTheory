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
      (∀ (h' : E.History), ExecutionProtocol.ReachesWithin E fuel h h' →
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
        Subtype.ext (funext fun i => hagree h (.refl _ _) i)
      rw [runFrom, runFrom,
        ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm,
        ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm, hhere]
      refine FinDist.bindOnSupport_congr fun target realized => ?_
      exact ih _ fun h' hreach i => hagree h' (.step _ _ realized hreach) i

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

/-- **An information state a player has acted at never returns.** This is the
form the no-revisit condition is used in: having moved at `h`, the player meets
that information state at no later history at which it moves again. -/
theorem infoOf_ne_of_actsOnce (hactsOnce : M.ActsOnceAtEachInfoState) (i : ι)
    {h later : E.History} {fuel : ℕ}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    {reached : E.State} (realized : reached ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    (hacts : (joint i).isSome)
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    {laterJoint : ∀ j, Option (E.Action j)} (laterLegal : E.Legal later.state laterJoint)
    {laterReached : E.State}
    (laterRealized : laterReached ∈ (E.step later.state ⟨laterJoint, laterLegal⟩).support)
    (hactsLater : (laterJoint i).isSome) :
    M.infoOf i later.trace ≠ M.infoOf i h.trace := by
  intro hsame
  have hnodup := hactsOnce i (later.extend laterLegal laterRealized).trace
  have hstep : M.actedAt i (later.extend laterLegal laterRealized).trace =
      M.infoOf i later.trace :: M.actedAt i later.trace := by
    show M.actedAt i (Trace.extend _ laterJoint laterLegal laterRealized) = _
    rw [InfoSignals.actedAt]
    cases hcase : laterJoint i with
    | none => rw [hcase] at hactsLater; exact absurd hactsLater (by simp)
    | some action => rfl
  rw [hstep] at hnodup
  refine (List.nodup_cons.mp hnodup).1 ?_
  have hsuffix := M.actedAt_isSuffix_of_reachesWithin i hreach
  have hhead : M.infoOf i h.trace ∈ M.actedAt i (h.extend isLegal realized).trace := by
    show M.infoOf i h.trace ∈ M.actedAt i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.actedAt]
    cases hcase : joint i with
    | none => rw [hcase] at hacts; exact absurd hacts (by simp)
    | some action => exact List.mem_cons_self
  rw [hsame]
  exact hsuffix.subset hhead

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

/-- A behavioral profile, as a chooser. -/
def randomizedChooser (policies : (i : ι) → M.BehavioralPolicy i) : E.RandomizedChooser :=
  fun h hterm => M.behavioralJoint policies h.trace hterm

/-- The law over histories a behavioral profile induces from a given history. -/
def runBehavioralFrom (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) (h : E.History) :
    FinDist E.History :=
  E.runRandomizedFor (M.randomizedChooser policies) fuel h

/-- The law over histories a behavioral profile induces from the start. -/
def runBehavioral (policies : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) : FinDist E.History :=
  M.runBehavioralFrom policies fuel E.initHistory

/-- Behavioral profiles that answer alike at every history a run of this length
can pass through induce the same law. This is what makes a change to a
coordinate the continuation never consults invisible. -/
theorem runBehavioralFrom_congr {first second : (i : ι) → M.BehavioralPolicy i} :
    ∀ (fuel : ℕ) (h : E.History),
      (∀ (h' : E.History), ExecutionProtocol.ReachesWithin E fuel h h' →
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
        rw [randomizedChooser, randomizedChooser, behavioralJoint, behavioralJoint]
        exact congrArg _ (congrArg FinDist.pi (funext fun i => hagree h (.refl _ _) i))
      rw [runBehavioralFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm,
        ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ fuel hterm, hhere]
      refine FinDist.bind_congr fun draw _ => FinDist.bindOnSupport_congr fun target realized => ?_
      exact ih _ fun h' hreach i => hagree h' (.step _ _ realized hreach) i

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
