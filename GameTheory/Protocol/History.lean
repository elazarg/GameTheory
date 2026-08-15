/-
# Running a game along its history

`runFor` asks for a joint action given the *state*. A player choosing from what
it has seen has no such argument available: what it can condition on is the
history, and two histories can reach one state while differing in what some
player observed. A profile of such players therefore cannot drive `runFor` at
all.

This module runs the protocol along histories instead, and the central fact is
that doing so does not create a second semantics. Pushing the history law
forward along the state each history reached returns the state law exactly,
whenever the chooser is one that ignores the history. The two runners agree
wherever both are defined, so the history runner refines the state runner rather
than competing with it.

Extending a history demands evidence that the transition was realized, which is
why the recursion composes laws with a support-dependent bind: the continuation
reads the proof that its input occurs.
-/

import GameTheory.Protocol.Extraction

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
set_option linter.checkUnivs false in
/-- A state together with a history that reached it. -/
structure History where
  /-- The state the history reached. -/
  state : E.State
  /-- The history itself. -/
  trace : Trace E state

/-- A history *is* evidence that the state it reached is reachable, so nothing
about the history runner needs the induction the state runner needed. -/
theorem History.reachable_state (h : E.History) : E.Reachable h.state := ⟨h.trace⟩

/-- In a tree-shaped protocol, a complete history is exactly a reachable
state: existence supplies a trace and tree-shapedness makes that trace unique.
This is the bridge finite EFG presentations use to enumerate histories without
`Fintype.ofFinite`. -/
noncomputable def historyEquivReachableState (htree : E.IsTreeShaped) :
    E.History ≃ { state : E.State // E.Reachable state } where
  toFun history := ⟨history.state, ⟨history.trace⟩⟩
  invFun state := ⟨state.1, Classical.choice state.2⟩
  left_inv history := by
    rcases history with ⟨state, trace⟩
    dsimp [ExecutionProtocol.Reachable]
    letI : Subsingleton (E.Trace state) := htree state
    congr
    exact Subsingleton.elim _ _
  right_inv state := by
    apply Subtype.ext
    rfl

/-- A finite-state tree-shaped protocol has finitely many complete histories.
The instance is an explicit equivalence construction, not a global
`Finite`-to-`Fintype` escape hatch. -/
@[reducible]
noncomputable def historyFintype [Fintype E.State]
    (htree : E.IsTreeShaped) : Fintype E.History := by
  classical
  exact Fintype.ofEquiv { state : E.State // E.Reachable state }
    (historyEquivReachableState htree).symm

variable (E) in
/-- The empty history, at the initial state. -/
def initHistory : E.History := ⟨E.init, .start⟩

@[simp]
theorem initHistory_state : (E.initHistory).state = E.init := rfl

/-- Extend a history by one realized legal transition. -/
def History.extend (h : E.History) {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal h.state joint) {target : E.State}
    (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support) : E.History :=
  ⟨target, h.trace.extend joint isLegal realized⟩

@[simp]
theorem History.extend_state (h : E.History) {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal h.state joint) {target : E.State}
    (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support) :
    (h.extend isLegal realized).state = target := rfl

/-! ## External values on realized histories

A protocol describes legal execution and chance, not what a transition is
worth to a particular consumer.  Cumulative values therefore take the
transition valuation as an argument.  This keeps rewards, costs, and
application-specific utilities out of the shared execution object while still
giving every sequential language the same checked fold over realized traces.
-/

/-- Fold an additive transition value along an indexed realized trace. -/
def Trace.valueSum {α : Type _} [Zero α] [Add α] (value : E.StepEvent → α) :
    ∀ {state : E.State}, E.Trace state → α
  | _, .start => 0
  | _, .extend prior joint isLegal realized =>
      prior.valueSum value + value ⟨_, joint, isLegal, _, realized⟩

@[simp]
theorem Trace.valueSum_start {α : Type _} [Zero α] [Add α]
    (value : E.StepEvent → α) :
    (Trace.start : E.Trace E.init).valueSum value = 0 := rfl

@[simp]
theorem Trace.valueSum_extend {α : Type _} [Zero α] [Add α]
    (value : E.StepEvent → α) {source target : E.State} (prior : E.Trace source)
    (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    (Trace.extend prior joint isLegal realized).valueSum value =
      prior.valueSum value + value ⟨source, joint, isLegal, target, realized⟩ := rfl

/-- The cumulative externally supplied value of a complete history. -/
def History.valueSum {α : Type _} [Zero α] [Add α] (h : E.History)
    (value : E.StepEvent → α) : α :=
  h.trace.valueSum value

@[simp]
theorem History.valueSum_init {α : Type _} [Zero α] [Add α]
    (value : E.StepEvent → α) : (E.initHistory).valueSum value = 0 := rfl

@[simp]
theorem History.valueSum_extend {α : Type _} [Zero α] [Add α]
    (h : E.History) (value : E.StepEvent → α) {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal h.state joint) {target : E.State}
    (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support) :
    (h.extend isLegal realized).valueSum value =
      h.valueSum value + value ⟨h.state, joint, isLegal, target, realized⟩ := rfl

/-- Whether a complete history ends at a terminal execution state.  This is a
history-facing view of the protocol's one terminality predicate, not a second
notion of stopping. -/
def History.isTerminal (h : E.History) : Prop := E.terminal h.state

/-- The complete histories at which execution has stopped. -/
def terminalHistories (E : ExecutionProtocol ι) : Set E.History :=
  { h | h.isTerminal }

theorem mem_terminalHistories_iff {h : E.History} :
    h ∈ E.terminalHistories ↔ h.isTerminal := Iff.rfl

/-- A legal joint action from a history proves that its endpoint is not
terminal. -/
theorem History.not_isTerminal_of_legal (h : E.History)
    {joint : ∀ i, Option (E.Action i)} (hlegal : E.Legal h.state joint) :
    ¬ h.isTerminal := hlegal.1

/-- At a non-terminal history endpoint, protocol progress supplies a legal
joint action. -/
theorem History.exists_legal_of_not_terminal (h : E.History)
    (hterm : ¬ h.isTerminal) : ∃ joint, E.Legal h.state joint :=
  E.exists_legal hterm

variable (E) in
/-- A chooser that may read the history, not only the state it reached. -/
def HistoryChooser : Type _ :=
  (h : E.History) → ¬ E.terminal h.state →
    { joint : ∀ i, Option (E.Action i) // E.Legal h.state joint }

/-- Every state-indexed chooser is a history-indexed one that discards the
history. -/
def Chooser.toHistoryChooser (chooser : E.Chooser) : E.HistoryChooser :=
  fun h hterm => chooser h.state hterm

open Classical in
/-- Run for at most `fuel` steps, recording the history rather than only the
state it reached. -/
def runHistoryFor (chooser : E.HistoryChooser) : ℕ → E.History → FinDist E.History
  | 0, h => FinDist.pure h
  | fuel + 1, h =>
    if hterm : E.terminal h.state then FinDist.pure h
    else
      (E.step h.state (chooser h hterm)).bindOnSupport fun _ realized =>
        runHistoryFor chooser fuel (h.extend (chooser h hterm).2 realized)

@[simp]
theorem runHistoryFor_zero (chooser : E.HistoryChooser) (h : E.History) :
    E.runHistoryFor chooser 0 h = FinDist.pure h := rfl

/-- Terminal histories are absorbing, exactly as terminal states are. -/
@[simp]
theorem runHistoryFor_of_terminal (chooser : E.HistoryChooser) (fuel : ℕ) {h : E.History}
    (hterm : E.terminal h.state) : E.runHistoryFor chooser fuel h = FinDist.pure h := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [runHistoryFor, dif_pos hterm]

theorem runHistoryFor_succ_of_not_terminal (chooser : E.HistoryChooser) (fuel : ℕ)
    {h : E.History} (hterm : ¬ E.terminal h.state) :
    E.runHistoryFor chooser (fuel + 1) h =
      (E.step h.state (chooser h hterm)).bindOnSupport fun _ realized =>
        E.runHistoryFor chooser fuel (h.extend (chooser h hterm).2 realized) := by
  rw [runHistoryFor, dif_neg hterm]

/-- **The state law is the history law's shadow.** For a chooser that ignores
the history, forgetting the history turns the history run law into the state run
law. Every theorem about the state law therefore transfers, and what the history
law adds is exactly what the state law had discarded. -/
theorem map_state_runHistoryFor (chooser : E.Chooser) :
    ∀ (fuel : ℕ) (h : E.History),
      FinDist.map History.state (E.runHistoryFor chooser.toHistoryChooser fuel h) =
        E.runFor chooser fuel h.state := by
  intro fuel
  induction fuel with
  | zero => intro h; simp
  | succ fuel ih =>
    intro h
    by_cases hterm : E.terminal h.state
    · rw [runHistoryFor_of_terminal _ _ hterm, runFor_of_terminal _ _ hterm, FinDist.map_pure]
    · rw [runHistoryFor_succ_of_not_terminal _ fuel hterm,
        runFor_succ_of_not_terminal chooser fuel hterm, FinDist.map_bindOnSupport]
      exact FinDist.bindOnSupport_eq_bind_of_eq_on_support fun _ _ => ih _

variable (E) in
/-- The histories a run of at most `fuel` steps can pass through, starting from
`h`. This over-approximates what any particular chooser reaches, which is what
makes it usable as a hypothesis: it does not depend on the chooser. -/
inductive ReachesWithin : ℕ → E.History → E.History → Prop
  | /-- Nowhere to go is somewhere reachable. -/
    refl (fuel : ℕ) (h : E.History) : ReachesWithin fuel h h
  | /-- One realized legal step, then the rest. -/
    step {fuel : ℕ} {h target : E.History} (joint : ∀ i, Option (E.Action i))
      (isLegal : E.Legal h.state joint) {reached : E.State}
      (realized : reached ∈ (E.step h.state ⟨joint, isLegal⟩).support)
      (rest : ReachesWithin fuel (h.extend isLegal realized) target) :
      ReachesWithin (fuel + 1) h target

/-- With no fuel there is nowhere to go, so this really does bound how far play
can get rather than relating everything to everything. -/
theorem reachesWithin_zero_iff {h target : E.History} :
    E.ReachesWithin 0 h target ↔ target = h := by
  refine ⟨fun hreach => ?_, fun hequal => by subst hequal; exact .refl 0 target⟩
  cases hreach
  rfl

/-- A bounded reachability witness remains valid when more fuel is available. -/
theorem ReachesWithin.mono {fuel extra : ℕ} {start target : E.History}
    (hreach : E.ReachesWithin fuel start target) :
    E.ReachesWithin (fuel + extra) start target := by
  induction hreach with
  | refl fuel history => exact .refl _ history
  | step joint isLegal realized rest ih =>
      have hstep := ReachesWithin.step joint isLegal realized ih
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- Bounded semantic reachability composes, with the fuel budgets adding. -/
theorem ReachesWithin.trans {firstFuel secondFuel : ℕ}
    {first middle last : E.History}
    (hfirst : E.ReachesWithin firstFuel first middle)
    (hsecond : E.ReachesWithin secondFuel middle last) :
    E.ReachesWithin (firstFuel + secondFuel) first last := by
  induction hfirst with
  | refl fuel history =>
      simpa [Nat.add_comm] using hsecond.mono (extra := fuel)
  | step joint isLegal realized rest ih =>
      have hstep := ReachesWithin.step joint isLegal realized (ih hsecond)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- Semantic reachability never shortens the canonical trace. -/
theorem ReachesWithin.trace_length_le {fuel : ℕ}
    {start target : E.History}
    (hreach : E.ReachesWithin fuel start target) :
    start.trace.length ≤ target.trace.length := by
  induction hreach with
  | refl => exact le_rfl
  | step joint isLegal realized rest ih =>
      exact le_trans (Nat.le_succ _) (by simpa [History.extend, Trace.length] using ih)

/-- A reachable history at the same trace depth is the starting history. -/
theorem ReachesWithin.eq_of_trace_length_eq {fuel : ℕ}
    {start target : E.History}
    (hreach : E.ReachesWithin fuel start target)
    (hlength : start.trace.length = target.trace.length) :
    target = start := by
  cases hreach with
  | refl => rfl
  | step joint isLegal realized rest =>
      have hle := rest.trace_length_le
      simp only [History.extend, Trace.length] at hle
      omega

/-- Every complete history is semantically reachable from the initial history;
its indexed trace supplies the exact transition budget. -/
theorem reachesWithin_from_init (h : E.History) :
    E.ReachesWithin h.trace.length E.initHistory h := by
  rcases h with ⟨state, trace⟩
  induction trace with
  | start => exact .refl 0 E.initHistory
  | @extend source target prior joint isLegal realized ih =>
      have hone : E.ReachesWithin 1 ⟨source, prior⟩
          ⟨target, Trace.extend prior joint isLegal realized⟩ :=
        .step joint isLegal realized (.refl 0 _)
      simpa [Trace.length] using ih.trans hone

/-- Choosers agreeing on every history induce the same history law. -/
theorem runHistoryFor_congr {first second : E.HistoryChooser}
    (hagree : ∀ (h : E.History) (hterm : ¬ E.terminal h.state), first h hterm = second h hterm) :
    ∀ (fuel : ℕ) (h : E.History),
      E.runHistoryFor first fuel h = E.runHistoryFor second fuel h := by
  intro fuel
  induction fuel with
  | zero => intro h; rfl
  | succ fuel ih =>
    intro h
    by_cases hterm : E.terminal h.state
    · rw [runHistoryFor_of_terminal _ _ hterm, runHistoryFor_of_terminal _ _ hterm]
    · rw [runHistoryFor_succ_of_not_terminal first fuel hterm,
        runHistoryFor_succ_of_not_terminal second fuel hterm, hagree h hterm]
      exact FinDist.bindOnSupport_congr fun _ _ => ih _

end ExecutionProtocol

end GameTheory.Protocol
