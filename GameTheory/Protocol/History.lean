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

open Probability

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
