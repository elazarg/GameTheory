/-
# Execution protocols

Legal actions, stochastic transitions, terminality, and traces. This layer knows
nothing about who observes what; the information layer sits on top of it.

Three requirements shape the interface.

* **No impossible total chooser.** `Chooser` is asked for a joint action only at
  a *non-terminal* state, so run semantics inspects terminality before
  requesting an action.
* **Chance is carried by the transition law.** A state where nobody is active is
  legal for the no-op joint action, and `step` may still return a nondegenerate
  law. A `none` mover with no probability law is not chance semantics.
* **Histories are data.** `Trace` is `Type`-valued, so `Subsingleton (Trace E s)`
  is a real uniqueness statement. A `Prop`-valued reachability relation would
  make that vacuous under proof irrelevance.

Legality is a definition, not a field: a joint action is legal at a state when
play has not stopped there and every active player supplies an available action.
A protocol therefore cannot declare a legality relation inconsistent with its own
`active` and `available`.
-/

import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua

variable {ι : Type uι}

/-- A joint action is legal when every active player supplies an available
action and every inactive player supplies none. -/
def IsLegalJoint {Action : ι → Type ua} (active : ι → Prop)
    (available : (i : ι) → Set (Action i)) (joint : ∀ i, Option (Action i)) : Prop :=
  ∀ i, match joint i with
    | some a => active i ∧ a ∈ available i
    | none => ¬ active i

set_option linter.checkUnivs false in
/-- Legal actions, stochastic transitions, and terminality. State and action
universes stay independent. -/
structure ExecutionProtocol (ι : Type uι) where
  /-- The execution state space. -/
  State : Type us
  /-- Each player's action carrier. -/
  Action : ι → Type ua
  /-- The initial state. -/
  init : State
  /-- Who must move. Proposition-valued: enumerating movers is not part of proof
  semantics. -/
  active : State → ι → Prop
  /-- What an active player may choose. -/
  available : (state : State) → (i : ι) → Set (Action i)
  /-- Where execution stops. A `Prop`, never a stored horizon. -/
  terminal : State → Prop
  /-- The stochastic transition law. It accepts only legal joint actions, and
  legality includes non-terminality, so `step` cannot be applied at a terminal
  state at all. -/
  step : (state : State) →
    { joint : ∀ i, Option (Action i) //
      ¬ terminal state ∧ IsLegalJoint (active state) (available state) joint } →
    FinDist State
  /-- Every non-terminal state has something legal to do. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace ExecutionProtocol

variable (E : ExecutionProtocol ι)

/-- A joint action is legal at a state when execution has not stopped there and
every active player supplies an available action. -/
def Legal (state : E.State) (joint : ∀ i, Option (E.Action i)) : Prop :=
  ¬ E.terminal state ∧ IsLegalJoint (E.active state) (E.available state) joint

/-- Terminal states have no legal joint action.

`active` is therefore unconstrained at terminal states: a protocol may declare
somebody active where play has stopped, and nothing depends on whether it does,
because no legal action exists there either way. -/
theorem terminal_no_legal {state : E.State} (hterm : E.terminal state)
    (joint : ∀ i, Option (E.Action i)) : ¬ E.Legal state joint :=
  fun hlegal => hlegal.1 hterm

/-- Non-terminal states always have one. -/
theorem exists_legal {state : E.State} (hterm : ¬ E.terminal state) :
    ∃ joint, E.Legal state joint := by
  obtain ⟨joint, hjoint⟩ := E.progress state hterm
  exact ⟨joint, hterm, hjoint⟩

/-- The no-op joint action. -/
def noop : ∀ i, Option (E.Action i) := fun _ => none

/-- The no-op is legal exactly where execution continues and nobody is active.
This is the canonical chance or administrative step; the randomness lives in
`step`. -/
theorem noop_isLegal {state : E.State} (hterm : ¬ E.terminal state)
    (hidle : ∀ i, ¬ E.active state i) : E.Legal state E.noop :=
  ⟨hterm, fun i => hidle i⟩

/-- A chance state: execution continues, but no player moves. -/
def IsChance (state : E.State) : Prop :=
  ¬ E.terminal state ∧ ∀ i, ¬ E.active state i

/-- The law a chance state induces. -/
def chanceLaw {state : E.State} (hchance : E.IsChance state) : FinDist E.State :=
  E.step state ⟨E.noop, E.noop_isLegal hchance.1 hchance.2⟩

/-! ## Run semantics

The chooser is a *partial* object by construction: it is applied only where a
legal joint action is known to exist. -/

/-- A policy for the whole protocol. Terminal states are never queried, so no
total legal-joint chooser is required anywhere. -/
def Chooser : Type _ :=
  (state : E.State) → ¬ E.terminal state →
    { joint : ∀ i, Option (E.Action i) // E.Legal state joint }

open Classical in
/-- Run for at most `fuel` steps, stopping at terminal states. -/
def runFor (chooser : E.Chooser) : ℕ → E.State → FinDist E.State
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
    if hterm : E.terminal state then FinDist.pure state
    else (E.step state (chooser state hterm)).bind (runFor chooser fuel)

variable {E}

@[simp]
theorem runFor_zero (chooser : E.Chooser) (state : E.State) :
    E.runFor chooser 0 state = FinDist.pure state := rfl

/-- Terminal states are absorbing: the run stops, it does not ask for an
action. -/
@[simp]
theorem runFor_of_terminal (chooser : E.Chooser) (fuel : ℕ) {state : E.State}
    (hterm : E.terminal state) : E.runFor chooser fuel state = FinDist.pure state := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [runFor, dif_pos hterm]

theorem runFor_succ_of_not_terminal (chooser : E.Chooser) (fuel : ℕ) {state : E.State}
    (hterm : ¬ E.terminal state) :
    E.runFor chooser (fuel + 1) state =
      (E.step state (chooser state hterm)).bind (E.runFor chooser fuel) := by
  rw [runFor, dif_neg hterm]

/-- A chance state is stepped through, not stopped at. -/
theorem runFor_succ_of_chance (chooser : E.Chooser) (fuel : ℕ) {state : E.State}
    (hchance : E.IsChance state) :
    E.runFor chooser (fuel + 1) state =
      (E.chanceLaw hchance).bind (E.runFor chooser fuel) := by
  have hidle : chooser state hchance.1 = ⟨E.noop, E.noop_isLegal hchance.1 hchance.2⟩ := by
    refine Subtype.ext (funext fun i => ?_)
    have hleg := (chooser state hchance.1).2.2 i
    cases hcase : (chooser state hchance.1).1 i with
    | none => rfl
    | some a =>
      rw [hcase] at hleg
      exact absurd hleg.1 (hchance.2 i)
  rw [runFor_succ_of_not_terminal chooser fuel hchance.1, chanceLaw]
  exact congrArg (fun d => (E.step state d).bind (E.runFor chooser fuel)) hidle

/-- Running `m + n` steps is running `m` and then `n`. -/
theorem runFor_add (chooser : E.Chooser) (first second : ℕ) (state : E.State) :
    E.runFor chooser (first + second) state =
      (E.runFor chooser first state).bind (E.runFor chooser second) := by
  induction first generalizing state with
  | zero => simp [FinDist.pure_bind]
  | succ first ih =>
    by_cases hterm : E.terminal state
    · rw [runFor_of_terminal chooser _ hterm, runFor_of_terminal chooser _ hterm,
        FinDist.pure_bind, runFor_of_terminal chooser second hterm]
    · rw [show first + 1 + second = (first + second) + 1 by omega,
        runFor_succ_of_not_terminal chooser _ hterm,
        runFor_succ_of_not_terminal chooser _ hterm, FinDist.bind_bind]
      exact FinDist.bind_congr fun s _ => ih s

variable (E) in
/-- Under `chooser`, everything reachable from `state` in `horizon` steps has
already stopped. This is the certificate a general-state protocol supplies in
place of an inductive finite semantics. -/
def StopsWithin (chooser : E.Chooser) (horizon : ℕ) (state : E.State) : Prop :=
  ∀ reached ∈ (E.runFor chooser horizon state).support, E.terminal reached

/-- Once the run has stopped, extra fuel changes nothing: a bounded-horizon
certificate turns the fuelled runner into a total evaluator. -/
theorem runFor_eq_of_stopsWithin {chooser : E.Chooser} {horizon : ℕ} {state : E.State}
    (hstop : E.StopsWithin chooser horizon state) (extra : ℕ) :
    E.runFor chooser (horizon + extra) state = E.runFor chooser horizon state := by
  rw [runFor_add]
  refine Eq.trans (FinDist.bind_congr fun reached hreached => ?_) (FinDist.bind_pure _)
  exact runFor_of_terminal chooser extra (hstop reached hreached)

/-- Hence the run law is the same for every fuel past the horizon. -/
theorem runFor_eq_of_stopsWithin_le {chooser : E.Chooser} {horizon fuel : ℕ}
    {state : E.State} (hstop : E.StopsWithin chooser horizon state)
    (hle : horizon ≤ fuel) :
    E.runFor chooser fuel state = E.runFor chooser horizon state := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact runFor_eq_of_stopsWithin hstop extra

/-! ## Realized transitions and histories -/

variable (E) in
set_option linter.checkUnivs false in
/-- One realized legal transition. -/
structure StepEvent where
  /-- The state the transition leaves. -/
  source : E.State
  /-- The joint action taken. -/
  joint : ∀ i, Option (E.Action i)
  /-- Its legality at `source`. -/
  isLegal : E.Legal source joint
  /-- The state the transition reaches. -/
  target : E.State
  /-- The target has positive probability under the transition law. -/
  realized : target ∈ (E.step source ⟨joint, isLegal⟩).support

variable (E) in
/-- A history: the *data* of a run from `init` ending at a state. Because this
is `Type`-valued, `Subsingleton (Trace E state)` is a genuine uniqueness
statement rather than a proof-irrelevance artifact. -/
inductive Trace : E.State → Type _
  | /-- The empty history at the initial state. -/
    start : Trace E.init
  | /-- Extend a history by one realized legal transition. -/
    extend {source target : E.State} (prior : Trace source)
      (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint)
      (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) : Trace target

/-- How many transitions a history contains. -/
def Trace.length : ∀ {state : E.State}, Trace E state → ℕ
  | _, .start => 0
  | _, .extend prior _ _ _ => prior.length + 1

variable (E) in
/-- Every history of at least `horizon` steps has already stopped. A predicate
about reachable traces, never a stored field. -/
def BoundedHorizon (horizon : ℕ) : Prop :=
  ∀ (state : E.State) (trace : Trace E state), horizon ≤ trace.length → E.terminal state

variable (E) in
/-- The arena is tree-shaped: every reachable state has exactly one history.
This is the premise tree extraction needs, and a merging arena refutes it. -/
def IsTreeShaped : Prop := ∀ state : E.State, Subsingleton (Trace E state)

end ExecutionProtocol

end GameTheory.Protocol
