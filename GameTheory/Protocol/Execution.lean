/-
# Execution protocols

The execution half of D6: legal actions, stochastic transitions, terminality,
and traces. It knows nothing about who observes what; the information layer is
separate and is layered on top.

Three RFC requirements shape the interface.

* **No impossible total chooser.** `Chooser` is asked for a joint action only at
  a *non-terminal* state, so run semantics inspects terminality before
  requesting an action (RFC 9.1.6).
* **Chance is carried by the transition law.** A state where nobody is active is
  legal for the no-op joint action, and `step` may still return a nondegenerate
  law. A `none` mover with no probability law is not chance semantics.
* **Histories are data.** `Trace` is `Type`-valued, so `Subsingleton (Trace E s)`
  is a real uniqueness statement. The v1 snapshot's `Subsingleton (Reachable s t)`
  was vacuous under proof irrelevance; this is the repair.

Legality is a *definition* here rather than a stored field plus a consistency
law, which removes one field and one law from the RFC's sketch.
-/

import GameTheory.Probability.FinDist

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua

variable {ι : Type uι}

/-- A joint action is legal when every active player supplies an available
action and every inactive player supplies none. This is the RFC's
`legal_iff_active_available`, stated as a definition. -/
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
  semantics (D9). -/
  active : State → ι → Prop
  /-- What an active player may choose. -/
  available : (state : State) → (i : ι) → Set (Action i)
  /-- Where execution stops. A `Prop`, never a stored horizon. -/
  terminal : State → Prop
  /-- Nobody chooses at a terminal state. -/
  terminal_inactive : ∀ state, terminal state → ∀ i, ¬ active state i
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

/-- Terminal states have no legal joint action. In the RFC's sketch this was an
assumed field; here it is a theorem. -/
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
total legal-joint chooser is required anywhere (RFC 9.1.6). -/
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
