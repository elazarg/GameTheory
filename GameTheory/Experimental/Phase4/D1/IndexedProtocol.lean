/-
# EXP-020: indexing the carriers instead of storing them

The signature-ownership decision was taken provisionally, with the cost to be
re-measured once a second layer had been built on it. That layer exists and
repeated the same choice: an execution protocol stores its state and action
carriers, and every concrete instance must be marked reducible or downstream
elaboration fails at some distant use site.

This file is the other side of the competition, on the sequential layer rather
than on the static one where the decision was first taken. It carries the same
interface with the carriers as *parameters*, far enough to reach the two places
the bundled form charges for: a concrete instance, and an induction over
histories.

It is recorded evidence, not API. Nothing imports it.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Experimental.Phase4.D1

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uι us ua

/-- The execution interface with its carriers indexed rather than stored. Field
for field this is the accepted structure with two fields promoted to
parameters. -/
structure IndexedProtocol (ι : Type uι) (State : Type us) (Action : ι → Type ua) where
  /-- The initial state. -/
  init : State
  /-- Who must move. -/
  active : State → ι → Prop
  /-- What an active player may choose. -/
  available : (state : State) → (i : ι) → Set (Action i)
  /-- Where execution stops. -/
  terminal : State → Prop
  /-- The stochastic transition law, accepting only legal joint actions. -/
  step : (state : State) →
    { joint : ∀ i, Option (Action i) //
      ¬ terminal state ∧ IsLegalJoint (active state) (available state) joint } →
    FinDist State
  /-- Every non-terminal state has something legal to do. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace IndexedProtocol

variable {ι : Type uι} {State : Type us} {Action : ι → Type ua}
variable (E : IndexedProtocol ι State Action)

/-- A legal joint action, including non-terminality, exactly as before. -/
def Legal (state : State) (joint : ∀ i, Option (Action i)) : Prop :=
  ¬ E.terminal state ∧ IsLegalJoint (E.active state) (E.available state) joint

/-- A chooser, exactly as before. -/
def Chooser : Type _ :=
  (state : State) → ¬ E.terminal state → { joint : ∀ i, Option (Action i) // E.Legal state joint }

open Classical in
/-- The fuelled runner, exactly as before. -/
def runFor (chooser : E.Chooser) : ℕ → State → FinDist State
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
    if hterm : E.terminal state then FinDist.pure state
    else (E.step state (chooser state hterm)).bind (runFor chooser fuel)

/-- Histories, as data, indexed by the state reached. -/
inductive Trace : State → Type _
  | start : Trace E.init
  | extend {source target : State} (prior : Trace source) (joint : ∀ i, Option (Action i))
      (isLegal : E.Legal source joint)
      (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) : Trace target

/-- How many transitions a history contains. -/
def Trace.length : ∀ {state : State}, E.Trace state → ℕ
  | _, .start => 0
  | _, .extend prior _ _ _ => prior.length + 1

end IndexedProtocol

/-! ## A concrete instance

The bundled form needs `@[reducible]` here. This one does not: the carriers
arrive as arguments, so there is no projection for anything downstream to get
stuck on. -/

/-- Where the walk can be. -/
inductive Spot | start | done
  deriving DecidableEq, Repr

/-- The only move. -/
inductive Step | go
  deriving DecidableEq, Repr

/-- One move and the walk is over. -/
def walk : IndexedProtocol Unit Spot (fun _ => Step) where
  init := .start
  active state _ := state = .start
  available _ _ := Set.univ
  terminal state := state = .done
  step state _ :=
    match state with
    | .start => FinDist.pure .done
    | .done => FinDist.pure .done
  progress := by
    rintro state hterm
    by_cases hstart : state = Spot.start
    · exact ⟨fun _ => some .go, fun _ => ⟨hstart, Set.mem_univ _⟩⟩
    · refine ⟨fun _ => none, fun _ => hstart⟩

/-! ## The induction the bundled form makes awkward

Under the accepted design an induction over histories needs its index written at
the structure's projection rather than at the carrier; written the other way it
fails inside the equation compiler. Here `Spot` *is* the index, so there is no
other way to write it. -/

theorem source_eq_start {state : Spot} {joint : Unit → Option Step}
    (isLegal : walk.Legal state joint) : state = Spot.start := by
  cases state with
  | start => rfl
  | done => exact absurd rfl isLegal.1

/-- An induction over histories, with the index written at the carrier. That is
the only spelling available here, and it is exactly the spelling that fails under
the bundled form, where the index must be written at the structure's projection
instead. -/
theorem trace_state_cases : ∀ {state : Spot} (_ : walk.Trace state),
    state = Spot.start ∨ state = Spot.done := by
  intro state trace
  induction trace with
  | start => exact Or.inl rfl
  | extend prior joint isLegal realized _ =>
    rcases source_eq_start isLegal with rfl
    exact Or.inr (FinDist.mem_support_pure.mp realized)

end GameTheory.Experimental.Phase4.D1
