/-
# Strategic-form compilation

The bridge from the protocol layer to the static core: a protocol plus a
horizon compiles to a `GameForm` whose strategies are per-player policies and
whose outcome law is the run law.

Two deliberate restrictions, both recorded rather than hidden.

* Strategies here are *state*-indexed (`StatePolicy`), which is the
  perfect-information case. Information-local policies are history-indexed,
  because `InfoSignals.infoOf` recurses over `Trace`, and folding those into a
  `Chooser` needs a history-indexed runner, which does not yet exist.
* The compiled form carries a fuel argument. `ExecutionProtocol.StopsWithin`
  turns that into a horizon-independent law.

Once compiled, every static concept applies unchanged: `IsNash`,
`IsCoarseCorrelatedEq`, dominance, and the executable frontend all take a
`GameForm` and a preference, and none of them knows a protocol exists.
-/

import GameTheory.Protocol.Extraction
import GameTheory.Core.Form

noncomputable section

namespace GameTheory.Protocol

open Probability GameTheory

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- What one player does wherever it is active. This is the
perfect-information strategy: it may read the state, because at perfect
information the state is what the player knows. -/
def StatePolicy (i : ι) : Type _ :=
  (state : E.State) → E.active state i → { a : E.Action i // a ∈ E.available state i }

open Classical in
/-- The joint action a profile of state policies produces: active players act,
inactive players stand down. -/
def jointOf (profile : (i : ι) → E.StatePolicy i) (state : E.State) :
    ∀ i, Option (E.Action i) :=
  fun i => if hactive : E.active state i then some (profile i state hactive).1 else none

open Classical in
theorem jointOf_isLegal (profile : (i : ι) → E.StatePolicy i) (state : E.State) :
    IsLegalJoint (E.active state) (E.available state) (E.jointOf profile state) := by
  intro i
  by_cases hactive : E.active state i
  · simp [jointOf, hactive, (profile i state hactive).2]
  · simp [jointOf, hactive]

/-- A profile of state policies is a chooser. -/
def chooserOf (profile : (i : ι) → E.StatePolicy i) : E.Chooser :=
  fun state hterm => ⟨E.jointOf profile state, hterm, E.jointOf_isLegal profile state⟩

variable (E) in
/-- The signature of the compiled game: strategies are state policies, outcomes
are the states play can stop in. -/
abbrev strategicSignature : GameSignature ι where
  Strategy := E.StatePolicy
  Outcome := E.State

variable (E) in
/-- **The compilation.** A protocol and a horizon become a `GameForm`.

Reducible so that the compiled form's outcome carrier reduces to the protocol's
state type; without it, static concepts stated over the carrier do not match. -/
@[reducible]
def toGameForm (horizon : ℕ) : GameForm ι where
  sig := E.strategicSignature
  play profile := E.runFor (E.chooserOf profile) horizon E.init

/-- The named evaluation fact. A certificate consumer must reuse *this* rather
than reprove the run law. -/
@[simp]
theorem toGameForm_play (horizon : ℕ) (profile : Profile E.strategicSignature) :
    (E.toGameForm horizon).play profile =
      E.runFor (E.chooserOf profile) horizon E.init := rfl

@[simp]
theorem toGameForm_sig (horizon : ℕ) :
    (E.toGameForm horizon).sig = E.strategicSignature := rfl

/-- Past a horizon at which play has stopped, the compiled form no longer
depends on the horizon. This is what turns a fuelled compilation into a
well-defined strategic form. -/
theorem toGameForm_play_eq_of_stopsWithin {horizon fuel : ℕ}
    (profile : Profile E.strategicSignature)
    (hstop : E.StopsWithin (E.chooserOf profile) horizon E.init) (hle : horizon ≤ fuel) :
    (E.toGameForm fuel).play profile = (E.toGameForm horizon).play profile :=
  runFor_eq_of_stopsWithin_le hstop hle

/-- Only behaviour at reachable decision sites is visible in the compiled form.
This is the compiled counterpart of `runFor_congr_of_restrict_eq`. -/
theorem toGameForm_play_congr {horizon : ℕ}
    {first second : Profile E.strategicSignature}
    (hagree : Chooser.restrict (E.chooserOf first) = Chooser.restrict (E.chooserOf second)) :
    (E.toGameForm horizon).play first = (E.toGameForm horizon).play second :=
  runFor_congr_of_restrict_eq hagree horizon reachable_init

end ExecutionProtocol

end GameTheory.Protocol
