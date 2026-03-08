import GameTheory.Model.SemanticForm

/-!
# GameTheory.Model.PolicyStep

Experimental enabled-player semantics with a minimal control source language.

The current `SM`-based `InfoModel` uses

- `step : (∀ i, Option (Act i)) -> σ -> σ -> Prop`

This draft explores a tighter alternative:

- enabled players are explicit in the machine
- actions are supplied only for enabled coordinates
- control over an enabled coordinate is either:
  - still chosen by the player at execution time
  - hard-coded as a random law, tagged by visibility

This is only a design sketch. It does not replace `InfoModel` or
`InfoGame`.
-/

namespace GameTheory

/-- Visibility class of a hard-coded random source. -/
inductive Visibility where
  | pub
  | priv
deriving DecidableEq, Repr

/-- Minimal source of control for one enabled coordinate. -/
inductive ActionSource (α : Type) where
  | player
  | random : Visibility → PMF α → ActionSource α

/-- Experimental latent-state machine with state-dependent enabled players. -/
structure EnabledLSM (ι : Type) where
  State : Type
  Act : ι → Type
  init : State
  Enabled : State → ι → Prop
  step : (s : State) → ((i : ι) → Enabled s i → Act i) → State → Prop

namespace EnabledLSM

variable {ι : Type}

/-- Full action on exactly the coordinates enabled at state `s`. -/
abbrev EnabledAction (M : EnabledLSM ι) (s : M.State) : Type :=
  (i : ι) → M.Enabled s i → M.Act i

/-- State-dependent source specification for the enabled coordinates. -/
abbrev SourceSpec (M : EnabledLSM ι) (s : M.State) : Type :=
  (i : ι) → M.Enabled s i → ActionSource (M.Act i)

/-- The open coordinates at state `s`: enabled coordinates whose source is
`player`. -/
def IsOpen (M : EnabledLSM ι) {s : M.State} (src : SourceSpec M s) (i : ι) (hi : M.Enabled s i) :
    Prop :=
  src i hi = .player

/-- Runtime action is supplied only for enabled coordinates whose source is
still `player`. -/
abbrev OpenAction (M : EnabledLSM ι) (s : M.State) (src : SourceSpec M s) : Type :=
  (i : ι) → (hi : M.Enabled s i) → M.IsOpen src i hi → M.Act i

/-- A one-step execution interface parameterized by a source specification:

- `src` says, for each enabled coordinate, whether it remains player-controlled
  or has been hard-coded to a random source
- `ao` supplies runtime choices only on the player-controlled coordinates

The stochastic interpretation of the `random` case is intentionally left out of
this file. This is just the structural interface. -/
abbrev ControlledStep (M : EnabledLSM ι) : Type :=
  (s : M.State) →
  (src : SourceSpec M s) →
  OpenAction M s src →
  M.State →
  Prop

end EnabledLSM

end GameTheory
