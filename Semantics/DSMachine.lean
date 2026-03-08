import Math.ProbabilityMassFunction

/-! ## Dependent-alphabet stochastic machine

A `DSMachine` is a stochastic state machine whose label (input) type depends on
the current state. This is the minimal abstraction for systems where the set of
available actions varies with state — e.g., observation-indexed actions in game
theory.
-/

/-- Dependent-alphabet stochastic machine. The label type may vary with the state. -/
structure DSMachine (σ : Type) (Label : σ → Type) where
  /-- Initial state. -/
  init : σ
  /-- Stochastic transition: given state `s` and label `l : Label s`,
  produce a distribution over next states. -/
  step : (s : σ) → Label s → PMF σ
