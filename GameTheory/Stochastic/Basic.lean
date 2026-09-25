/-
# Stochastic games

The native object stores only state, simultaneous actions, a probability-mass
transition law, and stage utility. Initial states, discount factors,
finiteness, and nonemptiness belong to the consumers that need them.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GameTheory.Stochastic

universe uι us ua

/-- A stochastic game with simultaneous pure actions and ordinary PMF state
transitions. -/
structure Game (ι : Type uι) where
  /-- Public state. -/
  State : Type us
  /-- Each player's action carrier. -/
  Action : ι → Type ua
  /-- Transition law after a pure joint action. -/
  transition : State → (∀ i, Action i) → PMF State
  /-- One-stage utility before the transition is realized. -/
  stageUtility : State → (∀ i, Action i) → ι → ℝ

-- State and action carriers intentionally have independent universes; the
-- transition and utility fields merely relate them in this record.

namespace Game

variable {ι : Type uι} (G : Game ι)

/-- The proof-free public data of one completed stochastic-game stage. -/
structure StageRecord where
  /-- State before the simultaneous action. -/
  source : G.State
  /-- Realized pure joint action. -/
  joint : ∀ i, G.Action i
  /-- State reached after the stochastic transition. -/
  target : G.State

-- A stage record inherits the game's independent state and action universes;
-- the linter sees both only through this dependent record.

/-- Reverse-chronological perfect-public-monitoring history. -/
abbrev PublicHistory := List G.StageRecord

end Game

end GameTheory.Stochastic
