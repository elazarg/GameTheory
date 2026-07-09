/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Semantics.TransitionTrace

/-!
# Semantics.Simulation
-/

set_option autoImplicit false

namespace Semantics
namespace Transition

variable {α β σ τ : Type*}

/-- Homomorphic simulation by state/label maps. -/
structure HomSimulation
    (step₁ : α → σ → σ → Prop)
    (step₂ : β → τ → τ → Prop) where
  stateMap : σ → τ
  labelMap : α → β
  step :
    ∀ {a : α} {s s' : σ},
      step₁ a s s' → step₂ (labelMap a) (stateMap s) (stateMap s')

namespace HomSimulation

theorem reachBy_map
    {step₁ : α → σ → σ → Prop}
    {step₂ : β → τ → τ → Prop}
    (sim : HomSimulation step₁ step₂)
    {w : List α} {s t : σ}
    (h : ReachBy step₁ w s t) :
    ReachBy step₂ (w.map sim.labelMap) (sim.stateMap s) (sim.stateMap t) := by
  induction h with
  | nil s =>
      simp
  | @cons a rest s u t hs hrest ih =>
      simpa using ReachBy.cons (sim.step hs) ih

end HomSimulation

end Transition
end Semantics
