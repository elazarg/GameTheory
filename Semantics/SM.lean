/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

/-! # Pointed labeled state machine

A generic state machine with label type `α`, state type `σ`, an initial state,
and a relational step function. This is domain-agnostic — no game theory,
no players, no observations.

Trace witnesses live in `Semantics.TransitionTrace`; this file only packages
the initial state with the transition relation. -/

set_option autoImplicit false

namespace Semantics

/-- Pointed labeled state machine: initial state + relational step. -/
structure SM (α σ : Type) where
  /-- Initial state. -/
  init : σ
  /-- Labeled transition relation: `step a s t` means label `a` takes state `s` to `t`. -/
  step : α → σ → σ → Prop

namespace SM

variable {α σ : Type}

end SM
end Semantics
