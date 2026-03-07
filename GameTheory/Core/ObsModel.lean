import GameTheory.Core.LSM

/-! # Observation model interface

A minimal interface for observation-based game models. Any representation
(InfoModel, EFG, etc.) can provide an `ObsModel` to use downstream theorems
(e.g. correlated realization, Kuhn's theorem). -/

set_option autoImplicit false

namespace GameTheory

/-- Observation model: per-player observation function on machine states.
Everything else (local traces, observation equivalence, profile types) is derived. -/
structure ObsModel {ι : Type} (M : LSM ι) where
  /-- Player-specific observation type. -/
  Obs : ι → Type
  /-- Player-specific observation function. -/
  observe : (i : ι) → M.State → Obs i

end GameTheory
