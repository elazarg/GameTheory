import Semantics.SM

/-! # Observation model

Multi-agent observation model extending `Semantics.SM`.
State type `σ` and per-player action type `Act` are parameters;
the SM label type is the joint action profile `∀ i, Option (Act i)`. -/

set_option autoImplicit false

namespace GameTheory

/-- Multi-agent observation model extending a pointed labeled state machine.
Adds per-player observation types and functions. -/
structure ObsModel (ι σ : Type) (Act : ι → Type)
    extends Semantics.SM (∀ i, Option (Act i)) σ where
  /-- Per-player observation type. -/
  Obs : ι → Type
  /-- Per-player observation function on states. -/
  observe : (i : ι) → σ → Obs i

namespace ObsModel

variable {ι σ : Type} {Act : ι → Type}

/-- Joint (possibly inactive) action profile. -/
abbrev JointAction (_ : ObsModel ι σ Act) := ∀ i, Option (Act i)

end ObsModel
end GameTheory
