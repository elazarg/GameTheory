import Mathlib.Data.Set.Basic

set_option autoImplicit false

/-!
# Projection and FactorsThrough

`FactorsThrough`: predicate asserting a function factors through an observation map.
-/

namespace Math
namespace Projection

/-- A projection/readout map from rich objects `X` to observables `Ω`. -/
abbrev Map (X Ω : Type*) := X → Ω

/-- A function `f` factors through a projection `obs` if it can be written as
`g ∘ obs` for some `g`. -/
def FactorsThrough {X Ω β : Type*} (obs : Map X Ω) (f : X → β) : Prop :=
  ∃ g : Ω → β, f = g ∘ obs

theorem eq_of_factorsThrough {X Ω β : Type*}
    {obs : Map X Ω} {f : X → β}
    (hf : FactorsThrough obs f) {x y : X} (hxy : obs x = obs y) :
    f x = f y := by
  rcases hf with ⟨g, rfl⟩
  simp [hxy]

end Projection
end Math
