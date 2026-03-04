import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Math
namespace Order
namespace Extremal

variable {α β : Type*} [Preorder β]

theorem dual_bound_witness_packaging
    (f g : α → β) (x : α) (v : β)
    (hEq : f x = v)
    (hLower : ∀ y, v ≤ f y)
    (hUpper : ∀ y, g y ≤ v) :
    (∃ x, f x = v) ∧ (∀ y, v ≤ f y) ∧ (∀ y, g y ≤ v) :=
  ⟨⟨x, hEq⟩, hLower, hUpper⟩

-- Existing in core as `le_antisymm`.

theorem argopt_transfer_of_affine
    (X : Type*) (f g : X → ℝ) (a b : ℝ)
    (hb : 0 < b)
    (hfg : ∀ x, g x = a + b * f x) :
    (∀ x y, f y ≤ f x) → (∀ x y, g y ≤ g x) := by
  intro hf x y
  rw [hfg x, hfg y]
  have hmul : b * f y ≤ b * f x := mul_le_mul_of_nonneg_left (hf x y) (le_of_lt hb)
  simpa using add_le_add_left hmul a

end Extremal
end Order
end Math
