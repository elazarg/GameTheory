import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Math
namespace Order
namespace Transfer

variable {X Y : Type*}
variable {P : X → Prop} {Q : Y → Prop}
variable {φ : X → Y}
variable {β : Type*} [Preorder β]

theorem predicate_transfer_of_pointwise
    (h : ∀ x, P x → Q (φ x)) :
    ∀ x, P x → Q (φ x) := h

theorem no_improvement_transfer
    {S T : Type*}
    (objS : S → β) (objT : T → β) (map : S → T)
    (hobj : ∀ s, objT (map s) = objS s) :
    (∀ s s', objS s' ≤ objS s) →
    (∀ s s', objT (map s') ≤ objT (map s)) := by
  intro hmono s s'
  simpa [hobj s, hobj s'] using hmono s s'

theorem predicate_transfer_compose
    {Z : Type*}
    {R : Z → Prop}
    {ψ : Z → X}
    (h : ∀ x, P x → Q (φ x)) :
    ∀ z, R z → P (ψ z) → Q (φ (ψ z)) := by
  intro z _ hz
  exact h (ψ z) hz

theorem fixed_point_transfer
    {X : Type*}
    (T : X → X) (P : X → Prop)
    (h : ∀ x, T x = x → P x) :
    ∀ x, T x = x → P x := h

end Transfer
end Order
end Math
