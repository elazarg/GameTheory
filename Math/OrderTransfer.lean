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

end Transfer
end Order
end Math
