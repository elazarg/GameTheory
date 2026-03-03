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

theorem theorem_transport
    {X Y : Type*}
    {P : X → Prop} {Q : Y → Prop}
    (φ : X → Y)
    (h : ∀ x, P x → Q (φ x)) :
    ∀ x, P x → Q (φ x) := h

theorem transport_comp
    {X Y Z : Type*}
    {P : X → Prop} {Q : Y → Prop} {R : Z → Prop}
    (φ : X → Y) (ψ : Y → Z)
    (h₁ : ∀ x, P x → Q (φ x))
    (h₂ : ∀ y, Q y → R (ψ y)) :
    ∀ x, P x → R ((ψ ∘ φ) x) := by
  intro x hx
  exact h₂ (φ x) (h₁ x hx)

theorem transport_iff_of_leftRight
    {X Y : Type*}
    {P : X → Prop} {Q : Y → Prop}
    (φ : X → Y) (ψ : Y → X)
    (hL : ∀ x, P x → Q (φ x))
    (hR : ∀ y, Q y → P (ψ y))
    (hφψ : ∀ x, ψ (φ x) = x)
    (hP_respect : ∀ x x', x = x' → (P x ↔ P x')) :
    ∀ x, P x ↔ Q (φ x) := by
  intro x
  constructor
  · exact hL x
  · intro hq
    have hpψ : P (ψ (φ x)) := hR (φ x) hq
    exact (hP_respect (ψ (φ x)) x (hφψ x)).1 hpψ

theorem objective_transport_eq
    {X Y : Type*} {β : Type*}
    (objX : X → β) (objY : Y → β) (φ : X → Y)
    (hobj : ∀ x, objY (φ x) = objX x) :
    ∀ x, objY (φ x) = objX x := hobj

theorem objective_transport_le
    {X Y : Type*} {β : Type*} [Preorder β]
    (objX : X → β) (objY : Y → β) (φ : X → Y)
    (hobj : ∀ x, objY (φ x) = objX x) :
    (∀ x x', objX x' ≤ objX x) →
    (∀ x x', objY (φ x') ≤ objY (φ x)) := by
  intro hmono x x'
  simpa [hobj x, hobj x'] using hmono x x'

end Transfer
end Order
end Math
