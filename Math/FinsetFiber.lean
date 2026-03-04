import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Math
namespace Finset
namespace Fiber

variable {α β : Type*} [DecidableEq β]

/-- If `|f '' s| < |s|`, then there are two distinct points in `s`
with the same image under `f`. -/
theorem exists_collision_of_card_image_lt
    (s : Finset α) (f : α → β)
    (h : (Finset.image f s).card < s.card) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ f a = f b := by
  by_contra hno
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    by_contra hne
    exact hno ⟨a, b, ha, hb, hne, hab⟩
  have hcard := Finset.card_image_of_injOn (s := s) (f := f) hinj
  linarith

/-- Specialization of `exists_collision_of_card_image_lt` to the case
`|s| = |f '' s| + 1`. -/
theorem exists_collision_of_card_eq_card_image_add_one
    (s : Finset α) (f : α → β)
    (h : s.card = (Finset.image f s).card + 1) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ f a = f b := by
  apply exists_collision_of_card_image_lt s f
  linarith

end Fiber
end Finset
end Math
