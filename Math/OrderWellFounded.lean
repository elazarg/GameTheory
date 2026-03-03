import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Basic

set_option autoImplicit false

namespace Math
namespace Order
namespace WellFounded

variable {α : Type*} {r : α → α → Prop}

theorem induction_schema
    (wf : _root_.WellFounded r)
    {P : α → Prop}
    (step : ∀ a, (∀ b, r b a → P b) → P a) :
    ∀ a, P a := by
  intro a
  exact wf.induction a step

theorem exists_min_of_nonempty
    (wf : _root_.WellFounded r)
    (s : Set α) (hs : s.Nonempty) :
    ∃ m, m ∈ s ∧ ∀ a, a ∈ s → ¬ r a m := by
  refine ⟨wf.min s hs, wf.min_mem s hs, ?_⟩
  intro a ha
  exact wf.not_lt_min s hs ha

theorem fixedPoint_transfer
    {T : α → α} {Q : α → Prop} {x : α}
    (hfix : T x = x)
    (hQ : ∀ y, T y = y → Q y) :
    Q x :=
  hQ x hfix

end WellFounded
end Order
end Math
