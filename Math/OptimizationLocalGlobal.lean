import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Math
namespace Optimization
namespace LocalGlobal

variable {α ι β : Type*}
variable [Preorder β]

def IsFixedPoint (step : α → α) (x : α) : Prop :=
  step x = x

def NoImprovement (obj : α → β) (step : α → α) : Prop :=
  ∀ x, obj (step x) ≤ obj x

def LocallyOptimal (nbr : α → α → Prop) (obj : α → β) (x : α) : Prop :=
  ∀ y, nbr x y → obj y ≤ obj x

def ReachableBy (move : ι → α → α) (x y : α) : Prop :=
  ∃ i, y = move i x

theorem isFixedPoint_of_eq
    (step : α → α) {x : α} (hx : step x = x) :
    IsFixedPoint step x := hx

theorem noImprovement_at_of_fixed
    (obj : α → β) (step : α → α) {x : α}
    (hx : IsFixedPoint step x) :
    obj (step x) ≤ obj x := by
  have hEq : obj (step x) = obj x := by
    exact congrArg obj hx
  exact le_of_eq hEq

theorem locallyOptimal_of_move_family
    (move : ι → α → α) (obj : α → β) (x : α)
    (hmove : ∀ i, obj (move i x) ≤ obj x) :
    LocallyOptimal (ReachableBy move) obj x := by
  intro y hy
  rcases hy with ⟨i, rfl⟩
  exact hmove i

theorem locallyOptimal_of_global_on_set
    (S : Set α) (nbr : α → α → Prop) (obj : α → β) (x : α)
    (hglobal : ∀ y, y ∈ S → obj y ≤ obj x)
    (hnbr : ∀ y, nbr x y → y ∈ S) :
    LocallyOptimal nbr obj x := by
  intro y hyn
  exact hglobal y (hnbr y hyn)

theorem noImprovement_of_move_family
    (move : ι → α → α) (select : α → ι) (obj : α → β)
    (hmove : ∀ x i, obj (move i x) ≤ obj x) :
    NoImprovement obj (fun x => move (select x) x) := by
  intro x
  exact hmove x (select x)

section Additive

theorem noImprovement_add
    (obj₁ obj₂ : α → ℝ) (step : α → α)
    (h₁ : NoImprovement obj₁ step)
    (h₂ : NoImprovement obj₂ step) :
    NoImprovement (fun x => obj₁ x + obj₂ x) step := by
  intro x
  exact add_le_add (h₁ x) (h₂ x)

theorem locallyOptimal_add
    (nbr : α → α → Prop) (obj₁ obj₂ : α → ℝ) (x : α)
    (h₁ : LocallyOptimal nbr obj₁ x)
    (h₂ : LocallyOptimal nbr obj₂ x) :
    LocallyOptimal nbr (fun y => obj₁ y + obj₂ y) x := by
  intro y hy
  exact add_le_add (h₁ y hy) (h₂ y hy)

end Additive

section OrderedRing

theorem noImprovement_smul_nonneg
    (obj : α → ℝ) (step : α → α) {c : ℝ}
    (hc : 0 ≤ c) (h : NoImprovement obj step) :
    NoImprovement (fun x => c * obj x) step := by
  intro x
  exact mul_le_mul_of_nonneg_left (h x) hc

theorem locallyOptimal_smul_nonneg
    (nbr : α → α → Prop) (obj : α → ℝ) (x : α) {c : ℝ}
    (hc : 0 ≤ c) (h : LocallyOptimal nbr obj x) :
    LocallyOptimal nbr (fun y => c * obj y) x := by
  intro y hy
  exact mul_le_mul_of_nonneg_left (h y hy) hc

end OrderedRing

end LocalGlobal
end Optimization
end Math
