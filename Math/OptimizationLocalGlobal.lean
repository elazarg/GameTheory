import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Local Optimality and Fixed Points

Abstract fixed-point and local optimality theory: `IsFixedPoint`, `NoImprovement`,
`LocallyOptimal`. Transfer lemmas for objectives and neighborhoods.
-/

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

section PositivePart

theorem max_mul_self_eq_sq (x : ℝ) :
    x * max x 0 = (max x 0) ^ 2 := by
  by_cases hx : x ≤ 0
  · have hmax : max x 0 = 0 := max_eq_right hx
    simp [hmax]
  · have hx' : 0 < x := lt_of_not_ge hx
    have hmax : max x 0 = x := max_eq_left (le_of_lt hx')
    simp [hmax, sq]

theorem all_nonpos_of_weighted_pospart_fixedPoint
    {α : Type*} [Fintype α]
    (w g : α → ℝ)
    (hfp : ∀ a, w a * (1 + ∑ b : α, max (g b) 0) = w a + max (g a) 0)
    (hwg : ∑ a : α, w a * g a = 0) :
    ∀ a, g a ≤ 0 := by
  have hident : ∀ a, w a * (∑ b : α, max (g b) 0) = max (g a) 0 := by
    intro a
    have h := hfp a
    linarith
  have hsum_zero : ∑ a : α, max (g a) 0 * g a = 0 := by
    have :
        (∑ b : α, max (g b) 0) * (∑ a : α, w a * g a) =
          ∑ a : α, max (g a) 0 * g a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      have h := hident a
      calc
        (∑ b : α, max (g b) 0) * (w a * g a)
            = w a * (∑ b : α, max (g b) 0) * g a := by ring
        _ = max (g a) 0 * g a := by rw [h]
    rw [hwg, mul_zero] at this
    exact this.symm
  have hnonneg : ∀ a, 0 ≤ max (g a) 0 * g a := by
    intro a
    have hsq : max (g a) 0 * g a = (max (g a) 0) ^ 2 := by
      simpa [mul_comm] using (max_mul_self_eq_sq (g a))
    rw [hsq]
    exact sq_nonneg (max (g a) 0)
  have hall_zero : ∀ a, max (g a) 0 * g a = 0 := by
    intro a
    exact
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnonneg a)).1 hsum_zero
        a (Finset.mem_univ a)
  intro a
  by_contra hpos
  have hg : 0 < g a := lt_of_not_ge hpos
  have hmax : max (g a) 0 = g a := max_eq_left (le_of_lt hg)
  have hterm := hall_zero a
  rw [hmax] at hterm
  have : g a = 0 := by
    nlinarith [hterm]
  exact (ne_of_gt hg) this

end PositivePart

end LocalGlobal
end Optimization
end Math
