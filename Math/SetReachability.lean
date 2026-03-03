import Mathlib.Data.Set.Basic
import Math.ProbabilityMassFunction

set_option autoImplicit false

namespace Math
namespace Set
namespace Reachability

variable {α β γ : Type*}

theorem eq_of_eqOn_mem
    {R : Set α} {f g : α → β}
    (hfg : Set.EqOn f g R) {x : α} (hx : x ∈ R) :
    f x = g x :=
  hfg hx

theorem eqOn_mono
    {R S : Set α} {f g : α → β}
    (hRS : S ⊆ R) (hfg : Set.EqOn f g R) :
    Set.EqOn f g S := by
  intro x hx
  exact hfg (hRS hx)

theorem eqOn_comp_right
    {R : Set α} {f g : α → β} {h : β → γ}
    (hfg : Set.EqOn f g R) :
    Set.EqOn (fun x => h (f x)) (fun x => h (g x)) R := by
  intro x hx
  simpa using congrArg h (hfg hx)

theorem bind_eq_of_eqOn_support
    (μ : PMF α) (f g : α → PMF β)
    (hfg : Set.EqOn f g μ.support) :
    μ.bind f = μ.bind g := by
  exact Math.ProbabilityMassFunction.bind_congr_on_support μ f g (fun a ha => hfg ha)

theorem expect_eq_of_eqOn_support
    (μ : PMF α) (f g : α → ℝ)
    (hfg : Set.EqOn f g μ.support) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  exact Math.ProbabilityMassFunction.expect_congr_on_support μ f g (fun a ha => hfg ha)

end Reachability
end Set
end Math
