import Mathlib.Data.Set.Function
import Math.ProbabilityMassFunction

set_option autoImplicit false

/-!
# Set.EqOn Congruence for PMF Operations

`Set.EqOn`-based congruence lemmas for `PMF.bind` and `expect`: functions
agreeing on support/reachable sets produce equal results.
-/

namespace Math
namespace Set
namespace Reachability

variable {α β γ : Type*}

theorem bind_eq_of_eqOn_support
    (μ : PMF α) (f g : α → PMF β)
    (hfg : Set.EqOn f g μ.support) :
    μ.bind f = μ.bind g := by
  exact Math.ProbabilityMassFunction.bind_congr_on_support μ f g (fun a ha => hfg ha)

theorem bind_eq_of_eqOn_reachable
    (μ : PMF α) (R : Set α) (f g : α → PMF β)
    (hsupp : μ.support ⊆ R)
    (hfg : Set.EqOn f g R) :
    μ.bind f = μ.bind g := by
  exact bind_eq_of_eqOn_support μ f g (Set.EqOn.mono hsupp hfg)

theorem expect_eq_of_eqOn_support
    (μ : PMF α) (f g : α → ℝ)
    (hfg : Set.EqOn f g μ.support) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  exact Math.ProbabilityMassFunction.expect_congr_on_support μ f g (fun a ha => hfg ha)

theorem expect_eq_of_eqOn_reachable
    (μ : PMF α) (R : Set α) (f g : α → ℝ)
    (hsupp : μ.support ⊆ R)
    (hfg : Set.EqOn f g R) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  exact expect_eq_of_eqOn_support μ f g (Set.EqOn.mono hsupp hfg)

end Reachability
end Set
end Math
