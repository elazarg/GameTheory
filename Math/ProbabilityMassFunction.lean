import Math.Probability

set_option autoImplicit false

namespace Math
namespace ProbabilityMassFunction

variable {α β γ : Type*}

noncomputable def pushforward (μ : PMF α) (f : α → β) : PMF β :=
  μ.bind (fun a => PMF.pure (f a))

theorem pushforward_comp
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) := by
  simp [pushforward, PMF.bind_bind, Function.comp]

theorem bind_congr_on_support
    (μ : PMF α) (f g : α → PMF β)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr (fun a => ?_)
  by_cases ha0 : μ a = 0
  · simp [ha0]
  · have haS : a ∈ μ.support := by
      simpa [PMF.mem_support_iff] using ha0
    rw [hfg a haS]

set_option linter.unusedFintypeInType false in
theorem expect_mono_of_pointwise
    {Ω : Type} [Fintype Ω]
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g := by
  simpa [Math.Probability.expect_eq_sum] using
    (Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) ENNReal.toReal_nonneg))

end ProbabilityMassFunction
end Math
