/-
# Secure implementations proved by uniform hybrids

Polynomially many replacements preserve utility indistinguishability when one
negligible bound controls every adjacent replacement. The bound is uniform in
the replacement index; separate negligible bounds for each fixed index do not
suffice when the number of replacements grows with the security parameter.
-/
import GameTheory.Core.PseudoNash
import GameTheory.Math.Probability.HybridIndistinguishability

noncomputable section

namespace GameTheory

open GameTheory.Math GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

/-- Construct the canonical simulation certificate from uniform utility hybrids.
Each witness supplies its complete chain, endpoints, and polynomial length. -/
def SecureImplementation.ofUniformHybrids [DecidableEq ι]
    {tests : Set (SampleTest ℝ)} {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (compile : ∀ who, ideal.sig.Strategy who → real.sig.Strategy who)
    (honest : ∀ (profile : Profile ideal.sig) who,
      ∃ (H : ℕ → ℕ → PMF ℝ) (steps : ℕ → ℕ),
        (∃ d : ℕ, ∀ᶠ κ in Filter.atTop, steps κ ≤ κ ^ d) ∧
        UniformHybridBound tests H steps ∧
        (fun κ => H κ 0) = real.utilityLaw who (Profile.map compile profile) ∧
        (fun κ => H κ (steps κ)) = ideal.utilityLaw who profile)
    (simulate : ∀ (profile : Profile ideal.sig) who (deviation : real.sig.Strategy who),
      ∃ (simulated : ideal.sig.Strategy who) (H : ℕ → ℕ → PMF ℝ) (steps : ℕ → ℕ),
        (∃ d : ℕ, ∀ᶠ κ in Filter.atTop, steps κ ≤ κ ^ d) ∧
        UniformHybridBound tests H steps ∧
        (fun κ => H κ 0) =
          real.utilityLaw who (Profile.update (Profile.map compile profile) who deviation) ∧
        (fun κ => H κ (steps κ)) =
          ideal.utilityLaw who (Profile.update profile who simulated)) :
    SecureImplementation tests ideal real where
  compile := compile
  honest profile who := by
    obtain ⟨H, steps, hsteps, hbound, hstart, hend⟩ := honest profile who
    rw [← hstart, ← hend]
    exact indistinguishableBy_of_uniform_hybrid hsteps hbound
  simulate profile who deviation := by
    obtain ⟨simulated, H, steps, hsteps, hbound, hstart, hend⟩ :=
      simulate profile who deviation
    refine ⟨simulated, ?_⟩
    rw [← hstart, ← hend]
    exact indistinguishableBy_of_uniform_hybrid hsteps hbound

end GameTheory
