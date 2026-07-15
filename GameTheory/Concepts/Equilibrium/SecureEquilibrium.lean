/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.PrefPreorderProperties

/-!
# Secure Equilibrium

A secure equilibrium refines Nash equilibrium by giving every player a hostile
tie-break: primarily maximize their own expected utility; among deviations that
leave it unchanged, prefer to weakly lower every opponent's utility and
strictly lower at least one.

The definition is phrased on outcome laws, so it applies directly to stochastic
`KernelGame`s and delegates equilibrium bookkeeping to `IsNashFor`.

## Main definitions

* `KernelGame.SecurelyProfitableLawDeviation`
* `KernelGame.securePref`
* `KernelGame.IsSecureEq`

## Main results

* `KernelGame.isSecureEq_iff_no_securelyProfitableDeviation`
* `KernelGame.IsSecureEq.isNash`
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Expected utility of `who` under an outcome law. -/
noncomputable def lawEU (G : KernelGame ι) (μ : PMF G.Outcome) (who : ι) : ℝ :=
  expect μ (fun ω => G.utility ω who)

/-- Moving from outcome law `old` to `new` is securely profitable for `who` if
it either strictly improves `who`'s expected utility, or preserves it while
weakly lowering every opponent's utility and strictly lowering at least one.

For two players this is the usual lexicographic objective: maximize one's own
payoff, then minimize the opponent's payoff. -/
noncomputable def SecurelyProfitableLawDeviation (G : KernelGame ι) (who : ι)
    (old new : PMF G.Outcome) : Prop :=
  G.lawEU new who > G.lawEU old who ∨
    (G.lawEU new who = G.lawEU old who ∧
      (∀ other, other ≠ who → G.lawEU new other ≤ G.lawEU old other) ∧
      ∃ other, other ≠ who ∧ G.lawEU new other < G.lawEU old other)

/-- The weak secure preference used by `IsNashFor`: the status-quo law is
acceptable relative to a deviation exactly when that deviation is not securely
profitable. -/
noncomputable def securePref (G : KernelGame ι) :
    ι → PMF G.Outcome → PMF G.Outcome → Prop :=
  fun who old new => ¬ G.SecurelyProfitableLawDeviation who old new

/-- A secure equilibrium is Nash equilibrium under the hostile-tie-break
preference `securePref`. -/
def IsSecureEq [DecidableEq ι] (G : KernelGame ι) (σ : Profile G) : Prop :=
  G.IsNashFor G.securePref σ

/-- Unfolded secure-equilibrium characterization by unilateral deviations. -/
theorem isSecureEq_iff_no_securelyProfitableDeviation [DecidableEq ι]
    (G : KernelGame ι)
    (σ : Profile G) :
    G.IsSecureEq σ ↔
      ∀ who (s' : G.Strategy who),
        ¬ G.SecurelyProfitableLawDeviation who
          (G.outcomeKernel σ)
          (G.outcomeKernel (Function.update σ who s')) := by
  change G.toGameForm.IsNashFor G.securePref σ ↔ _
  rw [G.toGameForm.isNashFor_iff]
  rfl

/-- Every secure equilibrium is a Nash equilibrium. -/
theorem IsSecureEq.isNash [DecidableEq ι] {G : KernelGame ι} {σ : Profile G}
    (h : G.IsSecureEq σ) : G.IsNash σ := by
  rw [G.IsNash_iff_IsNashFor_eu]
  refine KernelGame.IsNashFor.mono (G := G) (pref₁ := G.euPref)
    (pref₂ := G.securePref) ?_ (show G.IsNashFor G.securePref σ from h)
  intro who old new hsecure
  simp only [securePref, SecurelyProfitableLawDeviation] at hsecure
  simp only [euPref]
  by_contra hle
  exact hsecure (Or.inl (lt_of_not_ge hle))

end KernelGame

end GameTheory
