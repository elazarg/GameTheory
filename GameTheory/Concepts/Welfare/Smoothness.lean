/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.ZeroSum.ConstantSumCorrelated

/-!
# Smoothness and the robust price of anarchy

Roughgarden's **smoothness** framework for bounding the price of anarchy of
welfare-maximization games. A game is `(λ, μ)`-smooth if for any two profiles the
total utility from each player unilaterally best-deviating toward the second is at
least `λ · W(s*) − μ · W(s)`. The consequence — the *robust* price of anarchy — is
the inequality `λ · W(t) ≤ (1 + μ) · W(s)` for any Nash equilibrium `s` and any
profile `t`, and the same bound for every **coarse correlated equilibrium**. When
`1 + μ > 0` this rearranges to the welfare ratio `λ / (1 + μ)`.

## Main definitions

* `KernelGame.IsSmooth` — `(λ, μ)`-smoothness for welfare maximization

## Main results

* `IsSmooth.nash_bound` — `λ · W(t) ≤ (1 + μ) · W(s)` for any Nash equilibrium `s` and profile `t`
* `IsSmooth.coarseCorrelated_bound` — the same bound holds for coarse correlated equilibria
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (G : KernelGame ι)

/-- A game is **(λ, μ)-smooth** (Roughgarden) for welfare maximization if, for any
two profiles `s` and `t`, the total utility obtained when each player unilaterally
switches to their `t`-action against `s` is at least `λ · W(t) − μ · W(s)`. -/
def IsSmooth (lam mu : ℝ) : Prop :=
  ∀ s t : Profile G,
    lam * G.socialWelfare t - mu * G.socialWelfare s ≤
      ∑ i, G.eu (Function.update s i (t i)) i

/-- **Smoothness bounds the price of anarchy at a Nash equilibrium.** If `G` is
`(λ, μ)`-smooth then the welfare of any Nash equilibrium `s` satisfies
`λ · W(t) ≤ (1 + μ) · W(s)` for every profile `t` (in particular the optimum). -/
theorem IsSmooth.nash_bound {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {s : Profile G} (hs : G.IsNash s) (t : Profile G) :
    lam * G.socialWelfare t ≤ (1 + mu) * G.socialWelfare s := by
  have hdev : (∑ i, G.eu (Function.update s i (t i)) i) ≤ G.socialWelfare s := by
    rw [socialWelfare]
    exact Finset.sum_le_sum fun i _ => hs i (t i)
  nlinarith [hsmooth s t, hdev]

/-! ### Robust price of anarchy: the bound extends to coarse correlated equilibria -/

variable [Fintype (Profile G)] [Finite G.Outcome]

set_option linter.unusedFintypeInType false in
/-- **Robust price of anarchy.** Smoothness bounds the welfare not only of Nash
equilibria but of every **coarse correlated equilibrium** `ν`: the expected welfare
`∑ᵢ correlatedEu ν i` satisfies `λ · W(t) ≤ (1 + μ) · E[W]` for every profile `t`.
This is Roughgarden's "the price of anarchy is robust" theorem. -/
theorem IsSmooth.coarseCorrelated_bound {lam mu : ℝ} (hsmooth : G.IsSmooth lam mu)
    {ν : PMF (Profile G)} (hν : G.IsCoarseCorrelatedEq ν) (t : Profile G) :
    lam * G.socialWelfare t ≤ (1 + mu) * (∑ i, G.correlatedEu ν i) := by
  set CW := ∑ i, G.correlatedEu ν i with hCW
  have hCW_eq : CW = expect ν (fun s => G.socialWelfare s) := by
    rw [hCW, show (∑ i, G.correlatedEu ν i) = ∑ i, expect ν (fun s => G.eu s i) from
      Finset.sum_congr rfl fun i _ => G.correlatedEu_eq_expect_eu ν i, expect_sum_comm]
    simp only [socialWelfare]
  have hdev_sum : ∑ i, expect ν (fun s => G.eu (Function.update s i (t i)) i) ≤ CW := by
    rw [hCW]
    refine Finset.sum_le_sum fun i _ => ?_
    have hcce := hν i (t i)
    rwa [G.correlatedEu_constantDeviationDistribution_eq_expect_update ν i (t i)] at hcce
  have hsmooth_exp :
      lam * G.socialWelfare t - mu * CW ≤
        ∑ i, expect ν (fun s => G.eu (Function.update s i (t i)) i) := by
    rw [hCW_eq, expect_sum_comm]
    have heq : expect ν (fun s => lam * G.socialWelfare t - mu * G.socialWelfare s)
        = lam * G.socialWelfare t - mu * expect ν (fun s => G.socialWelfare s) := by
      rw [expect_sub, expect_const ν (lam * G.socialWelfare t),
        expect_const_mul ν mu (fun s => G.socialWelfare s)]
    rw [← heq]
    exact expect_mono ν _ _ fun s => hsmooth s t
  nlinarith [hdev_sum, hsmooth_exp]

end KernelGame

end GameTheory
