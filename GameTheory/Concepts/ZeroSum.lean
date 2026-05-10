import GameTheory.Core.GameProperties
import Mathlib.Algebra.BigOperators.Fin
import Math.Probability

/-!
# Zero-Sum Games

Theorems about zero-sum kernel games.

- `IsZeroSum.socialWelfare_eq_zero` — total expected utility is zero
- `IsZeroSum.eu_neg` — in a 2-player zero-sum game, one player's EU is the negation of the other's
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

/-- In a zero-sum game with finite players and per-player bounded utility, the
    social welfare is zero. -/
theorem IsZeroSum.socialWelfare_eq_zero_of_bounded [Fintype ι] {G : KernelGame ι}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) : G.socialWelfare σ = 0 := by
  simp only [socialWelfare, eu, expect]
  rw [show (∑ i : ι, ∑' ω, (G.outcomeKernel σ ω).toReal * G.utility ω i) =
      ∑' ω, ∑ i : ι, (G.outcomeKernel σ ω).toReal * G.utility ω i from by
    have hi : ∀ i ∈ (Finset.univ : Finset ι),
        Summable (fun ω => (G.outcomeKernel σ ω).toReal * G.utility ω i) := by
      intro i _
      exact Math.Probability.expect_summable_of_bounded
        (G.outcomeKernel σ) (fun ω => G.utility ω i) (hbd i)
    rw [Summable.tsum_finsetSum hi]]
  simp_rw [← Finset.mul_sum]
  have : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = 0 := fun ω => hzs ω
  simp [this]

/-- In a zero-sum game with finite outcomes and finite players,
    the social welfare (sum of all players' expected utilities) is always zero. -/
theorem IsZeroSum.socialWelfare_eq_zero [Fintype ι] {G : KernelGame ι} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) : G.socialWelfare σ = 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.socialWelfare_eq_zero_of_bounded σ hbd

/-- In a 2-player zero-sum game with bounded utility, one player's EU is the
    negation of the other's. -/
theorem IsZeroSum.eu_neg_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 = - G.eu σ 1 := by
  have h := hzs.socialWelfare_eq_zero_of_bounded σ hbd
  simp only [socialWelfare, Fin.sum_univ_two] at h
  linarith

/-- Bounded-utility variant: social welfare is zero in a zero-sum game with
finite players and per-player bounded utility, no `[Finite G.Outcome]`. -/
theorem IsZeroSum.socialWelfare_eq_zero_of_bounded [Fintype ι] {G : KernelGame ι}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) : G.socialWelfare σ = 0 := by
  simp only [socialWelfare, eu, expect]
  rw [show (∑ i : ι, ∑' ω, (G.outcomeKernel σ ω).toReal * G.utility ω i) =
      ∑' ω, ∑ i : ι, (G.outcomeKernel σ ω).toReal * G.utility ω i from by
    have hi : ∀ i ∈ (Finset.univ : Finset ι),
        Summable (fun ω => (G.outcomeKernel σ ω).toReal * G.utility ω i) := by
      intro i _
      exact Math.Probability.expect_summable_of_bounded
        (G.outcomeKernel σ) (fun ω => G.utility ω i) (hbd i)
    rw [Summable.tsum_finsetSum hi]]
  simp_rw [← Finset.mul_sum]
  have : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = 0 := fun ω => hzs ω
  simp [this]

/-- In a 2-player zero-sum game with finite outcomes,
    one player's expected utility is the negation of the other's. -/
theorem IsZeroSum.eu_neg {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) :
    G.eu σ 0 = - G.eu σ 1 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.eu_neg_of_bounded σ hbd

/-- Bounded-utility variant of `eu_neg`. -/
theorem IsZeroSum.eu_neg_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 = - G.eu σ 1 := by
  have h := hzs.socialWelfare_eq_zero_of_bounded σ hbd
  simp only [socialWelfare, Fin.sum_univ_two] at h
  linarith

end KernelGame
end GameTheory
