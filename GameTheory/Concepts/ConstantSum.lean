import GameTheory.Core.GameProperties
import GameTheory.Concepts.SolutionConcepts
import Mathlib.Algebra.BigOperators.Fin
import Math.Probability

/-!
# Constant-Sum Games

Theorems about constant-sum kernel games.

- `IsConstantSum.socialWelfare_eq` — social welfare equals `c`
- `IsConstantSum.eu_determined` — player 0's EU determined by 1's
- `IsZeroSum.isConstantSum_zero` — zero-sum is constant-sum 0
- `IsConstantSum.nash_eu_eq` — all Nash equilibria yield the same EU
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

/-- In a constant-sum game with finite outcomes and finite players,
    social welfare always equals `c`. -/
theorem IsConstantSum.socialWelfare_eq [Fintype ι]
    {G : KernelGame ι} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G) :
    G.socialWelfare σ = c := by
  letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
  simp only [socialWelfare, eu, expect_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hc : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = c :=
    fun ω => hcs ω
  simp_rw [hc, ← Finset.sum_mul, pmf_toReal_sum_one, one_mul]

/-- Bounded-utility version of `socialWelfare_eq`: drops `[Finite G.Outcome]`
    in favor of per-player utility bounds that ensure summability. -/
theorem IsConstantSum.socialWelfare_eq_of_bounded [Fintype ι]
    {G : KernelGame ι}
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.socialWelfare σ = c := by
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
  have hc : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = c :=
    fun ω => hcs ω
  simp_rw [hc]
  rw [tsum_mul_right, Math.Probability.pmf_toReal_tsum_one, one_mul]

/-- In a 2-player constant-sum game with finite outcomes,
    player 0's EU is `c - eu σ 1`. -/
theorem IsConstantSum.eu_determined
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G) :
    G.eu σ 0 = c - G.eu σ 1 := by
  have h := hcs.socialWelfare_eq σ
  simp only [socialWelfare, Fin.sum_univ_two] at h
  linarith

/-- A zero-sum game is a constant-sum game with constant 0. -/
theorem IsZeroSum.isConstantSum_zero [Fintype ι]
    {G : KernelGame ι}
    (hzs : G.IsZeroSum) : G.IsConstantSum 0 :=
  hzs

/-- In a 2-player constant-sum game, all Nash equilibria yield the same EU.
    This extends the zero-sum value uniqueness result. -/
theorem IsConstantSum.nash_eu_eq
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.eu σ 0 = G.eu τ 0 := by
  have h1σ := hcs.eu_determined σ
  have h1τ := hcs.eu_determined τ
  apply le_antisymm
  · have hcap : G.eu τ 0 ≥ G.eu (Function.update τ 0 (σ 0)) 0 := by
      convert hNτ 0 (σ 0)
    have hopt : G.eu σ 1 ≥ G.eu (Function.update σ 1 (τ 1)) 1 := by
      convert hNσ 1 (τ 1)
    have heq : Function.update σ 1 (τ 1) = Function.update τ 0 (σ 0) := by
      funext i
      fin_cases i <;> simp [Function.update]
    have hcs_cross := hcs.eu_determined (Function.update σ 1 (τ 1))
    rw [heq] at hcs_cross
    rw [heq] at hopt
    linarith
  · have hcap : G.eu σ 0 ≥ G.eu (Function.update σ 0 (τ 0)) 0 := by
      convert hNσ 0 (τ 0)
    have hopt : G.eu τ 1 ≥ G.eu (Function.update τ 1 (σ 1)) 1 := by
      convert hNτ 1 (σ 1)
    have heq : Function.update τ 1 (σ 1) = Function.update σ 0 (τ 0) := by
      funext i
      fin_cases i <;> simp [Function.update]
    have hcs_cross := hcs.eu_determined (Function.update τ 1 (σ 1))
    rw [heq] at hcs_cross hopt
    linarith

end KernelGame
end GameTheory
