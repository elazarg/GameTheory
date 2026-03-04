import GameTheory.GameProperties
import GameTheory.SolutionConcepts
import Mathlib.Algebra.BigOperators.Fin
import Math.Probability

/-!
# GameTheory.ConstantSum

Theorems about constant-sum games.

Provides:
- `IsConstantSum.socialWelfare_eq` — social welfare equals `c`
- `IsConstantSum.eu_determined` — player 0's EU determined by 1's
- `IsZeroSum.isConstantSum_zero` — zero-sum is constant-sum 0
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

set_option linter.unusedFintypeInType false in
/-- In a constant-sum game with finite outcomes and finite players,
    social welfare always equals `c`. -/
theorem IsConstantSum.socialWelfare_eq [Fintype ι]
    {G : KernelGame ι} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G) :
    G.socialWelfare σ = c := by
  simp only [socialWelfare, eu, expect_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hc : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = c :=
    fun ω => hcs ω
  simp_rw [hc, ← Finset.sum_mul, pmf_toReal_sum_one, one_mul]

set_option linter.unusedFintypeInType false in
/-- In a 2-player constant-sum game with finite outcomes,
    player 0's EU is `c - eu σ 1`. -/
theorem IsConstantSum.eu_determined
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
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

set_option linter.unusedFintypeInType false in
/-- In a 2-player constant-sum game, all Nash equilibria yield the same EU.
    This extends the zero-sum value uniqueness result. -/
theorem IsConstantSum.nash_eu_eq
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.eu σ 0 = G.eu τ 0 := by
  -- Both are constant-sum, so eu σ 0 = c - eu σ 1 and eu τ 0 = c - eu τ 1
  -- Also eu σ 1 = c - eu σ 0 and eu τ 1 = c - eu τ 0
  have h1σ := hcs.eu_determined σ
  have h1τ := hcs.eu_determined τ
  -- Nash gives: eu σ 0 ≥ eu(update σ 0 s₀) 0 and eu τ 1 ≥ eu(update τ 1 s₁) 1
  -- Player 0 in σ is best-responding, player 1 in τ is best-responding
  -- Combining with constant-sum...
  apply le_antisymm
  · -- eu σ 0 ≤ eu τ 0
    have hcap : G.eu τ 0 ≥ G.eu (Function.update τ 0 (σ 0)) 0 := by
      convert hNτ 0 (σ 0)
    have hopt : G.eu σ 1 ≥ G.eu (Function.update σ 1 (τ 1)) 1 := by
      convert hNσ 1 (τ 1)
    have heq : Function.update σ 1 (τ 1) = Function.update τ 0 (σ 0) := by
      funext i
      fin_cases i <;> simp [Function.update]
    have hcs_cross := hcs.eu_determined (Function.update σ 1 (τ 1))
    rw [heq] at hcs_cross
    -- hcap: eu τ 0 ≥ eu(cross) 0
    -- hcs_cross: eu(cross) 0 = c - eu(cross) 1
    -- heq applied to hopt: eu σ 1 ≥ eu(cross) 1
    rw [heq] at hopt
    linarith
  · -- eu τ 0 ≤ eu σ 0 (symmetric argument)
    have hcap : G.eu σ 0 ≥ G.eu (Function.update σ 0 (τ 0)) 0 := by
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
