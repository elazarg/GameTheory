import GameTheory.GameProperties
import Mathlib.Algebra.BigOperators.Fin

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

end KernelGame
end GameTheory
