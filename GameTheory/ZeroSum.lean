import GameTheory.GameProperties
import Mathlib.Algebra.BigOperators.Fin

/-!
# GameTheory.ZeroSum

Theorems about zero-sum games.

Provides:
- `IsZeroSum.socialWelfare_eq_zero` — total expected utility is zero in a zero-sum game
- `IsZeroSum.eu_neg` — in a 2-player zero-sum game, one player's EU is the negation of the other's
-/

open scoped BigOperators

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

set_option linter.unusedFintypeInType false in
/-- In a zero-sum game with finite outcomes and finite players,
    the social welfare (sum of all players' expected utilities) is always zero. -/
theorem IsZeroSum.socialWelfare_eq_zero [Fintype ι] {G : KernelGame ι} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) : G.socialWelfare σ = 0 := by
  simp only [socialWelfare, eu, expect_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have : ∀ ω : G.Outcome, ∑ i : ι, G.utility ω i = 0 := fun ω => hzs ω
  simp [this]

set_option linter.unusedFintypeInType false in
/-- In a 2-player zero-sum game with finite outcomes,
    one player's expected utility is the negation of the other's. -/
theorem IsZeroSum.eu_neg {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) :
    G.eu σ 0 = - G.eu σ 1 := by
  have h := hzs.socialWelfare_eq_zero σ
  simp only [socialWelfare, Fin.sum_univ_two] at h
  linarith

end KernelGame
end GameTheory
