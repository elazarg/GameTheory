import GameTheory.ZeroSum
import GameTheory.ConstantSum
import GameTheory.SolutionConcepts

/-!
# GameTheory.ZeroSumNash

Interactions between zero-sum / constant-sum structure and Nash equilibria
in 2-player kernel games.

Provides:
- `IsZeroSum.nash_eu_sum_zero` — at any Nash equilibrium of a 2-player zero-sum game,
  the sum of expected utilities is zero
- `IsConstantSum.nash_eu_sum` — at any profile of a 2-player constant-sum game,
  the sum of expected utilities equals the constant
- `IsZeroSum.eu_nonneg_iff_nonpos` — in a 2-player zero-sum game, player 0 has
  non-negative EU iff player 1 has non-positive EU
- `IsZeroSum.deviation_eu_neg` — in a 2-player zero-sum game, a unilateral
  deviation's gain for player 0 is exactly the loss for player 1
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

set_option linter.unusedFintypeInType false in
/-- In a 2-player zero-sum game, at any Nash equilibrium the sum of expected
    utilities is zero. -/
theorem IsZeroSum.nash_eu_sum_zero {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G} (_hN : G.IsNash σ) :
    G.eu σ 0 + G.eu σ 1 = 0 := by
  have h := hzs.eu_neg σ
  linarith

set_option linter.unusedFintypeInType false in
/-- In a 2-player constant-sum game, at any profile the sum of expected
    utilities equals the constant `c`. -/
theorem IsConstantSum.nash_eu_sum {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (σ : Profile G) :
    G.eu σ 0 + G.eu σ 1 = c := by
  have h := hcs.eu_determined σ
  linarith

set_option linter.unusedFintypeInType false in
/-- In a 2-player zero-sum game, player 0 has non-negative expected utility
    if and only if player 1 has non-positive expected utility. -/
theorem IsZeroSum.eu_nonneg_iff_nonpos {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) :
    G.eu σ 0 ≥ 0 ↔ G.eu σ 1 ≤ 0 := by
  have h := hzs.eu_neg σ
  constructor
  · intro h0; linarith
  · intro h1; linarith

set_option linter.unusedFintypeInType false in
/-- In a 2-player zero-sum game, the change in player 0's expected utility from
    a unilateral deviation is exactly the negation of the change in player 1's
    expected utility. That is, any gain for one player is an equal loss for the other. -/
theorem IsZeroSum.deviation_eu_neg {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) (s' : G.Strategy 0) :
    G.eu (Function.update σ 0 s') 0 - G.eu σ 0 =
    -(G.eu (Function.update σ 0 s') 1 - G.eu σ 1) := by
  have h1 := hzs.eu_neg σ
  have h2 := hzs.eu_neg (Function.update σ 0 s')
  linarith

end KernelGame
end GameTheory
