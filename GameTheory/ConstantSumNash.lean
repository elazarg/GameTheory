import GameTheory.ConstantSum
import GameTheory.ZeroSum
import GameTheory.SolutionConcepts
import GameTheory.Minimax

/-!
# GameTheory.ConstantSumNash

Nash equilibrium properties specific to 2-player constant-sum kernel games.

Provides:
- `IsConstantSum.nash_opponent_deviation_helps` — in a constant-sum Nash equilibrium,
  player 1's deviation can only increase player 0's expected utility
- `IsConstantSum.nash_opponent_deviation_helps'` — symmetric: player 0's deviation
  can only increase player 1's expected utility
- `IsConstantSum.nash_guarantees_0` — at a Nash equilibrium, player 0's strategy
  guarantees the Nash payoff against any opponent
- `IsConstantSum.nash_guarantees_1` — at a Nash equilibrium, player 1's strategy
  guarantees the Nash payoff against any opponent
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

set_option linter.unusedFintypeInType false in
/-- In a 2-player constant-sum Nash equilibrium, when player 1 deviates,
    player 0's expected utility can only increase (or stay the same).
    This follows because player 1 cannot improve by deviating (Nash),
    and the total is constant, so any loss for player 1 is a gain for player 0. -/
theorem IsConstantSum.nash_opponent_deviation_helps
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 1) :
    G.eu (Function.update σ 1 s') 0 ≥ G.eu σ 0 := by
  have h_nash := hN 1 s'
  have h1 := hcs.eu_determined σ
  have h2 := hcs.eu_determined (Function.update σ 1 s')
  linarith

set_option linter.unusedFintypeInType false in
/-- Symmetric version: in a 2-player constant-sum Nash equilibrium, when player 0
    deviates, player 1's expected utility can only increase (or stay the same). -/
theorem IsConstantSum.nash_opponent_deviation_helps'
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 0) :
    G.eu (Function.update σ 0 s') 1 ≥ G.eu σ 1 := by
  have h_nash := hN 0 s'
  have h1 := hcs.eu_determined σ
  have h2 := hcs.eu_determined (Function.update σ 0 s')
  linarith

/-- Auxiliary: for `Fin 2`, updating player 0's strategy in `τ` to `σ 0` gives the
    same profile as updating player 1's strategy in `σ` to `τ 1`. Both yield the
    profile where player 0 plays `σ 0` and player 1 plays `τ 1`. -/
private theorem fin2_update_comm {α : Fin 2 → Type} (σ τ : ∀ i, α i) :
    Function.update τ 0 (σ 0) = Function.update σ 1 (τ 1) := by
  funext i; fin_cases i <;> simp [Function.update]

set_option linter.unusedFintypeInType false in
/-- At a Nash equilibrium of a 2-player constant-sum game, player 0's Nash strategy
    guarantees the Nash payoff against any opponent strategy. This combines the
    constant-sum structure (opponent's loss is your gain) with Nash stability. -/
theorem IsConstantSum.nash_guarantees_0
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.Guarantees 0 (σ 0) (G.eu σ 0) := by
  intro τ
  have key : Function.update τ 0 (σ 0) = Function.update σ 1 (τ 1) :=
    fin2_update_comm σ τ
  rw [key]
  exact hcs.nash_opponent_deviation_helps hN (τ 1)

set_option linter.unusedFintypeInType false in
/-- At a Nash equilibrium of a 2-player constant-sum game, player 1's Nash strategy
    guarantees the Nash payoff against any opponent strategy. -/
theorem IsConstantSum.nash_guarantees_1
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.Guarantees 1 (σ 1) (G.eu σ 1) := by
  intro τ
  have key : Function.update τ 1 (σ 1) = Function.update σ 0 (τ 0) := by
    funext i; fin_cases i <;> simp [Function.update]
  rw [key]
  exact hcs.nash_opponent_deviation_helps' hN (τ 0)

end KernelGame
end GameTheory
