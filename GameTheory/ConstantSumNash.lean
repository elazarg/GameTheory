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

variable {ι : Type}

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a 2-player constant-sum Nash equilibrium, when player 1 deviates,
    player 0's expected utility can only increase (or stay the same).
    This follows because player 1 cannot improve by deviating (Nash),
    and the total is constant, so any loss for player 1 is a gain for player 0. -/
theorem IsConstantSum.nash_opponent_deviation_helps
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 1) :
    G.eu (Function.update σ 1 s') 0 ≥ G.eu σ 0 := by
  have h_nash : G.eu σ 1 ≥ G.eu (Function.update σ 1 s') 1 := by convert hN 1 s'
  have h1 := hcs.eu_determined σ
  have h2 := hcs.eu_determined (Function.update σ 1 s')
  linarith

set_option linter.unusedFintypeInType false in
open Classical in
/-- Symmetric version: in a 2-player constant-sum Nash equilibrium, when player 0
    deviates, player 1's expected utility can only increase (or stay the same). -/
theorem IsConstantSum.nash_opponent_deviation_helps'
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 0) :
    G.eu (Function.update σ 0 s') 1 ≥ G.eu σ 1 := by
  have h_nash : G.eu σ 0 ≥ G.eu (Function.update σ 0 s') 0 := by convert hN 0 s'
  have h1 := hcs.eu_determined σ
  have h2 := hcs.eu_determined (Function.update σ 0 s')
  linarith

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
  convert hcs.nash_opponent_deviation_helps hN (τ 1) using 2
  convert fin2_update_comm σ τ

set_option linter.unusedFintypeInType false in
/-- At a Nash equilibrium of a 2-player constant-sum game, player 1's Nash strategy
    guarantees the Nash payoff against any opponent strategy. -/
theorem IsConstantSum.nash_guarantees_1
    {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.Guarantees 1 (σ 1) (G.eu σ 1) := by
  intro τ
  convert hcs.nash_opponent_deviation_helps' hN (τ 0) using 2
  funext i; fin_cases i <;> simp [Function.update]

end KernelGame
end GameTheory
