import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.Minimax
import Math.Probability

/-!
# Constant-Sum Nash Properties

Nash equilibrium properties specific to 2-player constant-sum kernel games.

Provides:
- `IsConstantSum.nash_opponent_deviation_helps` — in a constant-sum Nash equilibrium,
  player 1's deviation can only increase player 0's expected utility
- `IsConstantSum.nash_guarantees_0` — at a Nash equilibrium, player 0's strategy
  guarantees the Nash payoff against any opponent
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

open Classical in
/-- In a 2-player constant-sum Nash equilibrium with bounded utility, when player 1
    deviates, player 0's expected utility can only increase. -/
theorem IsConstantSum.nash_opponent_deviation_helps_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 1)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu (Function.update σ 1 s') 0 ≥ G.eu σ 0 := by
  have h_nash : G.eu σ 1 ≥ G.eu (Function.update σ 1 s') 1 := by convert hN 1 s'
  have h1 := hcs.eu_determined_of_bounded σ hbd
  have h2 := hcs.eu_determined_of_bounded (Function.update σ 1 s') hbd
  linarith

open Classical in
/-- Symmetric form: when player 0 deviates, player 1's expected utility can only
    increase. -/
theorem IsConstantSum.nash_opponent_deviation_helps'_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 0)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu (Function.update σ 0 s') 1 ≥ G.eu σ 1 := by
  have h_nash : G.eu σ 0 ≥ G.eu (Function.update σ 0 s') 0 := by convert hN 0 s'
  have h1 := hcs.eu_determined_of_bounded σ hbd
  have h2 := hcs.eu_determined_of_bounded (Function.update σ 0 s') hbd
  linarith

/-- Under bounded utility, player 0's Nash strategy guarantees the Nash payoff
    against any opponent. -/
theorem IsConstantSum.nash_guarantees_0_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.Guarantees 0 (σ 0) (G.eu σ 0) := by
  intro τ
  convert hcs.nash_opponent_deviation_helps_of_bounded hN (τ 1) hbd using 2
  funext i
  fin_cases i <;> simp [Function.update]

/-- Under bounded utility, player 1's Nash strategy guarantees the Nash payoff
    against any opponent. -/
theorem IsConstantSum.nash_guarantees_1_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.Guarantees 1 (σ 1) (G.eu σ 1) := by
  intro τ
  convert hcs.nash_opponent_deviation_helps'_of_bounded hN (τ 0) hbd using 2
  funext i; fin_cases i <;> simp [Function.update]

open Classical in
/-- In a 2-player constant-sum Nash equilibrium, when player 1 deviates,
    player 0's expected utility can only increase (or stay the same). -/
theorem IsConstantSum.nash_opponent_deviation_helps
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 1) :
    G.eu (Function.update σ 1 s') 0 ≥ G.eu σ 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.nash_opponent_deviation_helps_of_bounded hN s' hbd

open Classical in
/-- Symmetric version: when player 0 deviates, player 1's EU can only increase. -/
theorem IsConstantSum.nash_opponent_deviation_helps'
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) (s' : G.Strategy 0) :
    G.eu (Function.update σ 0 s') 1 ≥ G.eu σ 1 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.nash_opponent_deviation_helps'_of_bounded hN s' hbd

/-- Player 0's Nash strategy guarantees the Nash payoff against any opponent. -/
theorem IsConstantSum.nash_guarantees_0
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.Guarantees 0 (σ 0) (G.eu σ 0) := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.nash_guarantees_0_of_bounded hN hbd

/-- Player 1's Nash strategy guarantees the Nash payoff against any opponent. -/
theorem IsConstantSum.nash_guarantees_1
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.Guarantees 1 (σ 1) (G.eu σ 1) := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.nash_guarantees_1_of_bounded hN hbd

end KernelGame
end GameTheory
