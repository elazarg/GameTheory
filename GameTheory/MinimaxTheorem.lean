import GameTheory.Minimax
import GameTheory.ZeroSumNash
import GameTheory.NashExistenceMixed

/-!
# Von Neumann's Minimax Theorem

The minimax theorem for finite 2-player zero-sum games.

## Main results

- `KernelGame.mixedExtension_isZeroSum` — zero-sum is preserved under mixed extension
- `KernelGame.IsZeroSum.nash_eu_eq` — all Nash equilibria of a zero-sum game yield the
  same EU for each player (uniqueness of the game's value)
- `KernelGame.von_neumann_minimax` — **main theorem**: every finite 2-player zero-sum
  game has a value in mixed strategies
-/

noncomputable section

open scoped BigOperators
namespace GameTheory
namespace KernelGame

-- ============================================================================
-- Zero-sum preserved under mixed extension
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- Zero-sum is preserved under mixed extension (same outcome space and utility). -/
theorem mixedExtension_isZeroSum {ι : Type} [Fintype ι] {G : KernelGame ι}
    [∀ i, Fintype (G.Strategy i)] (hzs : G.IsZeroSum) :
    G.mixedExtension.IsZeroSum :=
  hzs

-- ============================================================================
-- Nash equilibrium value properties in zero-sum games
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a 2-player zero-sum game at a Nash equilibrium, deviating player 1
    cannot decrease player 0's payoff. -/
theorem IsZeroSum.nash_p0_optimal {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G} (hN : G.IsNash σ)
    (s₁ : G.Strategy 1) :
    G.eu (Function.update σ 1 s₁) 0 ≥ G.eu σ 0 := by
  have h1 : G.eu σ 1 ≥ G.eu (Function.update σ 1 s₁) 1 := by convert hN 1 s₁
  linarith [hzs.eu_neg σ, hzs.eu_neg (Function.update σ 1 s₁)]

set_option linter.unusedFintypeInType false in
open Classical in
/-- At a Nash equilibrium, deviating player 0 cannot increase player 0's payoff. -/
theorem nash_p0_cap {G : KernelGame (Fin 2)}
    {σ : Profile G} (hN : G.IsNash σ) (s₀ : G.Strategy 0) :
    G.eu σ 0 ≥ G.eu (Function.update σ 0 s₀) 0 := by
  convert hN 0 s₀

set_option linter.unusedFintypeInType false in
open Classical in
/-- All Nash equilibria of a 2-player zero-sum game yield the same EU for player 0.
    This establishes the uniqueness of the game's value. -/
theorem IsZeroSum.nash_eu_eq {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.eu σ 0 = G.eu τ 0 := by
  apply le_antisymm
  · -- σ guarantees eu σ 0, τ caps at eu τ 0
    have hopt := hzs.nash_p0_optimal hNσ (τ 1)
    have hcap : G.eu τ 0 ≥ G.eu (Function.update τ 0 (σ 0)) 0 := by convert hNτ 0 (σ 0)
    have heq : Function.update σ 1 (τ 1) = Function.update τ 0 (σ 0) := by
      funext i; fin_cases i <;> simp [Function.update]
    rw [heq] at hopt; linarith
  · -- Symmetric
    have hopt := hzs.nash_p0_optimal hNτ (σ 1)
    have hcap : G.eu σ 0 ≥ G.eu (Function.update σ 0 (τ 0)) 0 := by convert hNσ 0 (τ 0)
    have heq : Function.update τ 1 (σ 1) = Function.update σ 0 (τ 0) := by
      funext i; fin_cases i <;> simp [Function.update]
    rw [heq] at hopt; linarith

-- ============================================================================
-- Von Neumann's Minimax Theorem
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Von Neumann's Minimax Theorem.**

Every finite 2-player zero-sum game has a value `v` in mixed strategies:
there exists a mixed Nash equilibrium `σ` with EU `v` for player 0 such that
- player 0's mixed strategy guarantees at least `v` against any opponent, and
- player 1's mixed strategy prevents player 0 from exceeding `v`. -/
theorem von_neumann_minimax (G : KernelGame (Fin 2))
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (hzs : G.IsZeroSum) :
    ∃ (v : ℝ) (σ : Profile G.mixedExtension),
      G.mixedExtension.IsNash σ ∧
      G.mixedExtension.eu σ 0 = v ∧
      (∀ s₁, G.mixedExtension.eu (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, G.mixedExtension.eu (Function.update σ 0 s₀) 0 ≤ v) := by
  have hzs' : G.mixedExtension.IsZeroSum := mixedExtension_isZeroSum hzs
  obtain ⟨σ, hN⟩ := mixed_nash_exists G
  haveI : Fintype G.mixedExtension.Outcome := ‹Fintype G.Outcome›
  refine ⟨_, σ, hN, rfl, fun s₁ => ?_, fun s₀ => ?_⟩
  · exact hzs'.nash_p0_optimal hN s₁
  · have h := nash_p0_cap hN s₀; linarith

end KernelGame
end GameTheory
