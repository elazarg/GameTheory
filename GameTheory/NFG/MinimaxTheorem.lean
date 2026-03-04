import GameTheory.NFG.Minimax
import GameTheory.NFG.ZeroSumNash
import GameTheory.Concepts.NashExistenceMixed
import Math.Probability

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

open Math.Probability
namespace KernelGame

-- ============================================================================
-- Zero-sum preserved under mixed extension
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- Zero-sum is preserved under mixed extension (same outcome space and utility). -/
theorem mixedExtension_isZeroSum {ι : Type} [Fintype ι] {G : KernelGame ι}
    [DecidableEq ι] [∀ i, Fintype (G.Strategy i)] (hzs : G.IsZeroSum) :
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
      funext i
      fin_cases i <;> simp [Function.update]
    rw [heq] at hopt; linarith
  · -- Symmetric
    have hopt := hzs.nash_p0_optimal hNτ (σ 1)
    have hcap : G.eu σ 0 ≥ G.eu (Function.update σ 0 (τ 0)) 0 := by convert hNσ 0 (τ 0)
    have heq : Function.update τ 1 (σ 1) = Function.update σ 0 (τ 0) := by
      funext i
      fin_cases i <;> simp [Function.update]
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

-- ============================================================================
-- Interchangeability of Nash equilibria in zero-sum games
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Interchangeability**: in a 2-player zero-sum game, if `σ` and `τ` are
    both Nash equilibria, then the "cross" profile `(σ 0, τ 1)` is also Nash.
    This is a consequence of the saddle-point characterization. -/
theorem IsZeroSum.nash_interchangeable {G : KernelGame (Fin 2)} [Fintype G.Outcome]
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.IsNash (Function.update σ 1 (τ 1)) := by
  -- The cross profile equals both update σ 1 (τ 1) and update τ 0 (σ 0)
  have heq : Function.update σ 1 (τ 1) = Function.update τ 0 (σ 0) := by
    funext i
    fin_cases i <;> simp [Function.update]
  -- Game value
  have hval := hzs.nash_eu_eq hNσ hNτ
  -- EU of cross profile = v (squeezed between two bounds)
  have hge : G.eu (Function.update σ 1 (τ 1)) 0 ≥ G.eu σ 0 :=
    hzs.nash_p0_optimal hNσ (τ 1)
  have hle : G.eu (Function.update τ 0 (σ 0)) 0 ≤ G.eu τ 0 := by
    have := nash_p0_cap hNτ (σ 0); linarith
  rw [heq] at hge
  have hval_cross : G.eu (Function.update σ 1 (τ 1)) 0 = G.eu σ 0 := by
    rw [heq]; linarith
  -- Prove Nash for player 0: cap from τ
  have hN0 : ∀ s₀ : G.Strategy 0,
      G.eu (Function.update σ 1 (τ 1)) 0 ≥
      G.eu (Function.update (Function.update σ 1 (τ 1)) 0 s₀) 0 := by
    intro s₀
    have hupd : Function.update (Function.update σ 1 (τ 1)) 0 s₀ =
                Function.update τ 0 s₀ := by
      simpa [Function.update_idem] using congrArg (fun p => Function.update p 0 s₀) heq
    rw [hval_cross, hupd]
    have := nash_p0_cap hNτ s₀
    linarith [hval]
  -- Prove Nash for player 1: optimality from σ
  have hN1 : ∀ s₁ : G.Strategy 1,
      G.eu (Function.update σ 1 (τ 1)) 1 ≥
      G.eu (Function.update (Function.update σ 1 (τ 1)) 1 s₁) 1 := by
    intro s₁
    have hupd : Function.update (Function.update σ 1 (τ 1)) 1 s₁ =
                Function.update σ 1 s₁ := by
      simp [Function.update_idem]
    rw [hupd]
    have h1 := hzs.eu_neg (Function.update σ 1 (τ 1))
    have h2 := hzs.eu_neg (Function.update σ 1 s₁)
    have hopt := hzs.nash_p0_optimal hNσ s₁
    rw [hval_cross] at h1
    linarith
  -- Combine
  intro who s'
  fin_cases who
  · convert hN0 s'
  · convert hN1 s'

end KernelGame
end GameTheory
