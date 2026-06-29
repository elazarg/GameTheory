/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.Minimax
import GameTheory.Concepts.ZeroSum.ZeroSumNash
import GameTheory.Concepts.Existence.NashExistenceMixed
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

attribute [local instance] Fintype.ofFinite

/-- Zero-sum is preserved under mixed extension (same outcome space and utility). -/
theorem mixedExtension_isZeroSum {ι : Type} [Fintype ι] {G : KernelGame ι}
    (hzs : G.IsZeroSum) :
    G.mixedExtension.IsZeroSum :=
  hzs

open Classical in
/-- Under bounded utility (no `[Finite G.Outcome]` needed): in a 2-player zero-sum
    game at a Nash equilibrium, deviating player 1 cannot decrease player 0's payoff. -/
theorem IsZeroSum.nash_p0_optimal_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ : Profile G} (hN : G.IsNash σ)
    (s₁ : G.Strategy 1)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu (Function.update σ 1 s₁) 0 ≥ G.eu σ 0 := by
  have h1 : G.eu σ 1 ≥ G.eu (Function.update σ 1 s₁) 1 := by convert hN 1 s₁
  linarith [hzs.eu_neg_of_bounded σ hbd, hzs.eu_neg_of_bounded (Function.update σ 1 s₁) hbd]

open Classical in
/-- In a 2-player zero-sum game at a Nash equilibrium, deviating player 1
    cannot decrease player 0's payoff. -/
theorem IsZeroSum.nash_p0_optimal {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G} (hN : G.IsNash σ)
    (s₁ : G.Strategy 1) :
    G.eu (Function.update σ 1 s₁) 0 ≥ G.eu σ 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.nash_p0_optimal_of_bounded hN s₁ hbd

open Classical in
/-- At a Nash equilibrium, deviating player 0 cannot increase player 0's payoff. -/
theorem nash_p0_cap {G : KernelGame (Fin 2)}
    {σ : Profile G} (hN : G.IsNash σ) (s₀ : G.Strategy 0) :
    G.eu σ 0 ≥ G.eu (Function.update σ 0 s₀) 0 := by
  convert hN 0 s₀

/-- Under bounded utility: all Nash equilibria of a 2-player zero-sum game yield
    the same EU for player 0 (uniqueness of the value). The zero-sum value
    uniqueness is the `c = 0` case of the constant-sum result. -/
theorem IsZeroSum.nash_eu_eq_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 = G.eu τ 0 :=
  IsConstantSum.nash_eu_eq_of_bounded (c := 0) hzs hNσ hNτ hbd

/-- All Nash equilibria of a 2-player zero-sum game yield the same EU for player 0.
    This establishes the uniqueness of the game's value. -/
theorem IsZeroSum.nash_eu_eq {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.eu σ 0 = G.eu τ 0 :=
  IsConstantSum.nash_eu_eq (c := 0) hzs hNσ hNτ

open Classical in
/-- **Von Neumann's Minimax Theorem**, bounded-utility form.

Every finite-strategy 2-player zero-sum game with bounded utility has a value
`v` in mixed strategies:
there exists a mixed Nash equilibrium `σ` with EU `v` for player 0 such that
- player 0's mixed strategy guarantees at least `v` against any opponent, and
- player 1's mixed strategy prevents player 0 from exceeding `v`.

The outcome carrier need not be finite. -/
theorem von_neumann_minimax_of_bounded (G : KernelGame (Fin 2))
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (hzs : G.IsZeroSum)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    ∃ (v : ℝ) (σ : Profile G.mixedExtension),
      G.mixedExtension.IsNash σ ∧
      G.mixedExtension.eu σ 0 = v ∧
      (∀ s₁, G.mixedExtension.eu (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, G.mixedExtension.eu (Function.update σ 0 s₀) 0 ≤ v) := by
  have hzs' : G.mixedExtension.IsZeroSum := mixedExtension_isZeroSum hzs
  obtain ⟨σ, hN⟩ := mixed_nash_exists_of_bounded G hbd
  have hbd' : ∀ i ω, |G.mixedExtension.utility ω i| ≤ C i := hbd
  refine ⟨_, σ, hN, rfl, fun s₁ => ?_, fun s₀ => ?_⟩
  · exact hzs'.nash_p0_optimal_of_bounded hN s₁ hbd'
  · have h := nash_p0_cap hN s₀; linarith

open Classical in
/-- **Von Neumann's Minimax Theorem.**

Every finite 2-player zero-sum game has a value `v` in mixed strategies:
there exists a mixed Nash equilibrium `σ` with EU `v` for player 0 such that
- player 0's mixed strategy guarantees at least `v` against any opponent, and
- player 1's mixed strategy prevents player 0 from exceeding `v`. -/
theorem von_neumann_minimax (G : KernelGame (Fin 2))
    [Finite G.Outcome] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (hzs : G.IsZeroSum) :
    ∃ (v : ℝ) (σ : Profile G.mixedExtension),
      G.mixedExtension.IsNash σ ∧
      G.mixedExtension.eu σ 0 = v ∧
      (∀ s₁, G.mixedExtension.eu (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, G.mixedExtension.eu (Function.update σ 0 s₀) 0 ≤ v) := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact G.von_neumann_minimax_of_bounded hzs hbd

open Classical in
/-- **Interchangeability**, bounded-utility form: in a 2-player zero-sum game,
    if `σ` and `τ` are both Nash equilibria, then the cross profile
    `(σ 0, τ 1)` is also Nash. -/
theorem IsZeroSum.nash_interchangeable_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.IsNash (Function.update σ 1 (τ 1)) := by
  have heq : Function.update σ 1 (τ 1) = Function.update τ 0 (σ 0) := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hval := hzs.nash_eu_eq_of_bounded hNσ hNτ hbd
  have hge : G.eu (Function.update σ 1 (τ 1)) 0 ≥ G.eu σ 0 :=
    hzs.nash_p0_optimal_of_bounded hNσ (τ 1) hbd
  have hle : G.eu (Function.update τ 0 (σ 0)) 0 ≤ G.eu τ 0 := by
    have := nash_p0_cap hNτ (σ 0); linarith
  rw [heq] at hge
  have hval_cross : G.eu (Function.update σ 1 (τ 1)) 0 = G.eu σ 0 := by
    rw [heq]; linarith
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
  have hN1 : ∀ s₁ : G.Strategy 1,
      G.eu (Function.update σ 1 (τ 1)) 1 ≥
      G.eu (Function.update (Function.update σ 1 (τ 1)) 1 s₁) 1 := by
    intro s₁
    have hupd : Function.update (Function.update σ 1 (τ 1)) 1 s₁ =
                Function.update σ 1 s₁ := by
      simp [Function.update_idem]
    rw [hupd]
    have h1 := hzs.eu_neg_of_bounded (Function.update σ 1 (τ 1)) hbd
    have h2 := hzs.eu_neg_of_bounded (Function.update σ 1 s₁) hbd
    have hopt := hzs.nash_p0_optimal_of_bounded hNσ s₁ hbd
    rw [hval_cross] at h1
    linarith
  intro who s'
  fin_cases who
  · exact hN0 s'
  · exact hN1 s'

open Classical in
/-- **Interchangeability**: in a 2-player zero-sum game, if `σ` and `τ` are
    both Nash equilibria, then the "cross" profile `(σ 0, τ 1)` is also Nash. -/
theorem IsZeroSum.nash_interchangeable {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ τ : Profile G}
    (hNσ : G.IsNash σ) (hNτ : G.IsNash τ) :
    G.IsNash (Function.update σ 1 (τ 1)) := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hzs.nash_interchangeable_of_bounded hNσ hNτ hbd

end KernelGame
end GameTheory
