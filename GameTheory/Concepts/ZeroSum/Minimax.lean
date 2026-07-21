/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Equilibrium.SecureEquilibrium
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.ZeroSum.CoalitionSecurity
import GameTheory.Concepts.ZeroSum.ZeroSumNash
import GameTheory.Concepts.Existence.NashExistenceMixed

/-!
# Minimax Concepts

Minimax concepts for kernel-based games: guarantees and saddle points.

Provides:
- `KernelGame.Guarantees` — player `who` playing `s` guarantees at least payoff `v`
- `KernelGame.Guarantees.mono` — monotonicity of guarantees in the bound
- `KernelGame.IsSaddlePoint` — saddle point for 2-player games
- `KernelGame.isSaddlePoint_iff_isNash` — saddle point ↔ Nash equilibrium for 2-player games
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

attribute [local instance] Fintype.ofFinite

open Classical in
/-- A profile `σ` is a saddle point for a 2-player game if neither player can
    improve by unilateral deviation. -/
def IsSaddlePoint (G : KernelGame (Fin 2)) (σ : Profile G) : Prop :=
  (∀ s₀ : G.Strategy 0, G.eu σ 0 ≥ G.eu (Function.update σ 0 s₀) 0) ∧
  (∀ s₁ : G.Strategy 1, G.eu σ 1 ≥ G.eu (Function.update σ 1 s₁) 1)

/-- In a 2-player game, a profile is a saddle point if and only if it is a Nash equilibrium. -/
theorem isSaddlePoint_iff_isNash (G : KernelGame (Fin 2)) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ G.IsNash σ := by
  constructor
  · intro ⟨h0, h1⟩ who s'
    fin_cases who
    · exact h0 s'
    · exact h1 s'
  · intro hN
    exact ⟨fun s₀ => hN 0 s₀, fun s₁ => hN 1 s₁⟩

open Classical in
/-- `Guarantees` is equivalent to order-theoretic worst-case EU being at least
    `v`, without enumerating the profile space. -/
theorem guarantees_iff_worstCaseEUInf_ge
    (G : KernelGame ι) [Nonempty (Profile G)]
    (who : ι) (s : G.Strategy who) (v : ℝ)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who))) :
    G.Guarantees who s v ↔ G.worstCaseEUInf who s ≥ v := by
  constructor
  · intro hg
    exact le_ciInf hg
  · intro hge σ
    exact le_trans hge (G.worstCaseEUInf_le who s hbdd σ)

open Classical in
/-- Finite-profile specialization: `Guarantees` is equivalent to finite
    worst-case EU being at least `v`. -/
theorem guarantees_iff_worstCaseEU_ge
    (G : KernelGame ι) [Finite (Profile G)]
    [Nonempty (Profile G)]
    (who : ι) (s : G.Strategy who) (v : ℝ) :
    G.Guarantees who s v ↔ G.worstCaseEU who s ≥ v := by
  letI := Fintype.ofFinite (Profile G)
  constructor
  · intro hg
    apply Finset.le_inf'
    intro σ _
    exact hg σ
  · intro hge σ
    exact le_trans hge (G.worstCaseEU_le who s σ)

open Classical in
/-- A singleton coalition can guarantee `v` exactly when some strategy's
order-theoretic worst-case expected utility is at least `v`. -/
theorem coalitionGuaranteesEU_singleton_iff_exists_worstCaseEUInf_ge
    (G : KernelGame ι) [Nonempty (Profile G)]
    (who : ι) (v : ℝ)
    (hbdd : ∀ s : G.Strategy who,
      BddBelow (Set.range (fun σ : Profile G =>
        G.eu (Function.update σ who s) who))) :
    G.CoalitionGuaranteesEU {who} (fun ω => G.utility ω who) v ↔
      ∃ s : G.Strategy who, G.worstCaseEUInf who s ≥ v := by
  rw [G.coalitionGuaranteesEU_singleton_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (G.guarantees_iff_worstCaseEUInf_ge who s v (hbdd s)).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (G.guarantees_iff_worstCaseEUInf_ge who s v (hbdd s)).mpr hs⟩

open Classical in
/-- Any singleton-coalition EU guarantee is below the order-theoretic security
level, under the usual bounded-above hypothesis for `iSup`. -/
theorem coalitionGuaranteesEU_singleton_le_securityLevelSup
    (G : KernelGame ι) [Nonempty (Profile G)]
    (who : ι) (v : ℝ)
    (h : G.CoalitionGuaranteesEU {who} (fun ω => G.utility ω who) v)
    (hbddSec : BddAbove (Set.range (fun s : G.Strategy who =>
      G.worstCaseEUInf who s))) :
    v ≤ G.securityLevelSup who := by
  rw [G.coalitionGuaranteesEU_singleton_iff] at h
  rcases h with ⟨s, hs⟩
  exact G.le_securityLevelSup_of_forall_eu_ge who s v hs hbddSec

open Classical in
/-- In a finite game, singleton-coalition EU forceability exactly characterizes
thresholds below the player's security level. -/
theorem coalitionGuaranteesEU_singleton_iff_le_securityLevel
    (G : KernelGame ι)
    [Finite (Profile G)] [Nonempty (Profile G)]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (who : ι) (v : ℝ) :
    G.CoalitionGuaranteesEU {who} (fun ω => G.utility ω who) v ↔
      v ≤ G.securityLevel who := by
  rw [G.coalitionGuaranteesEU_singleton_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact G.le_securityLevel_of_forall_eu_ge who s v hs
  · intro hv
    obtain ⟨s, hs⟩ := G.exists_securityStrategy who
    refine ⟨s, fun σ => ?_⟩
    calc
      v ≤ G.securityLevel who := hv
      _ = G.worstCaseEU who s := hs.symm
      _ ≤ G.eu (Function.update σ who s) who := G.worstCaseEU_le who s σ

open Classical in
/-- In a two-player zero-sum game, secure equilibrium and Nash equilibrium
coincide: an own-payoff tie also fixes the opponent's payoff. -/
theorem IsZeroSum.isSecureEq_iff_isNash {G : KernelGame (Fin 2)}
    [Finite G.Outcome] (hzs : G.IsZeroSum) (σ : Profile G) :
    G.IsSecureEq σ ↔ G.IsNash σ := by
  constructor
  · intro h
    exact h.isNash
  · intro hN
    rw [G.isSecureEq_iff_no_securelyProfitableDeviation]
    intro who s hprof
    have hNfor := (G.IsNash_iff_IsNashFor_eu σ).mp hN
    have hbest := (G.toGameForm.isNashFor_iff G.euPref σ).mp hNfor who s
    simp only [SecurelyProfitableLawDeviation, lawEU] at hprof
    simp only [euPref] at hbest
    rcases hprof with himprove | ⟨htie, _hall, other, hother, hharm⟩
    · exact (not_lt_of_ge hbest himprove)
    · fin_cases who
      · have ho : other = 1 := by
          fin_cases other
          · exact (hother rfl).elim
          · rfl
        subst other
        change expect (G.outcomeKernel (Function.update σ 0 s))
          (fun ω => G.utility ω 0) =
            expect (G.outcomeKernel σ) (fun ω => G.utility ω 0) at htie
        change expect (G.outcomeKernel (Function.update σ 0 s))
          (fun ω => G.utility ω 1) <
            expect (G.outcomeKernel σ) (fun ω => G.utility ω 1) at hharm
        have hcurrent := hzs.eu_neg σ
        have hdeviated := hzs.eu_neg (Function.update σ 0 s)
        simp only [eu] at hcurrent hdeviated
        linarith
      · have ho : other = 0 := by
          fin_cases other
          · rfl
          · exact (hother rfl).elim
        subst other
        change expect (G.outcomeKernel (Function.update σ 1 s))
          (fun ω => G.utility ω 1) =
            expect (G.outcomeKernel σ) (fun ω => G.utility ω 1) at htie
        change expect (G.outcomeKernel (Function.update σ 1 s))
          (fun ω => G.utility ω 0) <
            expect (G.outcomeKernel σ) (fun ω => G.utility ω 0) at hharm
        have hcurrent := hzs.eu_neg σ
        have hdeviated := hzs.eu_neg (Function.update σ 1 s)
        simp only [eu] at hcurrent hdeviated
        linarith

/-! ## Zero-sum minimax facts -/

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
