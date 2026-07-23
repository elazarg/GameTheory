/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive
import GameTheory.Concepts.Stochastic.Absorbing

/-!
# The Adaptive Equilibrium Certificate ("V1" verification interface)

A proof-facing, self-contained sufficient condition for
`StochasticGame.exists_uniformEquilibriumPayoff` in terms of history-adaptive
continuation potentials.  It packages the quantitative data needed to run a
Bellman telescope in the style of `GameTheory.Concepts.Stochastic.Adaptive`,
so that once a candidate payoff `v` has been certified by
`IsAdaptiveEquilibriumCertificate`, `IsUniformEquilibriumPayoff` follows by a
single composition with
`StochasticGame.isUniformEquilibriumPayoff_of_deviation_caps`.

The certificate at error level `δ` supplies, together with a behavior
profile `σ` and a horizon threshold `T₀`, one **combined potential**
`φ i : G.HistoryPotential` per player, interpreted as an estimate of the
continuation value of the game for player `i`: `φ i t h` should sit within
`δ` of `v i` at every decision epoch and every history (in particular at the
empty history, `φ i 0 (emptyHist s₀) ≈ v i`), and it should be
*near-harmonic in expectation* along `σ`'s play — adding the target `v i` to
the **expected** current potential is within a per-step error `e i t` of the
one-step lookahead (expected current stage payoff plus expected next-epoch
potential), in both directions.  Against every unilateral behavior
deviation, the *same* potential must dominate the deviator's one-step
lookahead **in expectation under the deviating profile** (an
excessive-function inequality), so that no deviation can gain more than the
accumulated error.  Finally the per-step error budgets must have vanishing
Cesàro average past `T₀`.

The near-harmonicity and deviation-domination clauses are stated as
*expectations* under the relevant history distribution (`σ`'s for on-path
play, `Function.update σ i dev`'s for the deviation `dev`) rather than as
per-history (worst-case-over-every-history) bounds: a history that is never
reached under the profile in question cannot break the certificate.  Only
the boundedness clause stays a per-history bound, because it must control
the potential's expectation under *every* possible deviation simultaneously
— an adversarial, not-fixed-in-advance family of distributions — and is
therefore genuinely a uniform (not merely on-path) regularity requirement on
`φ`.

## Main definitions

* `StochasticGame.IsAdaptiveCertificateAt` — one instance of the certificate
  data at a fixed error level `δ`
* `StochasticGame.IsAdaptiveEquilibriumCertificate` — the certificate:
  an instance at every `δ > 0`

## Main results

* `StochasticGame.finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le`
  / `StochasticGame.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge`
  — expectation-level Bellman guarantee lemmas (self-contained telescoping,
  in the style of `GameTheory.Concepts.Stochastic.Adaptive`)
* `StochasticGame.isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate`
  — the certificate implies `IsUniformEquilibriumPayoff`
* `StochasticGame.isAdaptiveEquilibriumCertificate_of_isAbsorbingState` — the
  certificate holds with a *constant* potential from every absorbing state,
  validating the interface against the known special case
  `StochasticGame.exists_uniformEquilibriumPayoff_of_isAbsorbingState`
  (`GameTheory.Concepts.Stochastic.Absorbing`)
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

-- ============================================================================
-- Expectation-level Bellman guarantee lemmas
-- ============================================================================
--
-- These mirror `finiteAveragePayoff_ge_of_history_bellman_le` /
-- `finiteAveragePayoff_le_of_history_bellman_ge` of
-- `GameTheory.Concepts.Stochastic.Adaptive`, specialized to a *constant*
-- target `v`, but with the Bellman hypothesis stated at the level of
-- expectations (`expectedHistoryValue`, `expectedStagePayoff`) rather than
-- pointwise on every history.  (General-purpose; candidates for migration
-- to `GameTheory.Concepts.Stochastic.Adaptive`.)

/-- A history potential's expectation at a fixed decision epoch inherits a
uniform per-history bound at that epoch. -/
theorem abs_expectedHistoryValue_sub_le (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (φ : G.HistoryPotential)
    {t : ℕ} {v C : ℝ} (hbound : ∀ h : G.Hist t, |φ t h - v| ≤ C) :
    |G.expectedHistoryValue σ s₀ φ t - v| ≤ C := by
  have heq : G.expectedHistoryValue σ s₀ φ t - v =
      expect (G.histDist σ s₀ t) (fun h => φ t h - v) := by
    unfold expectedHistoryValue
    rw [expect_sub, expect_const]
  rw [heq]
  exact abs_expect_le_of_abs_le _ _ hbound

/-- **Expectation-level lower guarantee.**  If, at every decision epoch, the
expected potential offset by a constant target `v` satisfies the
average-reward Bellman inequality *in expectation* — no pointwise
(per-history) hypothesis is needed — and the potential is uniformly bounded
within `C` of `v` at every history, then the finite-horizon average payoff
is at least `v`, up to a `2C / T` boundary loss and the average accumulated
error. -/
theorem finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ} {v C : ℝ}
    (hbound : ∀ t (h : G.Hist t), |φ t h - v| ≤ C)
    (hbellman : ∀ t, v + G.expectedHistoryValue σ s₀ φ t ≤
        G.expectedStagePayoff σ s₀ t who +
          G.expectedHistoryValue σ s₀ φ (t + 1) + e t)
    (hT : 0 < T) :
    v - 2 * C / (T : ℝ) - (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have htel : ∀ T' : ℕ,
      (T' : ℝ) * v + G.expectedHistoryValue σ s₀ φ 0 ≤
        (∑ t ∈ Finset.range T', G.expectedStagePayoff σ s₀ t who) +
          G.expectedHistoryValue σ s₀ φ T' + ∑ t ∈ Finset.range T', e t := by
    intro T'
    induction T' with
    | zero => simp
    | succ T' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      linarith [hbellman T']
  have hV0 : |G.expectedHistoryValue σ s₀ φ 0 - v| ≤ C :=
    G.abs_expectedHistoryValue_sub_le σ s₀ φ (fun h => hbound 0 h)
  have hVT : |G.expectedHistoryValue σ s₀ φ T - v| ≤ C :=
    G.abs_expectedHistoryValue_sub_le σ s₀ φ (fun h => hbound T h)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
      (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  have htelT := htel T
  rw [hsum] at htelT
  rw [show v - 2 * C / (T : ℝ) - (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * v - 2 * C - ∑ t ∈ Finset.range T, e t) / (T : ℝ) by
    field_simp]
  rw [div_le_iff₀ hTreal]
  have h1 := abs_le.mp hV0
  have h2 := abs_le.mp hVT
  nlinarith [htelT, h1.1, h1.2, h2.1, h2.2]

/-- **Expectation-level upper guarantee.**  Dual of
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le`. -/
theorem finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ} {v C : ℝ}
    (hbound : ∀ t (h : G.Hist t), |φ t h - v| ≤ C)
    (hbellman : ∀ t, G.expectedStagePayoff σ s₀ t who +
          G.expectedHistoryValue σ s₀ φ (t + 1) ≤
        v + G.expectedHistoryValue σ s₀ φ t + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      v + 2 * C / (T : ℝ) + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have htel : ∀ T' : ℕ,
      (∑ t ∈ Finset.range T', G.expectedStagePayoff σ s₀ t who) +
          G.expectedHistoryValue σ s₀ φ T' ≤
        (T' : ℝ) * v + G.expectedHistoryValue σ s₀ φ 0 +
          ∑ t ∈ Finset.range T', e t := by
    intro T'
    induction T' with
    | zero => simp
    | succ T' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      linarith [hbellman T']
  have hV0 : |G.expectedHistoryValue σ s₀ φ 0 - v| ≤ C :=
    G.abs_expectedHistoryValue_sub_le σ s₀ φ (fun h => hbound 0 h)
  have hVT : |G.expectedHistoryValue σ s₀ φ T - v| ≤ C :=
    G.abs_expectedHistoryValue_sub_le σ s₀ φ (fun h => hbound T h)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
      (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    field_simp
  have htelT := htel T
  rw [hsum] at htelT
  rw [show v + 2 * C / (T : ℝ) + (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * v + 2 * C + ∑ t ∈ Finset.range T, e t) / (T : ℝ) by
    field_simp]
  rw [le_div_iff₀ hTreal]
  have h1 := abs_le.mp hV0
  have h2 := abs_le.mp hVT
  nlinarith [htelT, h1.1, h1.2, h2.1, h2.2]

/-- **Expectation-level lower guarantee, decoupled bound.**  Variant of
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le` where the
potential is only required to be *uniformly bounded* (`|φ t h| ≤ C`), not
uniformly close to the target `v`.  This is what a potential needs when it is
forced to sit near genuinely different values at different histories (e.g.
near each of several absorbing states' own payoffs), so that no single `v`
is uniformly close to it, yet a boundary-loss estimate is still wanted for
the average-reward telescope.  A direct corollary of
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le`, applied at the
reference point `0` with the error sequence shifted by `v`. -/
theorem finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ} {v C : ℝ}
    (hbound : ∀ t (h : G.Hist t), |φ t h| ≤ C)
    (hbellman : ∀ t, v + G.expectedHistoryValue σ s₀ φ t ≤
        G.expectedStagePayoff σ s₀ t who +
          G.expectedHistoryValue σ s₀ φ (t + 1) + e t)
    (hT : 0 < T) :
    v - 2 * C / (T : ℝ) - (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have hbound' : ∀ t (h : G.Hist t), |φ t h - 0| ≤ C := by simpa using hbound
  have hbellman' : ∀ t, (0 : ℝ) + G.expectedHistoryValue σ s₀ φ t ≤
      G.expectedStagePayoff σ s₀ t who +
        G.expectedHistoryValue σ s₀ φ (t + 1) + (e t - v) := by
    intro t
    have := hbellman t
    linarith
  have hres := G.finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le
    σ s₀ who φ (fun t => e t - v) (v := (0 : ℝ)) (C := C) hbound' hbellman' hT
  have hsum : ∑ t ∈ Finset.range T, (e t - v) =
      (∑ t ∈ Finset.range T, e t) - T * v := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum] at hres
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hrw : (T : ℝ)⁻¹ * ((∑ t ∈ Finset.range T, e t) - T * v) =
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) - v := by
    field_simp
  rw [hrw] at hres
  linarith

/-- **Expectation-level upper guarantee, decoupled bound.**  Dual of
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound`. -/
theorem finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge_of_bound
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ} {v C : ℝ}
    (hbound : ∀ t (h : G.Hist t), |φ t h| ≤ C)
    (hbellman : ∀ t, G.expectedStagePayoff σ s₀ t who +
          G.expectedHistoryValue σ s₀ φ (t + 1) ≤
        v + G.expectedHistoryValue σ s₀ φ t + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      v + 2 * C / (T : ℝ) + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have hbound' : ∀ t (h : G.Hist t), |φ t h - 0| ≤ C := by simpa using hbound
  have hbellman' : ∀ t, G.expectedStagePayoff σ s₀ t who +
        G.expectedHistoryValue σ s₀ φ (t + 1) ≤
      (0 : ℝ) + G.expectedHistoryValue σ s₀ φ t + (e t + v) := by
    intro t
    have := hbellman t
    linarith
  have hres := G.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge
    σ s₀ who φ (fun t => e t + v) (v := (0 : ℝ)) (C := C) hbound' hbellman' hT
  have hsum : ∑ t ∈ Finset.range T, (e t + v) =
      (∑ t ∈ Finset.range T, e t) + T * v := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum] at hres
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hrw : (T : ℝ)⁻¹ * ((∑ t ∈ Finset.range T, e t) + T * v) =
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) + v := by
    field_simp
  rw [hrw] at hres
  linarith

-- ============================================================================
-- The certificate
-- ============================================================================

/-- One instance, at error level `δ`, of an **adaptive equilibrium
certificate**: a behavior profile `σ`, a horizon threshold `T₀ ≥ 2`,
per-player history-adapted potentials `φ`, and per-player per-step error
budgets `e`, satisfying:

* `hbound` — every potential stays within `δ` of the target payoff `v`, at
  every decision epoch and every history.  Specializing to `t = 0` and the
  empty history gives `|φ i 0 (emptyHist s₀) - v i| ≤ δ`.  This clause has
  to be a uniform (per-history) bound rather than an expectation: it must
  control the potential under *every* possible unilateral deviation
  simultaneously (see `hdev`), an adversarial family of distributions fixed
  only after `φ` is chosen.
* `hlow`/`hhigh` — **on-path near-harmonicity in expectation**: adding the
  target payoff `v i` to the *expected* current potential is within the
  per-step error `e i t` of the one-step lookahead (expected current stage
  payoff plus expected next-epoch potential) under `σ`, in both directions.
* `hdev` — **deviation domination in expectation**: for every player `i`
  and every unilateral behavior deviation `dev`, the *same* potential's
  upper-direction inequality persists under the deviating profile
  `Function.update σ i dev`, evaluated in expectation under *that*
  profile's history distribution.
* `hCesaro` — **vanishing error**: past `T₀`, the Cesàro average of every
  player's error budget is at most `δ`.

This is exactly the data consumed by
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le` and
`finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge` (applied to the
constant target `v i`) to produce quantitative finite-horizon payoff
bounds; see `isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate`. -/
def IsAdaptiveCertificateAt (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Prop :=
  ∃ (σ : G.BehaviorProfile) (T₀ : ℕ) (φ : ι → G.HistoryPotential)
    (e : ι → ℕ → ℝ),
    2 ≤ T₀ ∧
    (∀ i t (h : G.Hist t), |φ i t h - v i| ≤ δ) ∧
    (∀ i t, v i + G.expectedHistoryValue σ s₀ (φ i) t ≤
        G.expectedStagePayoff σ s₀ t i +
          G.expectedHistoryValue σ s₀ (φ i) (t + 1) + e i t) ∧
    (∀ i t, G.expectedStagePayoff σ s₀ t i +
          G.expectedHistoryValue σ s₀ (φ i) (t + 1) ≤
        v i + G.expectedHistoryValue σ s₀ (φ i) t + e i t) ∧
    (∀ i (dev : G.BehaviorStrategy i) t,
      G.expectedStagePayoff (Function.update σ i dev) s₀ t i +
          G.expectedHistoryValue (Function.update σ i dev) s₀ (φ i) (t + 1) ≤
        v i + G.expectedHistoryValue (Function.update σ i dev) s₀ (φ i) t +
          e i t) ∧
    ∀ i, ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e i t ≤ δ

/-- **Adaptive equilibrium certificate** ("V1" verification interface).
`v` is witnessed as a uniform-equilibrium-payoff candidate of `G` from `s₀`
by history-adaptive per-player potentials: for every `δ > 0` there is an
instance `IsAdaptiveCertificateAt G s₀ v δ`.

`isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate` shows this
implies `G.IsUniformEquilibriumPayoff s₀ v`; it therefore suffices to
construct one to settle a case of `exists_uniformEquilibriumPayoff`. -/
def IsAdaptiveEquilibriumCertificate (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ → G.IsAdaptiveCertificateAt s₀ v δ

-- ============================================================================
-- Verification: the certificate implies uniform equilibrium payoff
-- ============================================================================

/-- **Verification theorem for the adaptive certificate.**  If `v` admits an
`IsAdaptiveEquilibriumCertificate` at `s₀`, then `v` is a uniform
equilibrium payoff of `G` from `s₀`.

The proof composes, per player and per certificate instance, the
expectation-level Bellman guarantee lemmas above — applied to the on-path
profile `σ` and to every deviating profile `Function.update σ i dev` — with
`isUniformEquilibriumPayoff_of_deviation_caps`. -/
theorem isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : G.IsAdaptiveEquilibriumCertificate s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  obtain ⟨σ, T₀, φ, e, hT₀, hbound, hlow, hhigh, hdev, hCes⟩ :=
    hcert (δ / 2) (by linarith)
  refine ⟨σ, T₀, fun T hT => ⟨fun i => ?_, fun i dev => ?_⟩⟩
  · -- On-path: the average payoff is within `δ` of `v i`.
    have hT0 : 0 < T := by omega
    have hT2 : (2 : ℝ) ≤ (T : ℝ) := by
      have h1 : (T₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      have h2 : (2 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hT₀
      linarith
    have hdiv : 2 * (δ / 2) / (T : ℝ) ≤ δ / 2 := by
      rw [show 2 * (δ / 2) = δ by ring]
      exact div_le_div_of_nonneg_left hδ.le (by norm_num) hT2
    have hlo := G.finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le
      σ s₀ i (φ i) (e i) (v := v i) (C := δ / 2) (hbound i) (hlow i) hT0
    have hhi := G.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge
      σ s₀ i (φ i) (e i) (v := v i) (C := δ / 2) (hbound i) (hhigh i) hT0
    have hCesT := hCes i T hT
    apply abs_le.mpr
    constructor <;> linarith
  · -- Deviation cap: no unilateral deviation gains more than `δ`.
    have hT0 : 0 < T := by omega
    have hT2 : (2 : ℝ) ≤ (T : ℝ) := by
      have h1 : (T₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      have h2 : (2 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hT₀
      linarith
    have hdiv : 2 * (δ / 2) / (T : ℝ) ≤ δ / 2 := by
      rw [show 2 * (δ / 2) = δ by ring]
      exact div_le_div_of_nonneg_left hδ.le (by norm_num) hT2
    have hhi := G.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge
      (Function.update σ i dev) s₀ i (φ i) (e i) (v := v i) (C := δ / 2)
      (hbound i) (hdev i dev) hT0
    have hCesT := hCes i T hT
    linarith

-- ============================================================================
-- Acceptance test: absorbing initial states, via a constant potential
-- ============================================================================

/-- **The certificate holds at every absorbing initial state, with a
constant potential.**  Stationary play of a mixed stage-Nash equilibrium `m`
at an absorbing state `s₀` has exactly constant expected stage payoff at
every epoch, under `σ` and under every unilateral deviation
(`GameTheory.Concepts.Stochastic.Absorbing`); the constant potential
`φ i t h := v i` then has exactly (zero-error) constant expectation
`v i` at every epoch, under every profile, making the near-harmonicity and
deviation-domination clauses hold with equality: this is the "CONSTANT
potential" instance the interface is designed to exhibit. -/
theorem isAdaptiveEquilibriumCertificate_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) :
    ∃ v : Payoff ι, G.IsAdaptiveEquilibriumCertificate s₀ v := by
  obtain ⟨x, hx⟩ := G.exists_isMixedStageNash
  refine ⟨fun i => G.mixedStageEU s₀ (x s₀) i, fun δ hδ => ?_⟩
  have hcont : ∀ (i : ι) (σ' : G.BehaviorProfile) (t' : ℕ),
      G.expectedHistoryValue σ' s₀
        (fun _ _ => G.mixedStageEU s₀ (x s₀) i) t' =
        G.mixedStageEU s₀ (x s₀) i := by
    intro i σ' t'
    unfold expectedHistoryValue
    exact expect_const _ _
  refine ⟨G.stationaryBehaviorProfile (x s₀), 2,
    fun i _ _ => G.mixedStageEU s₀ (x s₀) i, fun _ _ => 0, le_refl 2, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro i t h
    simp only [sub_self, abs_zero]
    linarith
  · intro i t
    rw [hcont i _ t, hcont i _ (t + 1),
      G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
        hAbs (x s₀) t i]
    simp
  · intro i t
    rw [hcont i _ t, hcont i _ (t + 1),
      G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
        hAbs (x s₀) t i]
    simp
  · intro i dev t
    rw [hcont i _ t, hcont i _ (t + 1)]
    have hle := G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
      hAbs (fun d => hx s₀ i d) dev t
    simp only [add_zero]
    linarith
  · intro i T _hT
    simp
    linarith

/-- **Acceptance test.**  Uniform equilibrium payoffs exist from every
absorbing initial state, reproved via the adaptive equilibrium certificate
interface, validating its shape against the known result
`exists_uniformEquilibriumPayoff_of_isAbsorbingState`
(`GameTheory.Concepts.Stochastic.Absorbing`). -/
theorem exists_uniformEquilibriumPayoff_of_isAbsorbingState_of_certificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨v, hv⟩ := G.isAdaptiveEquilibriumCertificate_of_isAbsorbingState hAbs
  exact ⟨v, G.isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate s₀ v hv⟩

/-- The single-state case of the acceptance test, as a corollary: every
subsingleton state space admits a uniform equilibrium payoff, reproved via
the adaptive equilibrium certificate interface. -/
theorem exists_uniformEquilibriumPayoff_of_subsingleton_state_of_certificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Subsingleton G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  haveI : Finite G.State := Finite.of_subsingleton
  exact G.exists_uniformEquilibriumPayoff_of_isAbsorbingState_of_certificate
    (G.isAbsorbingState_of_subsingleton s₀)

end StochasticGame
end GameTheory
