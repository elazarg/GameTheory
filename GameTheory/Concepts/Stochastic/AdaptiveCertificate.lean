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

## "V2": the adaptive potential certificate

The certificate above ("V1") forces every potential to stay within `δ` of a
*constant* target `v` at *every* decision epoch and history. This provably
cannot express the proof that actually witnesses the Big Match's uniform
value `1/2` (`GameTheory.Concepts.Stochastic.BigMatchUniform`): along paths
absorbed at the losing state, the only available certifying potential sits
at `0`, nowhere near `1/2`. The second half of this file packages the
alternative sufficient condition that *does* work there — a **submartingale
floor** / **supermartingale ceiling** argument, needing no bound on the
potential at any history but the initial one — as
`StochasticGame.IsAdaptivePotentialCertificateAt` /
`StochasticGame.IsAdaptivePotentialEquilibriumCertificate` ("V2"), with

* `StochasticGame.finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`
  / `StochasticGame.finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge`
  — the expectation-level floor/ceiling guarantee lemmas
* `StochasticGame.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate`
  — V2's verification theorem
* `StochasticGame.isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState`
  — V1's own worked example (constant potential), re-derived through V2 as a
  corollary, witnessing that V2 strictly generalizes V1

`GameTheory.Concepts.Stochastic.BigMatchUniform.bf_dev_eventually_ge_half_via_certificate`
instantiates V2 with the Big Match's actual ingredients (`bfX`/`bfXExpect`),
the case V1 cannot express.
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

-- ============================================================================
-- "V2": the adaptive potential certificate (non-constant target)
-- ============================================================================
--
-- `BigMatchUniform.lean`'s actual proof of the Big Match's Stage 3c bound
-- combines two genuinely different ingredients (its Pieces 2–4): (Piece 2)
-- an *expectation-level submartingale* fact about a potential `φ` alone —
-- the expected potential is monotone nondecreasing along play, giving a
-- permanent *floor* `E[φ 0] ≤ E[φ t]` for every later `t`, entirely
-- independent of the stage payoffs — and (Piece 3) a *per-stage* inequality
-- relating *that same epoch's* expected potential to *that same epoch's*
-- expected stage payoff, with no successor-epoch term at all. Substituting
-- the floor into the per-stage inequality and summing over the horizon
-- (Piece 4's two budget-summability bounds) gives the average-payoff
-- guarantee directly, *without ever needing a bound on `φ` at any history
-- other than the initial one*: contrast the V1 Bellman clause, which
-- necessarily involves both `φ t` and `φ (t + 1)` and is telescoped, so it
-- needs `φ` controlled at *every* epoch to bound the telescope's two loose
-- ends.
--
-- `IsAdaptivePotentialCertificateAt` packages exactly this alternative
-- sufficient condition. A certificate needs *three* directions (on-path
-- lower bound, on-path upper bound, deviation cap); V1 supplies all three
-- from *one* potential per player because its `hbound` clause bounds that
-- potential everywhere. V2 does not have that clause, so it supplies a
-- **separate** potential for each direction, each with its own initial
-- value (close to the target), one-step expectation-level monotonicity
-- fact (submartingale for the lower direction, supermartingale for the
-- upper two), per-stage payoff bound, and vanishing-Cesàro-average budget.
-- V1's constant-potential certificates satisfy all of this trivially
-- (constancy makes every monotonicity clause hold with equality), so V1's
-- own worked example (`isAdaptiveEquilibriumCertificate_of_isAbsorbingState`)
-- is re-derived below as
-- `isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState`, a
-- corollary of V2's machinery via a constant potential.

/-- `expectedHistoryValue` at the initial epoch is just the potential's own
value at the (unique) empty history, independent of the behavior profile:
`histDist _ _ 0` is always the point mass on `emptyHist s₀`. -/
theorem expectedHistoryValue_zero (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State) (φ : G.HistoryPotential) :
    G.expectedHistoryValue σ s₀ φ 0 = φ 0 (G.emptyHist s₀) := by
  unfold expectedHistoryValue
  rw [G.histDist_zero, expect_pure]

/-- **Submartingale floor lower guarantee.** If a history potential's
expectation along `σ` is monotone nondecreasing, and at every decision epoch
the expected potential is dominated, up to a per-step budget `e t`, by that
epoch's expected stage payoff, then the finite-horizon average payoff is at
least the potential's *initial* expectation minus the average accumulated
budget. Unlike `finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le`,
no bound on `φ` at any history other than the initial one is needed: the
monotonicity clause alone supplies the floor `E[φ 0] ≤ E[φ t]` at every `t`,
so the successor-epoch potential never has to be controlled. This is the
general-purpose lemma behind `BigMatchUniform.lean`'s Piece 2 + Piece 3
combination (`bfXExpect_ge_bfPotential` + `expectedStagePayoff_bfDevProfile_ge`). -/
theorem finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ}
    (hmono : ∀ t, G.expectedHistoryValue σ s₀ φ t ≤ G.expectedHistoryValue σ s₀ φ (t + 1))
    (hbellman : ∀ t, G.expectedHistoryValue σ s₀ φ t ≤
        G.expectedStagePayoff σ s₀ t who + e t)
    (hT : 0 < T) :
    G.expectedHistoryValue σ s₀ φ 0 - (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have hmono' : Monotone (fun t => G.expectedHistoryValue σ s₀ φ t) :=
    monotone_nat_of_le_succ hmono
  have hstage : ∀ t, G.expectedHistoryValue σ s₀ φ 0 ≤
      G.expectedStagePayoff σ s₀ t who + e t := fun t =>
    (hmono' (Nat.zero_le t)).trans (hbellman t)
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hstage t)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at hs
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hEq : (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
      (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]; field_simp
  rw [hEq] at hs
  rw [show G.expectedHistoryValue σ s₀ φ 0 - (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * G.expectedHistoryValue σ s₀ φ 0 - ∑ t ∈ Finset.range T, e t) / (T : ℝ) by
    field_simp]
  rw [div_le_iff₀ hTreal]
  nlinarith [hs]

/-- **Supermartingale ceiling upper guarantee.** Dual of
`finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`. -/
theorem finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (φ : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ}
    (hmono : ∀ t, G.expectedHistoryValue σ s₀ φ (t + 1) ≤ G.expectedHistoryValue σ s₀ φ t)
    (hbellman : ∀ t, G.expectedStagePayoff σ s₀ t who ≤
        G.expectedHistoryValue σ s₀ φ t + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      G.expectedHistoryValue σ s₀ φ 0 + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have hmono' : Antitone (fun t => G.expectedHistoryValue σ s₀ φ t) :=
    antitone_nat_of_succ_le hmono
  have hstage : ∀ t, G.expectedStagePayoff σ s₀ t who ≤
      G.expectedHistoryValue σ s₀ φ 0 + e t := fun t =>
    (hbellman t).trans (by linarith [hmono' (Nat.zero_le t)])
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hstage t)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hEq : (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) =
      (T : ℝ) * G.finiteAveragePayoff s₀ T σ who := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]; field_simp
  rw [hEq] at hs
  rw [show G.expectedHistoryValue σ s₀ φ 0 + (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * G.expectedHistoryValue σ s₀ φ 0 + ∑ t ∈ Finset.range T, e t) / (T : ℝ) by
    field_simp]
  rw [le_div_iff₀ hTreal]
  nlinarith [hs]

/-- One instance, at error level `δ`, of an **adaptive equilibrium potential
certificate** ("V2"): a behavior profile `σ`, a horizon threshold `T₀ ≥ 2`,
and, for *each* of the three directions a certificate needs — the on-path
lower bound, the on-path upper bound, and the deviation cap — a **separate**
per-player history potential (`φlo`/`φhi`/`φdv`) together with its own
initial value close to `v`, one-step expectation-level monotonicity fact,
per-stage payoff bound, and vanishing-Cesàro-average budget
(`elo`/`ehi`/`edv`).  The deviation budget may depend on the deviating
behavior strategy; the verifier only needs its bound after that deviation
has been fixed. Unlike `IsAdaptiveCertificateAt`, no potential here is
required to stay close to `v` at any history other than the initial one. -/
def IsAdaptivePotentialCertificateAt (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Prop :=
  ∃ (σ : G.BehaviorProfile) (T₀ : ℕ)
    (φlo φhi φdv : ι → G.HistoryPotential) (elo ehi : ι → ℕ → ℝ)
    (edv : ∀ i, G.BehaviorStrategy i → ℕ → ℝ),
    2 ≤ T₀ ∧
    (∀ i, |φlo i 0 (G.emptyHist s₀) - v i| ≤ δ) ∧
    (∀ i, |φhi i 0 (G.emptyHist s₀) - v i| ≤ δ) ∧
    (∀ i, |φdv i 0 (G.emptyHist s₀) - v i| ≤ δ) ∧
    (∀ i t, G.expectedHistoryValue σ s₀ (φlo i) t ≤
        G.expectedHistoryValue σ s₀ (φlo i) (t + 1)) ∧
    (∀ i t, G.expectedHistoryValue σ s₀ (φlo i) t ≤
        G.expectedStagePayoff σ s₀ t i + elo i t) ∧
    (∀ i t, G.expectedHistoryValue σ s₀ (φhi i) (t + 1) ≤
        G.expectedHistoryValue σ s₀ (φhi i) t) ∧
    (∀ i t, G.expectedStagePayoff σ s₀ t i ≤
        G.expectedHistoryValue σ s₀ (φhi i) t + ehi i t) ∧
    (∀ i (dev : G.BehaviorStrategy i) t,
      G.expectedHistoryValue (Function.update σ i dev) s₀ (φdv i) (t + 1) ≤
        G.expectedHistoryValue (Function.update σ i dev) s₀ (φdv i) t) ∧
    (∀ i (dev : G.BehaviorStrategy i) t,
      G.expectedStagePayoff (Function.update σ i dev) s₀ t i ≤
        G.expectedHistoryValue (Function.update σ i dev) s₀ (φdv i) t +
          edv i dev t) ∧
    (∀ i, ∀ T, T₀ ≤ T → (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, elo i t ≤ δ) ∧
    (∀ i, ∀ T, T₀ ≤ T → (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ehi i t ≤ δ) ∧
    (∀ i (dev : G.BehaviorStrategy i), ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, edv i dev t ≤ δ)

/-- **Adaptive equilibrium potential certificate** ("V2" verification
interface). `v` is witnessed as a uniform-equilibrium-payoff candidate of
`G` from `s₀` by the floor/ceiling mechanism: for every `δ > 0` there is an
instance `IsAdaptivePotentialCertificateAt G s₀ v δ`. Strictly generalizes
`IsAdaptiveEquilibriumCertificate` ("V1"): see
`isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState` for V1's own
worked example re-derived here via a constant potential, and
`GameTheory.Concepts.Stochastic.BigMatchUniform.bf_dev_eventually_ge_half_via_certificate`
for the genuinely non-constant instance V1 cannot express. -/
def IsAdaptivePotentialEquilibriumCertificate (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ → G.IsAdaptivePotentialCertificateAt s₀ v δ

/-- **Verification theorem for the adaptive potential certificate.** If `v`
admits an `IsAdaptivePotentialEquilibriumCertificate` at `s₀`, then `v` is a
uniform equilibrium payoff of `G` from `s₀`. The proof composes, per player
and per certificate instance, `finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`
(on-path lower bound, from `φlo`) with
`finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge` (on-path
upper bound from `φhi`, and the deviation cap from `φdv` evaluated under
every deviating profile), through
`isUniformEquilibriumPayoff_of_deviation_caps`. -/
theorem isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : G.IsAdaptivePotentialEquilibriumCertificate s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  obtain ⟨σ, T₀, φlo, φhi, φdv, elo, ehi, edv, hT₀,
      hinitLo, hinitHi, hinitDv, hmonoLo, hbellLo, hmonoHi, hbellHi, hmonoDv,
      hbellDv, hCesLo, hCesHi, hCesDv⟩ := hcert (δ / 2) (by linarith)
  refine ⟨σ, T₀, fun T hT => ⟨fun i => ?_, fun i dev => ?_⟩⟩
  · -- On-path: the average payoff is within `δ` of `v i`.
    have hT0 : 0 < T := by omega
    have hlo := G.finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le
      σ s₀ i (φlo i) (elo i) (hmonoLo i) (hbellLo i) hT0
    have hhi := G.finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
      σ s₀ i (φhi i) (ehi i) (hmonoHi i) (hbellHi i) hT0
    rw [G.expectedHistoryValue_zero] at hlo hhi
    have h1 := hinitLo i
    have h2 := hinitHi i
    have h3 := hCesLo i T hT
    have h4 := hCesHi i T hT
    apply abs_le.mpr
    rw [abs_le] at h1 h2
    constructor <;> linarith
  · -- Deviation cap: no unilateral deviation gains more than `δ`.
    have hT0 : 0 < T := by omega
    have hdv := G.finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
      (Function.update σ i dev) s₀ i (φdv i) (edv i dev)
        (hmonoDv i dev) (hbellDv i dev) hT0
    rw [G.expectedHistoryValue_zero] at hdv
    have h1 := hinitDv i
    have h3 := hCesDv i dev T hT
    rw [abs_le] at h1
    linarith

-- ============================================================================
-- V2 acceptance test: V1's absorbing-state example, via a constant potential
-- ============================================================================

/-- **V1 as a corollary of V2.** The certificate holds at every absorbing
initial state with a *constant* potential shared by all three directions,
re-deriving V1's own worked example
(`isAdaptiveEquilibriumCertificate_of_isAbsorbingState`) through V2's
machinery: constancy makes every monotonicity clause hold with equality, so
the floor/ceiling mechanism reduces exactly to V1's shape. -/
theorem isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) :
    ∃ v : Payoff ι, G.IsAdaptivePotentialEquilibriumCertificate s₀ v := by
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
    (fun i _ _ => G.mixedStageEU s₀ (x s₀) i),
    (fun i _ _ => G.mixedStageEU s₀ (x s₀) i),
    (fun i _ _ => G.mixedStageEU s₀ (x s₀) i),
    fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, le_refl 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp only [sub_self, abs_zero]; linarith
  · intro i; simp only [sub_self, abs_zero]; linarith
  · intro i; simp only [sub_self, abs_zero]; linarith
  · intro i t; rw [hcont i _ t, hcont i _ (t + 1)]
  · intro i t
    rw [hcont i _ t,
      G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
        hAbs (x s₀) t i]
    simp
  · intro i t; rw [hcont i _ t, hcont i _ (t + 1)]
  · intro i t
    rw [hcont i _ t,
      G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
        hAbs (x s₀) t i]
    simp
  · intro i dev t; rw [hcont i _ t, hcont i _ (t + 1)]
  · intro i dev t
    rw [hcont i _ t]
    have hle := G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
      hAbs (fun d => hx s₀ i d) dev t
    simp only [add_zero]
    linarith
  · intro i T _hT; simp; linarith
  · intro i T _hT; simp; linarith
  · intro i dev T _hT; simp; linarith

/-- **Acceptance test, via V2.** Uniform equilibrium payoffs exist from every
absorbing initial state, reproved via the adaptive *potential* certificate
interface — demonstrating that V2 strictly generalizes V1
(`exists_uniformEquilibriumPayoff_of_isAbsorbingState_of_certificate`). -/
theorem exists_uniformEquilibriumPayoff_of_isAbsorbingState_of_potentialCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] {s₀ : G.State}
    (hAbs : G.IsAbsorbingState s₀) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨v, hv⟩ := G.isAdaptivePotentialEquilibriumCertificate_of_isAbsorbingState hAbs
  exact ⟨v, G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate s₀ v hv⟩

-- ============================================================================
-- "V2, decoupled bound" flavor: exact telescoping against a bounded
-- (not close-to-`v`) potential
-- ============================================================================
--
-- The monotonicity-based V2 certificate above (`IsAdaptivePotentialCertificateAt`)
-- captures the Big Match's proof, but not every non-constant certificate
-- has a monotone potential. `TransitionIndependent.lean`'s uniform
-- equilibrium payoff (re-derived via a certificate in
-- `TransitionIndependentCertificate.lean`) instead has an *exact*
-- Bellman/telescoping identity — via the Poisson equation `f = g + (Pu - u)`
-- for the induced Markov chain's stage reward `f` — against a potential `u`
-- that is merely *bounded*, not monotone and not close to the target `g`
-- anywhere. This is precisely what the *already existing*
-- `finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound` /
-- `finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge_of_bound` above
-- were built for (their docstrings anticipate exactly this "several
-- different absorbing values" situation). `IsAdaptiveDecoupledCertificateAt`
-- packages them at the certificate level: it is *exactly* V1's
-- `IsAdaptiveCertificateAt` with the `hbound` clause's target `v`
-- *decoupled* from the boundedness constant `C` — replacing "every
-- potential stays within `δ` of `v` everywhere" by "every potential stays
-- within a *fixed* `C` of `0` everywhere". Consequently every V1 instance
-- is *literally* (not just in the constant-potential special case) a
-- decoupled instance too (`isAdaptiveDecoupledCertificateAt_of_isAdaptiveCertificateAt`),
-- giving a second, more direct sense in which "V1 is a corollary of V2".

/-- One instance, at error level `δ`, of an **adaptive decoupled equilibrium
certificate**: exactly `IsAdaptiveCertificateAt`'s data and telescoping
clauses (`hlow`/`hhigh`/`hdev`, `hCesaro`), except the potentials' bound `C`
is *decoupled* from the target `v` (`hbound : |φ i t h| ≤ C i`, not `|φ i t h
- v i| ≤ δ`), and the Cesàro clause additionally absorbs the resulting
`2 * C i / T` boundary-loss term (matching the conclusion of
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound`). -/
def IsAdaptiveDecoupledCertificateAt (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Prop :=
  ∃ (σ : G.BehaviorProfile) (T₀ : ℕ) (φ : ι → G.HistoryPotential)
    (C : ι → ℝ) (e : ι → ℕ → ℝ),
    2 ≤ T₀ ∧
    (∀ i t (h : G.Hist t), |φ i t h| ≤ C i) ∧
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
      2 * C i / (T : ℝ) + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e i t ≤ δ

/-- **Adaptive decoupled equilibrium certificate.** `v` is witnessed as a
uniform-equilibrium-payoff candidate of `G` from `s₀` by exact (or
near-exact) Bellman telescoping against a *bounded* (not necessarily
close-to-`v`) potential: for every `δ > 0` there is an instance
`IsAdaptiveDecoupledCertificateAt G s₀ v δ`. -/
def IsAdaptiveDecoupledEquilibriumCertificate (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ → G.IsAdaptiveDecoupledCertificateAt s₀ v δ

/-- **Verification theorem for the adaptive decoupled certificate.**
Directly composes
`finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound` /
`finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge_of_bound` (applied
to `σ` and to every deviating profile) with
`isUniformEquilibriumPayoff_of_deviation_caps`; no `δ`-halving is needed
since the certificate's own `hCesaro` clause already bounds the *combined*
boundary-loss-plus-error term by `δ`. -/
theorem isUniformEquilibriumPayoff_of_isAdaptiveDecoupledEquilibriumCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : G.IsAdaptiveDecoupledEquilibriumCertificate s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  obtain ⟨σ, T₀, φ, C, e, hT₀, hbound, hlow, hhigh, hdev, hCes⟩ := hcert δ hδ
  refine ⟨σ, T₀, fun T hT => ⟨fun i => ?_, fun i dev => ?_⟩⟩
  · have hT0 : 0 < T := by omega
    have hlo := G.finiteAveragePayoff_ge_of_expectedHistoryValue_bellman_le_of_bound
      σ s₀ i (φ i) (e i) (hbound i) (hlow i) hT0
    have hhi := G.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge_of_bound
      σ s₀ i (φ i) (e i) (hbound i) (hhigh i) hT0
    have hCesT := hCes i T hT
    apply abs_le.mpr
    constructor <;> linarith
  · have hT0 : 0 < T := by omega
    have hhi := G.finiteAveragePayoff_le_of_expectedHistoryValue_bellman_ge_of_bound
      (Function.update σ i dev) s₀ i (φ i) (e i) (hbound i) (hdev i dev) hT0
    have hCesT := hCes i T hT
    linarith

/-- **V1 embeds into the decoupled V2 flavor.** Every V1 certificate instance
gives a decoupled certificate instance at the same `δ`, taking
`C i := |v i| + δ / 2`: V1's `hbound` (`|φ - v| ≤ δ / 2`) trivially gives
`|φ| ≤ C`, and V1's `hlow`/`hhigh`/`hdev` are *already* stated in exactly
`IsAdaptiveDecoupledCertificateAt`'s shape (the same telescoping clauses).
The horizon threshold is enlarged past V1's own `T₀` (which only controls
`(T)⁻¹ ∑ e`, not the boundary-loss term `2 * C i / T`, since `C i` depends
on `v i` and so is not itself controlled by `T₀`) to also make
`2 * C i / T ≤ δ / 2` for every player, using the finiteness of `ι`. -/
theorem isAdaptiveDecoupledCertificateAt_of_isAdaptiveCertificateAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι) {δ : ℝ} (hδ : 0 < δ)
    (hcert : G.IsAdaptiveCertificateAt s₀ v (δ / 2)) :
    G.IsAdaptiveDecoupledCertificateAt s₀ v δ := by
  classical
  obtain ⟨σ, T₀, φ, e, hT₀, hbound, hlow, hhigh, hdev, hCes⟩ := hcert
  set C : ι → ℝ := fun i => |v i| + δ / 2 with hCdef
  have hCnn : ∀ i, 0 ≤ C i := fun i => by positivity
  set Cmax : ℝ := ∑ i, C i with hCmaxdef
  have hCmaxnn : 0 ≤ Cmax := Finset.sum_nonneg fun i _ => hCnn i
  have hCmax : ∀ i, C i ≤ Cmax :=
    fun i => Finset.single_le_sum (fun j _ => hCnn j) (Finset.mem_univ i)
  obtain ⟨T₁, hT₁⟩ := exists_nat_gt (4 * Cmax / δ)
  refine ⟨σ, max T₀ (T₁ + 1), φ, C, e, le_trans hT₀ (le_max_left _ _), ?_, hlow, hhigh, hdev, ?_⟩
  · intro i t h
    calc |φ i t h| = |φ i t h - v i + v i| := by ring_nf
      _ ≤ |φ i t h - v i| + |v i| := abs_add_le _ _
      _ ≤ δ / 2 + |v i| := by linarith [hbound i t h]
      _ = C i := by rw [hCdef]; ring
  · intro i T hT
    have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : T₁ + 1 ≤ T := le_trans (le_max_right _ _) hT
    have hTreal : (0 : ℝ) < T := by
      have : (0 : ℕ) < T₁ + 1 := Nat.succ_pos _
      exact_mod_cast lt_of_lt_of_le this hT1
    have hT1real : (T₁ : ℝ) < (T : ℝ) := by
      have : T₁ < T := by omega
      exact_mod_cast this
    have hCesT := hCes i T hT0
    have hdiv : 2 * C i / (T : ℝ) ≤ δ / 2 := by
      have hstep : 2 * Cmax / (T : ℝ) ≤ δ / 2 := by
        rw [div_le_iff₀ hTreal]
        have h4 : 4 * Cmax < (T : ℝ) * δ := by
          rw [div_lt_iff₀ hδ] at hT₁
          calc 4 * Cmax < (T₁ : ℝ) * δ := hT₁
            _ ≤ (T : ℝ) * δ := mul_le_mul_of_nonneg_right hT1real.le hδ.le
        linarith
      have hmono : 2 * C i / (T : ℝ) ≤ 2 * Cmax / (T : ℝ) := by
        gcongr
        exact hCmax i
      linarith [hmono, hstep]
    linarith [hCesT, hdiv]

/-- **V1's verification theorem, re-derived as a corollary of "V2,
decoupled".** Same statement as
`isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate`, via the
literal embedding `IsAdaptiveCertificateAt → IsAdaptiveDecoupledCertificateAt`
above instead of Adaptive.lean's original (unbounded-`C`) telescope. -/
theorem isUniformEquilibriumPayoff_of_isAdaptiveEquilibriumCertificate_via_decoupled
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : G.IsAdaptiveEquilibriumCertificate s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_isAdaptiveDecoupledEquilibriumCertificate
  intro δ hδ
  exact G.isAdaptiveDecoupledCertificateAt_of_isAdaptiveCertificateAt s₀ v hδ
    (hcert (δ / 2) (by linarith))

-- ============================================================================
-- One-sided guarantee certificates and the zero-sum equilibrium wrapper
-- ============================================================================
--
-- The Big Match's capstone (`BigMatchUniform.exists_uniformEquilibriumPayoff_live`)
-- factors as: the maximizer secures `1/2` with one fixed strategy against
-- *every* minimizer completion (Stage 3c), the minimizer secures `-1/2`
-- with a different fixed strategy against *every* maximizer completion
-- (Stage 2, exactly, no error), and a zero-sum identity turns each
-- player's own security guarantee into the *other* player's deviation cap.
-- This is a general pattern, not special to the Big Match: `who` securing
-- `v` is exactly a *one-sided* (single-player, all-directions-but-one)
-- instance of the submartingale-floor mechanism
-- (`finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`) with
-- the crucial difference from `IsAdaptivePotentialCertificateAt` that the
-- guarantee must hold *simultaneously for every opponent completion* of
-- `who`'s fixed strategy, not just for one on-path profile.
--
-- `IsOneSidedGuaranteeCertificate` packages exactly this; the zero-sum
-- wrapper (`isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees`)
-- assembles two of them (one per player of a `Bool`-indexed zero-sum game,
-- matching `BigMatchUniform.lean`'s own `Player := Bool` convention) into a
-- full `IsUniformEquilibriumPayoff`, reusable well beyond the Big Match
-- (e.g. as the assembly step of a Mertens–Neyman-style uniform value
-- theorem).

/-- One instance, at error level `δ`, of a **one-sided guarantee
certificate**: player `who` has a *fixed* strategy `σwho`, together with a
horizon threshold `T₀`, such that against *every* completion `opp` of the
other players' strategies (the profile `Function.update opp who σwho`, which
fixes `who` at `σwho` and leaves every other player at whatever `opp` says),
`who`'s finite-average payoff is within `δ` of `vwho` from below, at every
horizon `T ≥ T₀`. The quantifier order is load-bearing: `σwho` and `T₀` are
chosen *before* the opponent completion `opp`, so the same fixed strategy
and horizon threshold work uniformly against every possible opponent
behavior. -/
def IsOneSidedGuaranteeCertificateAt (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (who : ι) (vwho δ : ℝ) : Prop :=
  ∃ (σwho : G.BehaviorStrategy who) (T₀ : ℕ), 2 ≤ T₀ ∧
    ∀ (opp : G.BehaviorProfile) (T : ℕ), T₀ ≤ T →
      vwho - δ ≤ G.finiteAveragePayoff s₀ T (Function.update opp who σwho) who

/-- **One-sided guarantee certificate.** Player `who` has a fixed strategy
securing finite-average payoff `vwho` (up to a vanishing error) against
*every* completion of the other players' behavior: for every `δ > 0` there
is an instance `IsOneSidedGuaranteeCertificateAt G s₀ who vwho δ`. -/
def IsOneSidedGuaranteeCertificate (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (who : ι) (vwho : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → G.IsOneSidedGuaranteeCertificateAt s₀ who vwho δ

/-- **Sufficient condition for a one-sided guarantee, from the
submartingale-V2 machinery.** A fixed securing strategy `σwho`, together
with, for *every* error level `δ` and *every* opponent completion `opp`, a
history potential whose expectation under `Function.update opp who σwho`
(i) starts within `δ` of `vwho`, (ii) is monotone nondecreasing, and (iii)
dominates `who`'s stage payoff up to a per-step budget with eventually
`≤ δ`-Cesàro average — exactly
`finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le`'s own
hypotheses, quantified over every opponent completion — gives a one-sided
guarantee for `who` securing `vwho`. This is the general mechanism behind
"`who` secures `vwho` against all opponents": a per-player submartingale
floor, evaluated at every possible completion of the opponents' play. -/
theorem isOneSidedGuaranteeCertificate_of_submartingale
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (who : ι) (vwho : ℝ)
    (hdata : ∀ δ : ℝ, 0 < δ → ∃ (σwho : G.BehaviorStrategy who) (T₀ : ℕ)
      (φ : G.BehaviorProfile → G.HistoryPotential)
      (e : G.BehaviorProfile → ℕ → ℝ),
      2 ≤ T₀ ∧
      (∀ opp : G.BehaviorProfile, vwho - δ ≤ φ opp 0 (G.emptyHist s₀)) ∧
      (∀ (opp : G.BehaviorProfile) t,
        G.expectedHistoryValue (Function.update opp who σwho) s₀ (φ opp) t ≤
          G.expectedHistoryValue (Function.update opp who σwho) s₀ (φ opp) (t + 1)) ∧
      (∀ (opp : G.BehaviorProfile) t,
        G.expectedHistoryValue (Function.update opp who σwho) s₀ (φ opp) t ≤
          G.expectedStagePayoff (Function.update opp who σwho) s₀ t who + e opp t) ∧
      ∀ (opp : G.BehaviorProfile) T, T₀ ≤ T →
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e opp t ≤ δ) :
    G.IsOneSidedGuaranteeCertificate s₀ who vwho := by
  intro δ hδ
  obtain ⟨σwho, T₀, φ, e, hT₀, hinit, hmono, hbellman, hCes⟩ := hdata (δ / 2) (by linarith)
  refine ⟨σwho, T₀, hT₀, fun opp T hT => ?_⟩
  have hT0 : 0 < T := by omega
  have hg := G.finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le
    (Function.update opp who σwho) s₀ who (φ opp) (e opp) (hmono opp) (hbellman opp) hT0
  rw [G.expectedHistoryValue_zero] at hg
  have hces := hCes opp T hT
  linarith [hinit opp]

-- ============================================================================
-- The zero-sum equilibrium wrapper (`Bool`-indexed games)
-- ============================================================================

/-- Zero-sum condition for a two-player `Bool`-indexed stochastic game,
matching `BigMatchUniform.lean`'s `Player := Bool` convention (`false` the
maximizing player, `true` the minimizing player): the minimizer's stage
payoff is the negative of the maximizer's, at every state and joint action.
The `Bool`-indexed analogue of `StochasticGame.IsZeroSum` (stated there for
`Fin 2`). -/
def IsZeroSumBoolGame (G : StochasticGame Bool) : Prop :=
  ∀ (s : G.State) (a : G.JointAct), G.stagePayoff s a true = -G.stagePayoff s a false

theorem IsZeroSumBoolGame.stageEUAt_true_eq_neg_false
    {G : StochasticGame Bool} (hzs : G.IsZeroSumBoolGame)
    (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    G.stageEUAt σ h true = -G.stageEUAt σ h false := by
  unfold stageEUAt
  rw [show (fun a => G.stagePayoff h.2 a true) =
      fun a => (-1 : ℝ) * G.stagePayoff h.2 a false by
    funext a
    rw [hzs h.2 a]
    ring]
  rw [expect_const_mul]
  ring

theorem IsZeroSumBoolGame.expectedStagePayoff_true_eq_neg_false
    {G : StochasticGame Bool} (hzs : G.IsZeroSumBoolGame)
    (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.expectedStagePayoff σ s₀ t true = -G.expectedStagePayoff σ s₀ t false := by
  unfold expectedStagePayoff
  rw [show (fun h => G.stageEUAt σ h true) =
      fun h => (-1 : ℝ) * G.stageEUAt σ h false by
    funext h
    rw [hzs.stageEUAt_true_eq_neg_false]
    ring]
  rw [expect_const_mul]
  ring

/-- **Zero-sum identity for finite-average payoffs.** The `Bool`-indexed
analogue of `BigMatchUniform.finiteAveragePayoff_minimizer`, derived here
generically from `IsZeroSumBoolGame` rather than from the Big Match's own
reward table. -/
theorem IsZeroSumBoolGame.finiteAveragePayoff_true_eq_neg_false
    {G : StochasticGame Bool} [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSumBoolGame) (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) :
    G.finiteAveragePayoff s₀ T σ true = -G.finiteAveragePayoff s₀ T σ false := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t true) =
      ∑ t ∈ Finset.range T, (-1 : ℝ) * G.expectedStagePayoff σ s₀ t false by
    apply Finset.sum_congr rfl
    intro t _
    rw [hzs.expectedStagePayoff_true_eq_neg_false]
    ring]
  rw [← Finset.mul_sum]
  ring

/-- **The zero-sum equilibrium wrapper.** For a `Bool`-indexed zero-sum
stochastic game, a one-sided guarantee for the maximizer (`false`) securing
`v` *together with* a one-sided guarantee for the minimizer (`true`)
securing `-v` assemble into a full uniform equilibrium payoff
`(v, -v)`. The two guarantees supply the two deviation caps directly (each
player's own security guarantee, evaluated at the *deviating* completion,
bounds the *other* player via the zero-sum identity), and the on-path
closeness comes from evaluating both guarantees at the on-path profile.
This is the reusable assembly step: constructing the two one-sided
certificates is the only game-specific work left to any particular uniform
value theorem (e.g. Mertens–Neyman) built on top of it. -/
theorem isUniformEquilibriumPayoff_of_isZeroSumBoolGame_of_oneSidedGuarantees
    (G : StochasticGame Bool) [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSumBoolGame) (s₀ : G.State) (v : ℝ)
    (hmax : G.IsOneSidedGuaranteeCertificate s₀ false v)
    (hmin : G.IsOneSidedGuaranteeCertificate s₀ true (-v)) :
    G.IsUniformEquilibriumPayoff s₀ (fun who => match who with | false => v | true => -v) := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ _
  intro δ hδ
  obtain ⟨σmax, Tmax, hTmax, hmaxg⟩ := hmax (δ / 2) (by linarith)
  obtain ⟨σmin, Tmin, hTmin, hming⟩ := hmin (δ / 2) (by linarith)
  set σ : G.BehaviorProfile := fun who => match who with
    | false => σmax
    | true => σmin with hσdef
  have hσfalse : σ false = σmax := rfl
  have hσtrue : σ true = σmin := rfl
  refine ⟨σ, max Tmax Tmin, fun T hT => ⟨fun who => ?_, fun who dev => ?_⟩⟩
  · -- on-path closeness
    have hT0 : Tmax ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : Tmin ≤ T := le_trans (le_max_right _ _) hT
    have hupd1 : Function.update σ false σmax = σ := by
      rw [← hσfalse]; exact Function.update_eq_self false σ
    have hupd2 : Function.update σ true σmin = σ := by
      rw [← hσtrue]; exact Function.update_eq_self true σ
    have h1 := hmaxg σ T hT0
    have h2 := hming σ T hT1
    rw [hupd1] at h1
    rw [hupd2] at h2
    have hzsσ := hzs.finiteAveragePayoff_true_eq_neg_false σ s₀ T
    cases who with
    | false =>
      change |G.finiteAveragePayoff s₀ T σ false - v| ≤ δ
      rw [hzsσ] at h2
      apply abs_le.mpr
      constructor <;> linarith
    | true =>
      change |G.finiteAveragePayoff s₀ T σ true - (-v)| ≤ δ
      rw [hzsσ]
      apply abs_le.mpr
      constructor <;> linarith
  · -- deviation caps
    have hT0 : Tmax ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : Tmin ≤ T := le_trans (le_max_right _ _) hT
    cases who with
    | false =>
      -- Cap the maximizer's own deviation via the minimizer's guarantee.
      change G.finiteAveragePayoff s₀ T (Function.update σ false dev) false ≤ v + δ
      set opp : G.BehaviorProfile := Function.update σ false dev with hoppdef
      have hoppTrue : opp true = σmin := by
        rw [hoppdef, Function.update_of_ne (by decide), hσtrue]
      have hupd : Function.update opp true σmin = opp := by
        rw [← hoppTrue]; exact Function.update_eq_self true opp
      have h2 := hming opp T hT1
      rw [hupd] at h2
      have hzsopp := hzs.finiteAveragePayoff_true_eq_neg_false opp s₀ T
      rw [hzsopp] at h2
      linarith
    | true =>
      -- Cap the minimizer's own deviation via the maximizer's guarantee.
      change G.finiteAveragePayoff s₀ T (Function.update σ true dev) true ≤ -v + δ
      set opp : G.BehaviorProfile := Function.update σ true dev with hoppdef
      have hoppFalse : opp false = σmax := by
        rw [hoppdef, Function.update_of_ne (by decide), hσfalse]
      have hupd : Function.update opp false σmax = opp := by
        rw [← hoppFalse]; exact Function.update_eq_self false opp
      have h1 := hmaxg opp T hT0
      rw [hupd] at h1
      have hzsopp := hzs.finiteAveragePayoff_true_eq_neg_false opp s₀ T
      rw [hzsopp]
      linarith

end StochasticGame
end GameTheory
