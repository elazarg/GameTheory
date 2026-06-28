/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Learning.NoRegretToCCE
import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Welfare.Smoothness

/-!
# Self-play: from per-player no-regret to coarse correlated equilibrium and welfare

Assembles the no-regret reduction (`NoRegretToCCE`) with independent per-player learning.
When each player plays an independent (product) mixed strategy each round, the joint external
regret of the product distribution is exactly that player's mixed-extension deviation gain.
Hence a uniform per-player regret bound makes the time-average of play an ε-coarse correlated
equilibrium, and Roughgarden smoothness then bounds its social welfare — the **price of anarchy
of learning**.

`selfPlay_timeAverage_isεCCE` takes the per-player cumulative regret bound `B` as a hypothesis. The
per-player gain sequence a no-regret learner consumes is `g_t a = mixedExtension.eu (update (p t) who
(pure a)) who`; since `mw_externalRegret_le` requires `[0,1]` gains, this file also provides the
affine normalization (`normGain` into the band `[lo i, lo i + W]`) and the scaling identity that
relates a normalized regret bound back to actual payoffs (multiplying it by `W`). The coupled
construction that actually discharges the hypothesis — multiplicative-weights self-play — is built on
top of these pieces in `MWSelfPlay`.

## Main results

* `KernelGame.externalRegret_pmfPi` — joint external regret of a product profile equals the
  player's mixed-extension deviation gain
* `KernelGame.selfPlay_timeAverage_isεCCE` — a per-player cumulative regret bound `B` over horizon
  `T` makes the time-average of independent play a `(B/T)`-coarse correlated equilibrium
* `KernelGame.IsSmooth.epsilonCoarseCorrelated_bound` — smoothness bounds the welfare of an ε-CCE
  up to an additive `(card ι)·ε`, the price of anarchy of (approximate) learning
-/

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι] (G : KernelGame ι) [Finite G.Outcome]

/-- The joint external regret of an independent (product) profile equals the deviating player's
    gain in the mixed extension: switching from the product strategy to the pure action `s'`. -/
theorem externalRegret_pmfPi (p : Profile G.mixedExtension) (who : ι) (s' : G.Strategy who) :
    G.externalRegret (pmfPi p) who s'
      = G.mixedExtension.eu (Function.update p who (PMF.pure s')) who
        - G.mixedExtension.eu p who := by
  rw [externalRegret_eq_swapRegret_const, swapRegret, unilateralDeviationDistribution_pmfPi]
  have hmap : PMF.map (fun _ => s') (p who) = PMF.pure s' := PMF.map_const (p who) s'
  rw [hmap, correlatedEu_pmfPi_eq_mixedExtension_eu, correlatedEu_pmfPi_eq_mixedExtension_eu]
  congr 2

/-! ### Payoff normalization: rescaling bounded utilities into `[0,1]` for multiplicative weights -/

variable {lo : ι → ℝ} {W : ℝ}

/-- Player `i`'s **normalized pure-deviation gain**: the mixed-extension EU of deviating to the pure
    action `a`, affinely mapped into `[0,1]` via the per-player band `[lo i, lo i + W]`. This is the
    gain sequence fed to a `[0,1]`-gain no-regret learner such as multiplicative weights. -/
noncomputable def normGain (lo : ι → ℝ) (W : ℝ) (p : Profile G.mixedExtension)
    (i : ι) (a : G.Strategy i) : ℝ :=
  (G.mixedExtension.eu (Function.update p i (PMF.pure a)) i - lo i) / W

/-- Own-strategy linearity: the expected pure-action EU under player `i`'s own mixed strategy
    equals their EU in the profile. -/
theorem expect_eu_update [∀ j, Finite (G.Strategy j)] (p : Profile G.mixedExtension) (i : ι) :
    expect (p i) (fun a => G.mixedExtension.eu (Function.update p i (PMF.pure a)) i)
      = G.mixedExtension.eu p i := by
  have h := G.weighted_gain_sum_zero p i
  simp only [mixedGain] at h
  rw [expect_sub, expect_const] at h
  linarith

/-- Normalized gains lie in `[0,1]` when every utility lies in the band `[lo i, lo i + W]`. -/
theorem normGain_mem_Icc (hW : 0 < W)
    (hbd : ∀ i ω, G.utility ω i ∈ Set.Icc (lo i) (lo i + W))
    (p : Profile G.mixedExtension) (i : ι) (a : G.Strategy i) :
    G.normGain lo W p i a ∈ Set.Icc (0 : ℝ) 1 := by
  haveI : Finite G.mixedExtension.Outcome := inferInstanceAs (Finite G.Outcome)
  have hlo : lo i ≤ G.mixedExtension.eu (Function.update p i (PMF.pure a)) i := by
    have hm := expect_mono (G.mixedExtension.outcomeKernel (Function.update p i (PMF.pure a)))
      (fun _ => lo i) (fun ω => G.utility ω i) (fun ω => (hbd i ω).1)
    rwa [expect_const] at hm
  have hhi : G.mixedExtension.eu (Function.update p i (PMF.pure a)) i ≤ lo i + W := by
    have hm := expect_mono (G.mixedExtension.outcomeKernel (Function.update p i (PMF.pure a)))
      (fun ω => G.utility ω i) (fun _ => lo i + W) (fun ω => (hbd i ω).2)
    rwa [expect_const] at hm
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · rw [normGain]; exact div_nonneg (by linarith) hW.le
  · rw [normGain, div_le_one hW]; linarith

/-- The expected normalized gain is the profile's normalized EU. -/
theorem expect_normGain [∀ j, Finite (G.Strategy j)]
    (p : Profile G.mixedExtension) (i : ι) :
    expect (p i) (G.normGain lo W p i) = (G.mixedExtension.eu p i - lo i) / W := by
  have hrw : (G.normGain lo W p i)
      = fun a => (1 / W) * (G.mixedExtension.eu (Function.update p i (PMF.pure a)) i - lo i) := by
    funext a; rw [normGain]; ring
  rw [hrw, expect_const_mul, expect_sub, expect_const, expect_eu_update]
  ring

/-- **Scaling identity** — the bridge from a `[0,1]`-gain regret bound to actual payoffs: the true
    pure-deviation gain is `W` times the centered normalized gain. -/
theorem eu_deviation_eq_W_mul_normGain [∀ j, Finite (G.Strategy j)] (hW : 0 < W)
    (p : Profile G.mixedExtension) (i : ι) (a : G.Strategy i) :
    G.mixedExtension.eu (Function.update p i (PMF.pure a)) i - G.mixedExtension.eu p i
      = W * (G.normGain lo W p i a - expect (p i) (G.normGain lo W p i)) := by
  rw [expect_normGain G]
  simp only [normGain]
  have hWne : W ≠ 0 := hW.ne'
  field_simp
  ring

/-- **Independent no-regret play yields a coarse correlated equilibrium.** If every player's
    cumulative mixed-extension deviation gain (against the realized independent play) is at most
    `B` over horizon `T`, then the time-average of play is a `(B/T)`-coarse correlated equilibrium.
    A no-regret learner (`mw_externalRegret_le`, on the gains rescaled into `[0,1]`) bounds `B`; the
    resulting `(B/T)` shrinks under a horizon-dependent learning-rate tuning (not formalized here). -/
theorem selfPlay_timeAverage_isεCCE [Finite (Profile G)] {T : ℕ} [NeZero T]
    (p : Fin T → Profile G.mixedExtension) {B : ℝ}
    (hreg : ∀ who s', (∑ t, (G.mixedExtension.eu (Function.update (p t) who (PMF.pure s')) who
              - G.mixedExtension.eu (p t) who)) ≤ B) :
    G.IsεCoarseCorrelatedEq (B / T) (G.timeAverage (fun t => pmfPi (p t))) := by
  apply timeAverage_isεCCE_of_regret_le
  intro who s'
  have hcongr : (∑ t, G.externalRegret (pmfPi (p t)) who s')
      = ∑ t, (G.mixedExtension.eu (Function.update (p t) who (PMF.pure s')) who
              - G.mixedExtension.eu (p t) who) :=
    Finset.sum_congr rfl (fun t _ => externalRegret_pmfPi G (p t) who s')
  rw [hcongr]
  exact hreg who s'

/-- **Price of anarchy of approximate learning.** If `G` is `(λ, μ)`-smooth then the welfare of any
    `ε`-coarse correlated equilibrium `ν` satisfies `λ · W(t) ≤ (1 + μ) · E[W] + (card ι) · ε` for
    every profile `t`. The additive loss is `(card ι)·ε` — one `ε` of slack per player. With the
    no-regret time-average (ε → 0) this recovers Roughgarden's robust price-of-anarchy bound in
    the limit. -/
theorem IsSmooth.epsilonCoarseCorrelated_bound [Finite (Profile G)]
    {lam mu ε : ℝ} (hsmooth : G.IsSmooth lam mu)
    {ν : PMF (Profile G)} (hν : G.IsεCoarseCorrelatedEq ε ν) (t : Profile G) :
    lam * G.socialWelfare t
      ≤ (1 + mu) * (∑ i, G.correlatedEu ν i) + (Fintype.card ι) * ε := by
  set CW := ∑ i, G.correlatedEu ν i with hCW
  have hCW_eq : CW = expect ν (fun s => G.socialWelfare s) := by
    rw [hCW, show (∑ i, G.correlatedEu ν i) = ∑ i, expect ν (fun s => G.eu s i) from
      Finset.sum_congr rfl fun i _ => G.correlatedEu_eq_expect_eu ν i, expect_sum_comm]
    simp only [socialWelfare]
  have hdev_sum : ∑ i, expect ν (fun s => G.eu (Function.update s i (t i)) i)
      ≤ CW + (Fintype.card ι : ℝ) * ε := by
    have hstep : ∑ i, expect ν (fun s => G.eu (Function.update s i (t i)) i)
        ≤ ∑ i : ι, (G.correlatedEu ν i + ε) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hcce := hν i (t i)
      rw [G.correlatedEu_constantDeviationDistribution_eq_expect_update ν i (t i)] at hcce
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
    rw [hCW]; linarith
  have hsmooth_exp : lam * G.socialWelfare t - mu * CW
      ≤ ∑ i, expect ν (fun s => G.eu (Function.update s i (t i)) i) := by
    rw [hCW_eq, expect_sum_comm]
    have heq : expect ν (fun s => lam * G.socialWelfare t - mu * G.socialWelfare s)
        = lam * G.socialWelfare t - mu * expect ν (fun s => G.socialWelfare s) := by
      rw [expect_sub, expect_const ν (lam * G.socialWelfare t),
        expect_const_mul ν mu (fun s => G.socialWelfare s)]
    rw [← heq]
    exact expect_mono ν _ _ fun s => hsmooth s t
  nlinarith [hdev_sum, hsmooth_exp]

end KernelGame

end GameTheory
