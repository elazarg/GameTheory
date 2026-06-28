/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Learning.SelfPlay
import Math.OnlineLearning

/-!
# Multiplicative-weights self-play and coarse correlated equilibrium

The constructive capstone of Tier A: every player runs multiplicative weights on their own
normalized pure-deviation gains, and the time-average of the resulting independent play is an
ε-coarse correlated equilibrium with an explicit `ε = W·(L/η + (eᵑ−1−η)/η·T)/T` for any fixed
learning rate `η`. This turns the conditional `selfPlay_timeAverage_isεCCE` into a *witnessed*
bound: a concrete decentralized learning process whose time-average is an ε-CCE. For a *fixed* `η`
this `ε` does not tend to `0` (it tends to `W·(eᵑ−1−η)/η`); driving it to `0` needs the
horizon-dependent tuning `η ≈ √(L/T)`, which (like the matching `mw_externalRegret_le` asymptotics)
is not formalized here — so "reaches the set of CCE" is exhibited as an explicit per-horizon bound,
not a convergence theorem.

The construction tracks the **cumulative score** rather than the payoff sequence, which makes it
a plain structural recursion (no circular definition): `mwScore` accumulates the current round's
normalized gains, and `mwProfile` is the exponential-weights distribution of the score. The score
equals the cumulative gain (`mwScore_eq_cumGain`), so `mwProfile` is exactly the `mwDist` algorithm
(`mwProfile_eq_mwDist`) and the game-free regret bound `mw_externalRegret_le` applies per player.

## Main definitions

* `KernelGame.mwScore` / `KernelGame.mwProfile` — the self-play score and per-round profile

## Main results

* `KernelGame.mwSelfPlay_timeAverage_isεCCE` — the time-average of MW self-play is an ε-CCE
* `KernelGame.exists_mwSelfPlay_isεCCE` — existence of an ε-CCE realized by MW self-play
-/

namespace GameTheory

open Math.Probability Math.PMFProduct Math.OnlineLearning

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι] (G : KernelGame ι) [Finite G.Outcome]
  [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
variable (η : ℝ) (lo : ι → ℝ) (W : ℝ)

/-- Cumulative normalized-gain score of multiplicative-weights self-play. Each round adds the
    normalized pure-deviation gain of the current self-play profile. -/
noncomputable def mwScore : ℕ → ∀ i, G.Strategy i → ℝ
  | 0 => fun _ _ => 0
  | (t + 1) => fun i a =>
      mwScore t i a
        + G.normGain lo W (fun j => expWeights η (mwScore t j)) i a

/-- The self-play profile at round `t`: each player plays exponential weights on their score. -/
noncomputable def mwProfile (t : ℕ) : Profile G.mixedExtension :=
  fun i => expWeights η (G.mwScore η lo W t i)

omit [Finite G.Outcome] in
/-- The score equals the cumulative normalized gain of the self-play trajectory. -/
theorem mwScore_eq_cumGain (t : ℕ) (i : ι) (a : G.Strategy i) :
    G.mwScore η lo W t i a
      = cumGain (fun s => G.normGain lo W (G.mwProfile η lo W s) i) t a := by
  induction t with
  | zero => simp [mwScore, cumGain]
  | succ t ih =>
    rw [cumGain_succ, ← ih]
    simp only [mwScore]
    rfl

omit [Finite G.Outcome] in
/-- The self-play profile is exactly the multiplicative-weights algorithm run on the player's
    own normalized-gain sequence. -/
theorem mwProfile_eq_mwDist (t : ℕ) (i : ι) :
    G.mwProfile η lo W t i
      = mwDist η (fun s => G.normGain lo W (G.mwProfile η lo W s) i) t := by
  rw [mwDist_eq_expWeights]
  simp only [mwProfile]
  congr 1
  funext a
  exact G.mwScore_eq_cumGain η lo W t i a

/-- **Multiplicative-weights self-play is an ε-coarse correlated equilibrium.** With utilities in
    the per-player band `[lo i, lo i + W]`, a fixed learning rate `η > 0`, and `L` a uniform upper
    bound on `log |Aᵢ|`, the time-average of independent MW self-play over horizon `T` is an
    ε-coarse correlated equilibrium with the explicit `ε = W·(L/η + (eᵑ−1−η)/η·T)/T`. For fixed `η`
    this `ε` does not vanish (it tends to `W·(eᵑ−1−η)/η`); the horizon-dependent tuning `η ≈ √(L/T)`
    that sends it to `0` is not formalized here. -/
theorem mwSelfPlay_timeAverage_isεCCE {L : ℝ} (hη : 0 < η) (hW : 0 < W)
    (hbd : ∀ i ω, G.utility ω i ∈ Set.Icc (lo i) (lo i + W))
    (hL : ∀ i, Real.log (Fintype.card (G.Strategy i)) ≤ L)
    (T : ℕ) [NeZero T] :
    G.IsεCoarseCorrelatedEq (W * (L / η + (Real.exp η - 1 - η) / η * T) / T)
      (G.timeAverage (fun t : Fin T => pmfPi (G.mwProfile η lo W (t : ℕ)))) := by
  apply selfPlay_timeAverage_isεCCE
  intro who s'
  -- Rewrite the cumulative deviation gain as `W · (best-action gain − algorithm gain)`.
  have halg : (∑ s ∈ Finset.range T,
        expect ((G.mwProfile η lo W s) who) (G.normGain lo W (G.mwProfile η lo W s) who))
      = algGain η (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T := by
    rw [algGain]
    exact Finset.sum_congr rfl (fun s _ => by rw [G.mwProfile_eq_mwDist η lo W s who])
  have key : (∑ t : Fin T, (G.mixedExtension.eu
        (Function.update (G.mwProfile η lo W (t : ℕ)) who (PMF.pure s')) who
        - G.mixedExtension.eu (G.mwProfile η lo W (t : ℕ)) who))
      = W * (cumGain (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T s'
           - algGain η (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T) := by
    rw [Fin.sum_univ_eq_sum_range (fun s =>
      G.mixedExtension.eu (Function.update (G.mwProfile η lo W s) who (PMF.pure s')) who
      - G.mixedExtension.eu (G.mwProfile η lo W s) who) T]
    rw [Finset.sum_congr rfl (fun s _ =>
      G.eu_deviation_eq_W_mul_normGain hW (G.mwProfile η lo W s) who s')]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, halg]
    rfl
  rw [key]
  -- Bound `best-action gain − algorithm gain` by the regret bound.
  have hbound : cumGain (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T s'
      - algGain η (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T
      ≤ L / η + (Real.exp η - 1 - η) / η * T := by
    calc cumGain (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T s'
            - algGain η (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T
        ≤ onlineExternalRegret η (fun s => G.normGain lo W (G.mwProfile η lo W s) who) T :=
          fixedActionRegret_le_onlineExternalRegret η _ T s'
      _ ≤ Real.log (Fintype.card (G.Strategy who)) / η + (Real.exp η - 1 - η) / η * T :=
          mw_externalRegret_le hη (fun s a => G.normGain_mem_Icc hW hbd _ who a) T
      _ ≤ L / η + (Real.exp η - 1 - η) / η * T := by
          have h1 : Real.log (Fintype.card (G.Strategy who)) / η ≤ L / η :=
            (div_le_div_iff_of_pos_right hη).2 (hL who)
          linarith
  exact mul_le_mul_of_nonneg_left hbound hW.le

-- `[Fintype ι]` is load-bearing in the proof (via `mwSelfPlay_timeAverage_isεCCE`) but the
-- existential conclusion hides the witnessing time-average, so it does not appear in the type.
set_option linter.unusedFintypeInType false in
/-- **Existence of an ε-coarse correlated equilibrium via learning.** The time-average of
    multiplicative-weights self-play exhibits an ε-CCE for the explicit `ε` above. -/
theorem exists_mwSelfPlay_isεCCE {L : ℝ} (hη : 0 < η) (hW : 0 < W)
    (hbd : ∀ i ω, G.utility ω i ∈ Set.Icc (lo i) (lo i + W))
    (hL : ∀ i, Real.log (Fintype.card (G.Strategy i)) ≤ L)
    (T : ℕ) [NeZero T] :
    ∃ μ : PMF (Profile G),
      G.IsεCoarseCorrelatedEq (W * (L / η + (Real.exp η - 1 - η) / η * T) / T) μ :=
  ⟨_, G.mwSelfPlay_timeAverage_isεCCE η lo W hη hW hbd hL T⟩

-- `[Fintype ι]` is load-bearing in the proof but hidden by the existential conclusion.
set_option linter.unusedFintypeInType false in
/-- **Learning reaches arbitrarily good coarse correlated equilibria.** For every `ε > 0`, a small
    enough fixed learning rate (`η ≈ ε`) and a long enough horizon `T` make the time-average of
    multiplicative-weights self-play an `ε`-coarse correlated equilibrium. This is the convergence
    form of the capstone: decentralized no-regret learning reaches the set of coarse correlated
    equilibria to any precision. (Existence of *some* CCE is already known via Brouwer; the content
    here is that a concrete learning process realizes it, to any `ε`.) -/
theorem mwSelfPlay_exists_isεCCE_of_pos {L : ℝ} (hW : 0 < W)
    (hbd : ∀ i ω, G.utility ω i ∈ Set.Icc (lo i) (lo i + W))
    (hL : ∀ i, Real.log (Fintype.card (G.Strategy i)) ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : PMF (Profile G), G.IsεCoarseCorrelatedEq ε μ := by
  have hWpos : (0 : ℝ) < 2 * W := by linarith
  set η₀ : ℝ := min 1 (ε / (2 * W)) with hη₀
  have hηpos : 0 < η₀ := lt_min one_pos (by positivity)
  have hη1 : η₀ ≤ 1 := min_le_left _ _
  have hηε : η₀ ≤ ε / (2 * W) := min_le_right _ _
  have hηε' : η₀ * (2 * W) ≤ ε := (le_div_iff₀ hWpos).1 hηε
  obtain ⟨T', hT'⟩ := exists_nat_ge (2 * W * L / (η₀ * ε))
  haveI : NeZero (T' + 1) := ⟨Nat.succ_ne_zero _⟩
  have hn : (0 : ℝ) < ((T' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos T'
  refine ⟨G.timeAverage (fun t : Fin (T' + 1) => pmfPi (G.mwProfile η₀ lo W (t : ℕ))), ?_⟩
  refine IsεCoarseCorrelatedEq.mono G
    (G.mwSelfPlay_timeAverage_isεCCE η₀ lo W hηpos hW hbd hL (T' + 1)) ?_
  have hC : (Real.exp η₀ - 1 - η₀) / η₀ ≤ η₀ := by
    rw [div_le_iff₀ hηpos]
    have hh := exp_sub_one_sub_self_le_sq hηpos.le hη1
    rw [pow_two] at hh
    linarith
  have hnge : 2 * W * L ≤ ((T' + 1 : ℕ) : ℝ) * (η₀ * ε) := by
    have h1 : 2 * W * L / (η₀ * ε) ≤ ((T' + 1 : ℕ) : ℝ) :=
      le_trans hT' (by exact_mod_cast Nat.le_succ T')
    rwa [div_le_iff₀ (by positivity)] at h1
  have hterm1 : W * L / (η₀ * ((T' + 1 : ℕ) : ℝ)) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnge]
  have hterm2 : W * η₀ ≤ ε / 2 := by nlinarith [hηε']
  have hsplit :
      W * (L / η₀ + (Real.exp η₀ - 1 - η₀) / η₀ * ((T' + 1 : ℕ) : ℝ)) / ((T' + 1 : ℕ) : ℝ)
        = W * L / (η₀ * ((T' + 1 : ℕ) : ℝ)) + W * ((Real.exp η₀ - 1 - η₀) / η₀) := by
    have hηne : η₀ ≠ 0 := hηpos.ne'
    have hnne : ((T' + 1 : ℕ) : ℝ) ≠ 0 := hn.ne'
    field_simp
  rw [hsplit]
  have hWC : W * ((Real.exp η₀ - 1 - η₀) / η₀) ≤ W * η₀ :=
    mul_le_mul_of_nonneg_left hC hW.le
  linarith [hterm1, hterm2, hWC]

end KernelGame

end GameTheory

