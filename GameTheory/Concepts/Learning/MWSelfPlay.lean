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

end KernelGame

end GameTheory
