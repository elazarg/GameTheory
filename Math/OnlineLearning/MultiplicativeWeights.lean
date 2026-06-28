/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multiplicative weights: a no-regret online learning algorithm

The multiplicative-weights (Hedge) algorithm and its sublinear external-regret guarantee,
stated game-free over a finite action set `A`. This is the explicit no-regret rule that makes
the no-regret ⇒ coarse correlated equilibrium reduction non-vacuous and constructive.

At each round `t` the learner plays each action with probability proportional to
`exp (η · cumulative-gain)`. The external regret — the gap between the best fixed action in
hindsight and the algorithm's expected gain — is bounded by `log |A| / η + (eᵑ−1−η)/η · T`,
which is `O(√(T log |A|))` for the tuning `η ≈ √(log|A| / T)`: sublinear in `T`.

## Main definitions

* `Math.OnlineLearning.mwDist` — the multiplicative-weights distribution at round `t`
* `Math.OnlineLearning.onlineExternalRegret` — best fixed action minus algorithm's expected gain

## Main results

* `Math.OnlineLearning.mw_externalRegret_le` — the sublinear external-regret bound
-/

namespace Math.OnlineLearning

open Math.Probability

variable {A : Type}

/-- Cumulative gain of action `a` over the first `t` rounds. -/
def cumGain (g : ℕ → A → ℝ) (t : ℕ) (a : A) : ℝ := ∑ s ∈ Finset.range t, g s a

@[simp] theorem cumGain_zero (g : ℕ → A → ℝ) (a : A) : cumGain g 0 a = 0 := by
  simp [cumGain]

theorem cumGain_succ (g : ℕ → A → ℝ) (t : ℕ) (a : A) :
    cumGain g (t + 1) a = cumGain g t a + g t a := by
  simp [cumGain, Finset.sum_range_succ]

/-- The unnormalized multiplicative weight of action `a` at round `t`. -/
noncomputable def mwWeight (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) (a : A) : ℝ :=
  Real.exp (η * cumGain g t a)

theorem mwWeight_pos (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) (a : A) : 0 < mwWeight η g t a :=
  Real.exp_pos _

variable [Fintype A] [Nonempty A]

/-- The normalizing constant (partition function) at round `t`. -/
noncomputable def mwDenom (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) : ℝ :=
  ∑ a, mwWeight η g t a

theorem mwDenom_pos (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) : 0 < mwDenom η g t :=
  Finset.sum_pos (fun a _ => mwWeight_pos η g t a) Finset.univ_nonempty

omit [Nonempty A] in
theorem mwDenom_zero (η : ℝ) (g : ℕ → A → ℝ) : mwDenom η g 0 = Fintype.card A := by
  simp [mwDenom, mwWeight]

/-- The multiplicative-weights distribution at round `t`: probability proportional to
    `exp (η · cumulative gain)`. -/
noncomputable def mwDist (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (mwWeight η g t a) / ENNReal.ofReal (mwDenom η g t))
    (by
      have hsum : ∑ a, ENNReal.ofReal (mwWeight η g t a) = ENNReal.ofReal (mwDenom η g t) := by
        rw [mwDenom, ENNReal.ofReal_sum_of_nonneg (fun a _ => (mwWeight_pos η g t a).le)]
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul, hsum]
      exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (mwDenom_pos η g t)).ne'
        ENNReal.ofReal_ne_top)

/-- The expected value under `mwDist` is the weight-average. -/
theorem expect_mwDist (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) (f : A → ℝ) :
    expect (mwDist η g t) f = (∑ a, mwWeight η g t a * f a) / mwDenom η g t := by
  rw [expect_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mwDist, PMF.ofFintype_apply, ENNReal.toReal_div]
  rw [ENNReal.toReal_ofReal (mwWeight_pos η g t a).le, ENNReal.toReal_ofReal (mwDenom_pos η g t).le]
  ring

/-- The algorithm's expected gain accumulated over the first `T` rounds. -/
noncomputable def algGain (η : ℝ) (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, expect (mwDist η g t) (g t)

theorem algGain_succ (η : ℝ) (g : ℕ → A → ℝ) (T : ℕ) :
    algGain η g (T + 1) = algGain η g T + expect (mwDist η g T) (g T) := by
  simp [algGain, Finset.sum_range_succ]

/-- The best fixed action's cumulative gain over the first `T` rounds. -/
noncomputable def bestGain (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => cumGain g T a)

/-- External regret of multiplicative weights: best fixed action minus the algorithm's gain. -/
noncomputable def onlineExternalRegret (η : ℝ) (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  bestGain g T - algGain η g T

/-- Per-step convexity bound: for `x ∈ [0,1]` and any `η`, `exp (η x) ≤ 1 + x (eᵑ − 1)`. -/
theorem exp_mul_le_of_mem_Icc {η x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (η * x) ≤ 1 + x * (Real.exp η - 1) := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ η)
    (by linarith [hx.2] : (0:ℝ) ≤ 1 - x) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, Real.exp_zero, mul_one, zero_add] at hconv
  have key : 1 + x * (Real.exp η - 1) = 1 - x + x * Real.exp η := by ring
  rw [mul_comm η x, key]
  exact hconv

/-- Potential recursion: `Φ(t+1) ≤ Φ(t) · exp((eᵑ−1) · E_t[g_t])`. -/
theorem mwDenom_succ_le (η : ℝ) {g : ℕ → A → ℝ}
    (hg : ∀ s a, g s a ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    mwDenom η g (t + 1)
      ≤ mwDenom η g t * Real.exp ((Real.exp η - 1) * expect (mwDist η g t) (g t)) := by
  have hstep : mwDenom η g (t + 1)
      ≤ mwDenom η g t + (Real.exp η - 1) * (∑ a, mwWeight η g t a * g t a) := by
    rw [mwDenom, mwDenom, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hw : mwWeight η g (t + 1) a = mwWeight η g t a * Real.exp (η * g t a) := by
      rw [mwWeight, mwWeight, cumGain_succ, mul_add, Real.exp_add]
    rw [hw]
    nlinarith [mwWeight_pos η g t a, exp_mul_le_of_mem_Icc (η := η) (hg t a)]
  have hEt : (∑ a, mwWeight η g t a * g t a) = mwDenom η g t * expect (mwDist η g t) (g t) := by
    rw [expect_mwDist, mul_div_cancel₀ _ (mwDenom_pos η g t).ne']
  rw [hEt] at hstep
  calc mwDenom η g (t + 1)
      ≤ mwDenom η g t + (Real.exp η - 1) * (mwDenom η g t * expect (mwDist η g t) (g t)) := hstep
    _ = mwDenom η g t * (1 + (Real.exp η - 1) * expect (mwDist η g t) (g t)) := by ring
    _ ≤ mwDenom η g t * Real.exp ((Real.exp η - 1) * expect (mwDist η g t) (g t)) := by
        apply mul_le_mul_of_nonneg_left _ (mwDenom_pos η g t).le
        linarith [Real.add_one_le_exp ((Real.exp η - 1) * expect (mwDist η g t) (g t))]

/-- Telescoped potential bound: `Φ(T) ≤ Φ(0) · exp((eᵑ−1) · algGain)`. -/
theorem mwDenom_le (η : ℝ) {g : ℕ → A → ℝ}
    (hg : ∀ s a, g s a ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    mwDenom η g T ≤ (Fintype.card A) * Real.exp ((Real.exp η - 1) * algGain η g T) := by
  induction T with
  | zero => simp [mwDenom_zero, algGain, Real.exp_zero]
  | succ T ih =>
    calc mwDenom η g (T + 1)
        ≤ mwDenom η g T * Real.exp ((Real.exp η - 1) * expect (mwDist η g T) (g T)) :=
          mwDenom_succ_le η hg T
      _ ≤ ((Fintype.card A) * Real.exp ((Real.exp η - 1) * algGain η g T))
            * Real.exp ((Real.exp η - 1) * expect (mwDist η g T) (g T)) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = (Fintype.card A) * Real.exp ((Real.exp η - 1) * algGain η g (T + 1)) := by
          rw [algGain_succ, mul_add, Real.exp_add]; ring

/-- The partition function lower-bounds the best action's exponentiated gain. -/
theorem exp_bestGain_le_mwDenom (η : ℝ) (g : ℕ → A → ℝ) (T : ℕ) :
    Real.exp (η * bestGain g T) ≤ mwDenom η g T := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun a => cumGain g T a)
  have heq : Real.exp (η * bestGain g T) = mwWeight η g T a := by
    rw [bestGain, ha, mwWeight]
  rw [heq]
  exact Finset.single_le_sum (fun b _ => (mwWeight_pos η g T b).le) (Finset.mem_univ a)

/-- **Multiplicative-weights external-regret bound.** With gains in `[0,1]` and learning rate
    `η > 0`, the external regret over `T` rounds is at most `log |A| / η + (eᵑ−1−η)/η · T`. For
    `η ≈ √(log |A| / T)` this is `O(√(T log |A|))` — sublinear, so the per-round regret → 0. -/
theorem mw_externalRegret_le {η : ℝ} (hη : 0 < η) {g : ℕ → A → ℝ}
    (hg : ∀ s a, g s a ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    onlineExternalRegret η g T
      ≤ Real.log (Fintype.card A) / η + (Real.exp η - 1 - η) / η * T := by
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hcomb : Real.exp (η * bestGain g T)
      ≤ (Fintype.card A) * Real.exp ((Real.exp η - 1) * algGain η g T) :=
    le_trans (exp_bestGain_le_mwDenom η g T) (mwDenom_le η hg T)
  -- take logs (both sides positive)
  have hlog : η * bestGain g T
      ≤ Real.log (Fintype.card A) + (Real.exp η - 1) * algGain η g T := by
    have h1 := Real.log_le_log (Real.exp_pos _) hcomb
    rwa [Real.log_exp, Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  -- the algorithm's gain is at most T (each expected gain ≤ 1)
  have halg : algGain η g T ≤ T := by
    rw [algGain]
    calc ∑ t ∈ Finset.range T, expect (mwDist η g t) (g t)
        ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ =>
            le_of_le_of_eq (expect_mono _ _ _ (fun a => (hg t a).2)) (expect_const _ 1))
      _ = T := by simp
  -- divide the log inequality by η
  have hbest : bestGain g T
      ≤ Real.log (Fintype.card A) / η + (Real.exp η - 1) / η * algGain η g T := by
    have key : Real.log (Fintype.card A) / η + (Real.exp η - 1) / η * algGain η g T
        = (Real.log (Fintype.card A) + (Real.exp η - 1) * algGain η g T) / η := by ring
    rw [key, le_div_iff₀ hη]
    linarith [hlog]
  -- assemble
  have hcoeff : 0 ≤ (Real.exp η - 1 - η) / η :=
    div_nonneg (by linarith [Real.add_one_le_exp η]) hη.le
  have hmul := mul_le_mul_of_nonneg_left halg hcoeff
  have hηne : η ≠ 0 := hη.ne'
  have hsplit : (Real.exp η - 1) / η * algGain η g T
      = algGain η g T + (Real.exp η - 1 - η) / η * algGain η g T := by
    field_simp
    ring
  rw [onlineExternalRegret]
  linarith [hbest, hmul, hsplit]

/-- The exponential-weights distribution induced by a cumulative-score vector: probability of
    action `a` proportional to `exp (η · score a)`. This is the score-based view of `mwDist`,
    used to define multiplicative-weights self-play without referring to a gain sequence. -/
noncomputable def expWeights (η : ℝ) (score : A → ℝ) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (Real.exp (η * score a))
      / ENNReal.ofReal (∑ b, Real.exp (η * score b)))
    (by
      have hpos : 0 < ∑ b, Real.exp (η * score b) :=
        Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
      have hsum : ∑ a, ENNReal.ofReal (Real.exp (η * score a))
          = ENNReal.ofReal (∑ b, Real.exp (η * score b)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun a _ => (Real.exp_pos _).le)).symm
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul, hsum]
      exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top)

/-- `mwDist` is exponential weighting applied to the cumulative-gain score. -/
theorem mwDist_eq_expWeights (η : ℝ) (g : ℕ → A → ℝ) (t : ℕ) :
    mwDist η g t = expWeights η (fun a => cumGain g t a) := rfl

/-- Any single fixed action's regret is bounded by the external regret: the gap between one
    action's cumulative gain and the algorithm's gain is at most the best action's gap. -/
theorem fixedActionRegret_le_onlineExternalRegret (η : ℝ) (g : ℕ → A → ℝ) (T : ℕ) (a : A) :
    cumGain g T a - algGain η g T ≤ onlineExternalRegret η g T := by
  have hle : cumGain g T a ≤ bestGain g T :=
    Finset.le_sup' (fun a => cumGain g T a) (Finset.mem_univ a)
  rw [onlineExternalRegret]
  linarith

end Math.OnlineLearning
