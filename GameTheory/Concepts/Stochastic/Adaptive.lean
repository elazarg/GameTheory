/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Discounted

/-!
# History-adapted continuation potentials

The deterministic Fink calendars use a potential depending only on calendar
time and the current state.  A genuinely adaptive vanishing-discount argument
must instead be able to update its continuation certificate from the realized
history.  This file supplies the corresponding Bellman telescope.

The potential and target below are dependent families on `G.Hist t`.  Thus
they may react to every past state and joint action, while the one-step
continuation is still evaluated under the actual behavior profile and state
transition kernel.  No Markov or stationarity assumption is used.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- A real continuation certificate allowed to depend on the entire history
at each decision epoch. -/
abbrev HistoryPotential (G : StochasticGame ι) :=
  (t : ℕ) → G.Hist t → ℝ

/-- Expected value of a history-dependent certificate at time `t`. -/
def expectedHistoryValue (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (V : G.HistoryPotential) (t : ℕ) : ℝ :=
  expect (G.histDist σ s₀ t) (V t)

/-- One-step continuation expectation of a history-dependent potential. -/
def historyContinuationEU (G : StochasticGame ι) [Fintype ι]
    (σ : G.BehaviorProfile) (V : G.HistoryPotential)
    {t : ℕ} (h : G.Hist t) : ℝ :=
  expect (G.stageActionDist σ h) fun a =>
    expect (G.transition h.2 a) fun s' =>
      V (t + 1) (Fin.snoc h.1 (h.2, a), s')

/-- The expected successor potential is the expectation of its one-step
history continuation at the preceding epoch. -/
theorem expectedHistoryValue_succ
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (V : G.HistoryPotential) (t : ℕ) :
    G.expectedHistoryValue σ s₀ V (t + 1) =
      expect (G.histDist σ s₀ t) (fun h =>
        G.historyContinuationEU σ V h) := by
  unfold expectedHistoryValue historyContinuationEU
  rw [G.histDist_succ, expect_bind]
  apply congrArg (expect (G.histDist σ s₀ t))
  funext h
  rw [expect_bind]
  apply congrArg (expect (G.stageActionDist σ h))
  funext a
  rw [expect_bind]
  apply congrArg (expect (G.transition h.2 a))
  funext s'
  rw [expect_pure]

/-- Finite-horizon Bellman telescope for targets and potentials that may
adapt to the full realized history. -/
theorem finitePayoff_telescope_of_history_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (z v : G.HistoryPotential) (e : ℕ → ℝ)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h + v t h ≤ G.stageEUAt σ h who +
        G.historyContinuationEU σ v h + e t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, G.expectedHistoryValue σ s₀ z t) +
        G.expectedHistoryValue σ s₀ v 0 ≤
      (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) +
        G.expectedHistoryValue σ s₀ v T +
          ∑ t ∈ Finset.range T, e t := by
  let Z : ℕ → ℝ := fun t => G.expectedHistoryValue σ s₀ z t
  let V : ℕ → ℝ := fun t => G.expectedHistoryValue σ s₀ v t
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, Z t + V t ≤ r t + V (t + 1) + e t := by
    intro t
    calc
      Z t + V t = expect (G.histDist σ s₀ t) (fun h =>
          z t h + v t h) := by
        rw [expect_add]
        rfl
      _ ≤ expect (G.histDist σ s₀ t) (fun h =>
          G.stageEUAt σ h who +
            G.historyContinuationEU σ v h + e t) :=
        expect_mono _ _ _ (hbellman t)
      _ = r t + V (t + 1) + e t := by
        rw [expect_add, expect_add, expect_const,
          ← G.expectedHistoryValue_succ]
        rfl
  change (∑ t ∈ Finset.range T, Z t) + V 0 ≤
    (∑ t ∈ Finset.range T, r t) + V T +
      ∑ t ∈ Finset.range T, e t
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      linarith [hstep T]

/-- Dual history-adapted Bellman telescope. -/
theorem finitePayoff_telescope_of_history_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (z v : G.HistoryPotential) (e : ℕ → ℝ)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who + G.historyContinuationEU σ v h ≤
        z t h + v t h + e t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who) +
        G.expectedHistoryValue σ s₀ v T ≤
      (∑ t ∈ Finset.range T, G.expectedHistoryValue σ s₀ z t) +
        G.expectedHistoryValue σ s₀ v 0 +
          ∑ t ∈ Finset.range T, e t := by
  let Z : ℕ → ℝ := fun t => G.expectedHistoryValue σ s₀ z t
  let V : ℕ → ℝ := fun t => G.expectedHistoryValue σ s₀ v t
  let r : ℕ → ℝ := fun t => G.expectedStagePayoff σ s₀ t who
  have hstep : ∀ t, r t + V (t + 1) ≤ Z t + V t + e t := by
    intro t
    calc
      r t + V (t + 1) = expect (G.histDist σ s₀ t) (fun h =>
          G.stageEUAt σ h who + G.historyContinuationEU σ v h) := by
        rw [expect_add, ← G.expectedHistoryValue_succ]
        rfl
      _ ≤ expect (G.histDist σ s₀ t) (fun h =>
          z t h + v t h + e t) :=
        expect_mono _ _ _ (hbellman t)
      _ = Z t + V t + e t := by
        rw [expect_add, expect_add, expect_const]
        rfl
  change (∑ t ∈ Finset.range T, r t) + V T ≤
    (∑ t ∈ Finset.range T, Z t) + V 0 +
      ∑ t ∈ Finset.range T, e t
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      linarith [hstep T]

/-- Lower finite-average guarantee from a history-adapted Bellman
certificate.  Only the initial/terminal potential bounds and the average
accumulated error survive the telescope. -/
theorem finiteAveragePayoff_ge_of_history_bellman_le
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (z v : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ}
    {c C0 CT : ℝ} (hz : ∀ t (h : G.Hist t), c ≤ z t h)
    (hv0 : ∀ h : G.Hist 0, |v 0 h| ≤ C0)
    (hvT : ∀ h : G.Hist T, |v T h| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      z t h + v t h ≤ G.stageEUAt σ h who +
        G.historyContinuationEU σ v h + e t)
    (hT : 0 < T) :
    c - (C0 + CT) / (T : ℝ) -
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤
      G.finiteAveragePayoff s₀ T σ who := by
  have htel := G.finitePayoff_telescope_of_history_bellman_le
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, c ≤ G.expectedHistoryValue σ s₀ z t := by
    intro t
    calc
      c = expect (G.histDist σ s₀ t) (fun _ => c) :=
        (expect_const _ _).symm
      _ ≤ expect (G.histDist σ s₀ t) (z t) :=
        expect_mono _ _ _ (hz t)
  have hsumZ : (T : ℝ) * c ≤
      ∑ t ∈ Finset.range T, G.expectedHistoryValue σ s₀ z t := by
    calc
      (T : ℝ) * c = ∑ _t ∈ Finset.range T, c := by simp
      _ ≤ ∑ t ∈ Finset.range T,
          G.expectedHistoryValue σ s₀ z t :=
        Finset.sum_le_sum fun t _ => hZ t
  have hV0 : -C0 ≤ G.expectedHistoryValue σ s₀ v 0 := by
    exact neg_le_of_abs_le (abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (v 0) hv0)
  have hVT : G.expectedHistoryValue σ s₀ v T ≤ CT := by
    exact le_of_abs_le (abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (v T) hvT)
  have hraw : (T : ℝ) * c - C0 - CT -
      (∑ t ∈ Finset.range T, e t) ≤
        ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show c - (C0 + CT) / (T : ℝ) -
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c - C0 - CT - (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp [ne_of_gt hTreal]
    ring]
  simpa only [div_eq_inv_mul] using
    (div_le_div_iff_of_pos_right hTreal).2 hraw

/-- Upper finite-average guarantee from a history-adapted Bellman
certificate. -/
theorem finiteAveragePayoff_le_of_history_bellman_ge
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι)
    (z v : G.HistoryPotential) (e : ℕ → ℝ) {T : ℕ}
    {c C0 CT : ℝ} (hz : ∀ t (h : G.Hist t), z t h ≤ c)
    (hv0 : ∀ h : G.Hist 0, |v 0 h| ≤ C0)
    (hvT : ∀ h : G.Hist T, |v T h| ≤ CT)
    (hbellman : ∀ (t : ℕ) (h : G.Hist t),
      G.stageEUAt σ h who + G.historyContinuationEU σ v h ≤
        z t h + v t h + e t)
    (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T σ who ≤
      c + (C0 + CT) / (T : ℝ) +
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t := by
  have htel := G.finitePayoff_telescope_of_history_bellman_ge
    σ s₀ who z v e hbellman T
  have hZ : ∀ t, G.expectedHistoryValue σ s₀ z t ≤ c := by
    intro t
    calc
      expect (G.histDist σ s₀ t) (z t) ≤
          expect (G.histDist σ s₀ t) (fun _ => c) :=
        expect_mono _ _ _ (hz t)
      _ = c := expect_const _ _
  have hsumZ : (∑ t ∈ Finset.range T,
      G.expectedHistoryValue σ s₀ z t) ≤ (T : ℝ) * c := by
    calc
      (∑ t ∈ Finset.range T, G.expectedHistoryValue σ s₀ z t) ≤
          ∑ _t ∈ Finset.range T, c :=
        Finset.sum_le_sum fun t _ => hZ t
      _ = (T : ℝ) * c := by simp
  have hV0 : G.expectedHistoryValue σ s₀ v 0 ≤ C0 := by
    exact le_of_abs_le (abs_expect_le_of_abs_le
      (G.histDist σ s₀ 0) (v 0) hv0)
  have hVT : -CT ≤ G.expectedHistoryValue σ s₀ v T := by
    exact neg_le_of_abs_le (abs_expect_le_of_abs_le
      (G.histDist σ s₀ T) (v T) hvT)
  have hraw : (∑ t ∈ Finset.range T,
      G.expectedStagePayoff σ s₀ t who) ≤
        (T : ℝ) * c + C0 + CT + ∑ t ∈ Finset.range T, e t := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show c + (C0 + CT) / (T : ℝ) +
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, e t) =
      ((T : ℝ) * c + C0 + CT + (∑ t ∈ Finset.range T, e t)) /
        (T : ℝ) by
    field_simp [ne_of_gt hTreal]
    ring]
  simpa only [div_eq_inv_mul] using
    (div_le_div_iff_of_pos_right hTreal).2 hraw

end StochasticGame
end GameTheory
