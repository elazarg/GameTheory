/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.Examples.BigMatch.Fink
import UniformEquilibrium.Examples.BigMatch.Uniform
import Mathlib.Analysis.PSeries

/-!
# Big-Match test for the linear running-deficit index

The linear index `rowDeficitIndex` is not a viable universal
Mertens–Neyman constructor. On the Big-Match history where the maximizer
continues and the minimizer always plays Right, its denominator grows only
linearly. Every discounted stationary Bellman equilibrium then stops with a
harmonic-order probability. The resulting hazards are not summable, whereas
the Blackwell–Ferguson strategy uses a square-summable `1 / D²` hazard on
this path.

This module records the analytic obstruction before any crossing theorem is
attempted for that index family.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Math.Probability
open Filter

/-- The live joint action in which the maximizer continues and the minimizer
plays Right. -/
def rightContinueAct : game.JointAct := fun who => who

/-- The length-`t` live history consisting only of `rightContinueAct`. -/
def rightContinueHist (t : ℕ) : game.Hist t :=
  (fun _ => (.live, rightContinueAct), .live)

@[simp] theorem totalPayoff_rightContinueHist (t : ℕ) :
    game.totalPayoff false (rightContinueHist t) = t := by
  simp [StochasticGame.totalPayoff, rightContinueHist, rightContinueAct,
    payoff, reward]

/-- Boolean-player form of the realized row surplus used by the linear
running-deficit construction. -/
def boolRowRunningSurplus (w : ℝ) {t : ℕ} (h : game.Hist t) : ℝ :=
  game.totalPayoff false h - t * w

@[simp] theorem rowRunningSurplus_rightContinueHist (t : ℕ) :
    boolRowRunningSurplus (1 / 2) (rightContinueHist t) = (t : ℝ) / 2 := by
  rw [boolRowRunningSurplus]
  simp
  ring

/-- Boolean-player form of the linearly clamped denominator. -/
def boolRowIndexDenom (N : ℕ) (w : ℝ) {t : ℕ} (h : game.Hist t) : ℝ :=
  max (N : ℝ) ((t : ℝ) + N + boolRowRunningSurplus w h)

/-- Along the all-Right live path, the proposed denominator is
`N + 3t/2`; its calendar term dominates rather than tracking the signed
Right-minus-Left excess used by Blackwell–Ferguson. -/
theorem rowIndexDenom_rightContinueHist (N t : ℕ) :
    boolRowIndexDenom N (1 / 2) (rightContinueHist t) =
      (N : ℝ) + 3 * (t : ℝ) / 2 := by
  unfold boolRowIndexDenom
  rw [rowRunningSurplus_rightContinueHist]
  rw [max_eq_right]
  · ring
  · have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith

/-- Boolean-player form of the linear running-deficit index. -/
def boolRowDeficitIndex (δ : ℝ) (N : ℕ) (w : ℝ) :
    (t : ℕ) → game.Hist t → ℝ :=
  fun _ h => δ / boolRowIndexDenom N w h

@[simp] theorem rowDeficitIndex_rightContinueHist (δ : ℝ) (N t : ℕ) :
    boolRowDeficitIndex δ N (1 / 2) t (rightContinueHist t) =
      δ / ((N : ℝ) + 3 * (t : ℝ) / 2) := by
  rw [boolRowDeficitIndex, rowIndexDenom_rightContinueHist]

/-- The stop hazard forced by a discounted Bellman equilibrium when the
linear deficit index is evaluated on the all-Right live path. -/
def rightContinueDeficitHazard (δ : ℝ) (N t : ℕ) : ℝ :=
  δ / ((N : ℝ) + 3 * (t : ℝ) / 2 + δ)

/-- Feeding the linear deficit index into any discounted stationary Bellman
equilibrium forces exactly `rightContinueDeficitHazard` as the stopping
probability on the all-Right live history. -/
theorem live_stopProbability_at_boolRowDeficitIndex
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) (hδN : δ < N) (t : ℕ)
    {x : game.StationaryMixedProfile} {V : State → Payoff Player}
    (hF : game.IsDiscountedStationaryBellmanEq
      (1 - boolRowDeficitIndex δ N (1 / 2) t (rightContinueHist t)) x V) :
    ((x .live false) true).toReal = rightContinueDeficitHazard δ N t := by
  let D : ℝ := (N : ℝ) + 3 * (t : ℝ) / 2
  have hDpos : 0 < D := by
    dsimp [D]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  let lam : ℝ := boolRowDeficitIndex δ N (1 / 2) t (rightContinueHist t)
  have hlam : lam = δ / D := by
    dsimp [lam, D]
    exact rowDeficitIndex_rightContinueHist δ N t
  have hlam0 : 0 < lam := by rw [hlam]; exact div_pos hδ hDpos
  have hDgeN : (N : ℝ) ≤ D := by
    dsimp [D]
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  have hδD : δ < D := lt_of_lt_of_le (by exact_mod_cast hδN) hDgeN
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hDpos]
    exact hδD
  have hstop := live_maximizer_stopProbability_eq
    (β := 1 - lam) (by linarith) (by linarith) hF
  have hstop' : ((x .live false) true).toReal = lam / (1 + lam) := by
    convert hstop using 1
    ring
  rw [hstop', hlam]
  dsimp [rightContinueDeficitHazard, D]
  field_simp [hDpos.ne']

/-- The hazards produced on the all-Right path have harmonic order and are
therefore not summable. -/
theorem not_summable_rightContinueDeficitHazard
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ¬ Summable (fun t => rightContinueDeficitHazard δ N t) := by
  let A : ℝ := (N : ℝ) + δ + 3 / 2
  let c : ℝ := δ / A
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hc : 0 < c := div_pos hδ hA
  have hminorize : ∀ t : ℕ,
      c * (1 / ((t : ℝ) + 1)) ≤ rightContinueDeficitHazard δ N t := by
    intro t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hNcast : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hden : 0 < (N : ℝ) + 3 * (t : ℝ) / 2 + δ := by positivity
    have hprod : (N : ℝ) + 3 * (t : ℝ) / 2 + δ ≤ A * ((t : ℝ) + 1) := by
      dsimp [A]
      nlinarith
    calc
      c * (1 / ((t : ℝ) + 1)) =
          δ / (A * ((t : ℝ) + 1)) := by
            dsimp [c]
            field_simp
      _ ≤ δ / ((N : ℝ) + 3 * (t : ℝ) / 2 + δ) := by
        rw [div_le_div_iff₀ (mul_pos hA (by positivity)) hden]
        exact mul_le_mul_of_nonneg_left hprod hδ.le
  intro hs
  have hscaled : Summable (fun t : ℕ => c * (1 / ((t : ℝ) + 1))) :=
    Summable.of_nonneg_of_le
      (fun t => mul_nonneg hc.le (by positivity))
      hminorize hs
  have hharmonic : Summable (fun t : ℕ => 1 / ((t : ℝ) + 1)) :=
    (summable_mul_left_iff hc.ne').mp hscaled
  have hnonneg : ∀ t : ℕ, 0 ≤ 1 / ((t : ℝ) + 1) := fun _ => by positivity
  have hnot : ¬ Summable (fun t : ℕ => 1 / ((t : ℝ) + 1)) :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).2
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact hnot hharmonic

theorem rightContinueDeficitHazard_nonneg
    {δ : ℝ} (hδ : 0 < δ) (N t : ℕ) :
    0 ≤ rightContinueDeficitHazard δ N t := by
  unfold rightContinueDeficitHazard
  positivity

theorem rightContinueDeficitHazard_lt_one
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) (t : ℕ) :
    rightContinueDeficitHazard δ N t < 1 := by
  unfold rightContinueDeficitHazard
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rw [div_lt_one]
  · linarith
  · positivity

/-- A time/state realization of the stopping hazards forced by the linear
index on the all-Right live path. The minimizer component is immaterial:
the no-go theorem below replaces it by the pure all-Right deviation. -/
def rightContinueDeficitProfile
    (δ : ℝ) (N : ℕ) (hδ : 0 < δ) (hN : 1 ≤ N) :
    TimeStateMixedProfile :=
  fun t _s who =>
    if who then PMF.pure true
    else
      coinPMF (rightContinueDeficitHazard δ N t)
        (rightContinueDeficitHazard_nonneg hδ N t)
        (rightContinueDeficitHazard_lt_one hδ hN t).le

@[simp] theorem stopProbability_rightContinueDeficitProfile
    (δ : ℝ) (N : ℕ) (hδ : 0 < δ) (hN : 1 ≤ N) (t : ℕ) :
    stopProbability (rightContinueDeficitProfile δ N hδ hN) t =
      rightContinueDeficitHazard δ N t := by
  unfold stopProbability rightContinueDeficitProfile
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact coinPMF_apply_true_toReal _ _ _

/-- The live probability of the forced-hazard realization tends to zero.
Equivalently, the linear-index player eventually makes the losing stop
against the all-Right response with probability one. -/
theorem tendsto_liveProbability_rightContinueDeficitHazard
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto
      (MarkovScalar.liveProbability (rightContinueDeficitHazard δ N))
      atTop (nhds 0) := by
  have hbranch := MarkovScalar.summable_or_tendsto_liveProbability_zero
    (rightContinueDeficitHazard δ N)
    (rightContinueDeficitHazard_nonneg hδ N)
    (fun t => (rightContinueDeficitHazard_lt_one hδ hN t).le)
  exact hbranch.resolve_left
    (not_summable_rightContinueDeficitHazard hδ N)

/-- The actual finite-horizon payoff of the forced-hazard realization
against the pure all-Right minimizer converges to zero. Thus it cannot
secure the Big Match value `1/2`. -/
theorem tendsto_payoff_rightContinueDeficitProfile_allRight
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto
      (fun T =>
        game.finiteAveragePayoff .live T
          (Function.update
            (timeStateBehaviorProfile
              (rightContinueDeficitProfile δ N hδ hN))
            true allRightMinimizer)
          false)
      atTop (nhds 0) := by
  have havg := MarkovScalar.tendsto_allRightAverage_zero
    (rightContinueDeficitHazard δ N)
    (tendsto_liveProbability_rightContinueDeficitHazard hδ hN)
  convert havg using 1
  funext T
  rw [finiteAveragePayoff_update_allRightMinimizer]
  unfold MarkovScalar.allRightAverage MarkovScalar.allRightStagePayoff
    MarkovScalar.liveProbability
  simp_rw [stopProbability_rightContinueDeficitProfile]

/-- The forced-hazard realization fails even the fixed `1/4` lower bound
against all-Right, so it cannot be a uniform `1/4`-optimal strategy for the
Big Match value `1/2`. -/
theorem not_eventually_one_quarter_le_payoff_rightContinueDeficitProfile
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 ≤ N) :
    ¬ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      (1 / 4 : ℝ) ≤
        game.finiteAveragePayoff .live T
          (Function.update
            (timeStateBehaviorProfile
              (rightContinueDeficitProfile δ N hδ hN))
            true allRightMinimizer)
          false := by
  rintro ⟨T₀, hT₀⟩
  have hlim :=
    tendsto_payoff_rightContinueDeficitProfile_allRight hδ hN
  obtain ⟨Tsmall, hsmall⟩ :=
    (Metric.tendsto_atTop.mp hlim) (1 / 4) (by norm_num)
  let T := max T₀ Tsmall
  have hlower := hT₀ T (le_max_left _ _)
  have hupper := hsmall T (le_max_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)] at hupper
  linarith

end BigMatch
end StochasticGame
end GameTheory
