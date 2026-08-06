/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformAsymptoticPayoffEquivalence
import GameTheory.Concepts.Stochastic.Discounted

/-!
# Expected-potential shaping preserves uniform-equilibrium payoffs

Add to player `i`'s stage payoff the expected one-step coboundary

`E[Fᵢ(s')] - Fᵢ(s)`.

For every behavior profile, prescribed or deviating, the expected cumulative
change telescopes to `E[Fᵢ(s_T)] - Fᵢ(s₀)`.  A bounded potential therefore
changes every `T`-stage average by `O(1 / T)`, uniformly over all behavior
profiles.  The vanishing-gap equivalence then shows that the complete set of
uniform-equilibrium payoff vectors is unchanged.

This is a game-theoretic gauge invariance theorem.  Any genuine asymptotic
obstruction must be invariant under bounded expected coboundaries.
-/

noncomputable section

open Filter
open Math.Probability

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- Stage payoff after expected-potential shaping. -/
def expectedPotentialShapedReward
    (G : StochasticGame ι) (F : ι → G.State → ℝ) :
    G.State → G.JointAct → ι → ℝ :=
  fun s a who =>
    G.stagePayoff s a who + expect (G.transition s a) (F who) - F who s

/-- The fixed-skeleton game obtained by expected-potential shaping. -/
def withExpectedPotentialShaping
    (G : StochasticGame ι) (F : ι → G.State → ℝ) : StochasticGame ι :=
  G.withStagePayoff (G.expectedPotentialShapedReward F)

/-- One-stage expected payoff after shaping: original expected payoff plus the
expected next potential minus the current potential. -/
theorem stageEUAt_withExpectedPotentialShaping
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) (σ : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (who : ι) :
    (G.withExpectedPotentialShaping F).stageEUAt σ h who =
      G.stageEUAt σ h who +
        expect (G.stageActionDist σ h) (fun a =>
          expect (G.transition h.2 a) (F who)) -
        F who h.2 := by
  unfold stageEUAt withExpectedPotentialShaping expectedPotentialShapedReward
  rw [stageActionDist_withStagePayoff]
  rw [expect_sub, expect_add, expect_const]

/-- Expected payoff of stage `t` after shaping. -/
theorem expectedStagePayoff_withExpectedPotentialShaping
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) (σ : G.BehaviorProfile)
    (s₀ : G.State) (t : ℕ) (who : ι) :
    (G.withExpectedPotentialShaping F).expectedStagePayoff σ s₀ t who =
      G.expectedStagePayoff σ s₀ t who +
        G.expectedStateValue σ s₀ (t + 1) (F who) -
        G.expectedStateValue σ s₀ t (F who) := by
  unfold expectedStagePayoff
  rw [histDist_withStagePayoff]
  simp_rw [stageEUAt_withExpectedPotentialShaping]
  rw [expect_sub, expect_add]
  rw [← G.expectedStateValue_succ σ s₀ t (F who)]
  rfl

/-- Exact expected-total-payoff telescope for potential shaping. -/
theorem expect_totalPayoff_withExpectedPotentialShaping
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) (σ : G.BehaviorProfile)
    (s₀ : G.State) (who : ι) (T : ℕ) :
    expect ((G.withExpectedPotentialShaping F).histDist σ s₀ T)
        (fun h => (G.withExpectedPotentialShaping F).totalPayoff who h) =
      expect (G.histDist σ s₀ T) (fun h => G.totalPayoff who h) +
        G.expectedStateValue σ s₀ T (F who) - F who s₀ := by
  induction T with
  | zero =>
      simp [withExpectedPotentialShaping]
  | succ T ih =>
      rw [(G.withExpectedPotentialShaping F).expect_totalPayoff_succ,
        G.expect_totalPayoff_succ, ih,
        G.expectedStagePayoff_withExpectedPotentialShaping F]
      ring

/-- Exact finite-average payoff difference under potential shaping. -/
theorem finiteAveragePayoff_withExpectedPotentialShaping_sub
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) (σ : G.BehaviorProfile)
    (s₀ : G.State) (T : ℕ) (who : ι) :
    (G.withExpectedPotentialShaping F).finiteAveragePayoff s₀ T σ who -
        G.finiteAveragePayoff s₀ T σ who =
      (T : ℝ)⁻¹ *
        (G.expectedStateValue σ s₀ T (F who) - F who s₀) := by
  unfold finiteAveragePayoff
  rw [G.expect_totalPayoff_withExpectedPotentialShaping F]
  ring

/-- A bounded potential gives the sharp `2C / T` finite-average gap. -/
theorem abs_finiteAveragePayoff_withExpectedPotentialShaping_sub_le
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) {C : ℝ}
    (hF : ∀ who s, |F who s| ≤ C)
    (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (who : ι) :
    |(G.withExpectedPotentialShaping F).finiteAveragePayoff s₀ T σ who -
        G.finiteAveragePayoff s₀ T σ who| ≤
      2 * C * (T : ℝ)⁻¹ := by
  rw [G.finiteAveragePayoff_withExpectedPotentialShaping_sub F]
  have hstate : |G.expectedStateValue σ s₀ T (F who)| ≤ C := by
    unfold expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun h => hF who h.2
  have hboundary :
      |G.expectedStateValue σ s₀ T (F who) - F who s₀| ≤ 2 * C := by
    calc
      |G.expectedStateValue σ s₀ T (F who) - F who s₀|
          ≤ |G.expectedStateValue σ s₀ T (F who)| + |F who s₀| :=
        abs_sub _ _
      _ ≤ C + C := add_le_add hstate (hF who s₀)
      _ = 2 * C := by ring
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ)⁻¹)]
  calc
    (T : ℝ)⁻¹ *
        |G.expectedStateValue σ s₀ T (F who) - F who s₀|
        ≤ (T : ℝ)⁻¹ * (2 * C) :=
      mul_le_mul_of_nonneg_left hboundary (by positivity)
    _ = 2 * C * (T : ℝ)⁻¹ := by ring

/-- A denominator-shifted vanishing modulus valid at every horizon, including
`T = 0`. -/
theorem hasFiniteAverageGapAtMost_withExpectedPotentialShaping
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hF : ∀ who s, |F who s| ≤ C)
    (s₀ : G.State) :
    G.HasFiniteAverageGapAtMost s₀ (G.expectedPotentialShapedReward F)
      (fun T => 4 * C / ((T : ℝ) + 1)) := by
  intro T σ who
  change
    |(G.withExpectedPotentialShaping F).finiteAveragePayoff s₀ T σ who -
        G.finiteAveragePayoff s₀ T σ who| ≤
      4 * C / ((T : ℝ) + 1)
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst T
    simp [withExpectedPotentialShaping, hC0]
  · have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hTplus : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hratio :
        2 * C * (T : ℝ)⁻¹ ≤ 4 * C / ((T : ℝ) + 1) := by
      calc
        2 * C * (T : ℝ)⁻¹ = (2 * C) / (T : ℝ) := by
          rw [div_eq_mul_inv]
        _ ≤ (4 * C) / ((T : ℝ) + 1) := by
          rw [div_le_div_iff₀ hTreal hTplus]
          nlinarith
    exact
      (G.abs_finiteAveragePayoff_withExpectedPotentialShaping_sub_le
        F hF σ s₀ T who).trans hratio

/-- The denominator-shifted shaping modulus tends to zero. -/
theorem tendsto_expectedPotentialShapingGap_zero (C : ℝ) :
    Tendsto (fun T : ℕ => 4 * C / ((T : ℝ) + 1)) atTop (nhds 0) := by
  have h :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * C) :
      Tendsto (fun T : ℕ => 4 * C * (1 / ((T : ℝ) + 1))) atTop (nhds 0))
  simpa [div_eq_mul_inv] using h

/-- Bounded expected-potential shaping preserves exactly the uniform-equilibrium
payoff set. -/
theorem isUniformEquilibriumPayoff_withExpectedPotentialShaping_iff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (F : ι → G.State → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hF : ∀ who s, |F who s| ≤ C)
    (s₀ : G.State) (v : Payoff ι) :
    (G.withExpectedPotentialShaping F).IsUniformEquilibriumPayoff s₀ v ↔
      G.IsUniformEquilibriumPayoff s₀ v := by
  exact G.isUniformEquilibriumPayoff_withStagePayoff_iff_of_tendsto_gap_zero
    s₀ (G.expectedPotentialShapedReward F)
    (fun T => 4 * C / ((T : ℝ) + 1))
    (G.hasFiniteAverageGapAtMost_withExpectedPotentialShaping F hC0 hF s₀)
    (tendsto_expectedPotentialShapingGap_zero C) v

end StochasticGame
end GameTheory
