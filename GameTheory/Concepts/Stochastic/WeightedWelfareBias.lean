/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.WeightedSecurityWelfareAssembly

/-!
# A bounded Bellman-bias source for weighted welfare caps

A scalar social bias satisfying a universal upper Bellman inequality makes
weighted average welfare telescope. Bounded endpoint terms vanish uniformly
with the horizon, producing the semantic all-profile welfare cap consumed by
the weighted security--welfare assembly theorem.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open scoped BigOperators

open Math.Probability

namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-! ## A bounded Bellman bias supplies the welfare cap -/

/-- A scalar social bias whose one-step drift universally caps weighted stage
welfare.  This is an average-reward upper Bellman certificate for the
grand-coalition planner problem. -/
def HasWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (v : Payoff ι) : Prop :=
  ∃ (bias : G.State → ℝ) (bound : ℝ),
    0 ≤ bound ∧
    (∀ state, |bias state| ≤ bound) ∧
    ∀ (state : G.State) (action : G.JointAct),
      (∑ i, weight i * G.stagePayoff state action i) +
          expect (G.transition state action) bias ≤
        (∑ i, weight i * v i) + bias state

private theorem weightedStageEU_eq_expect
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (profile : G.BehaviorProfile)
    {time : ℕ} (history : G.Hist time) :
    (∑ i, weight i * G.stageEUAt profile history i) =
      expect (G.stageActionDist profile history)
        (fun action => ∑ i, weight i * G.stagePayoff history.2 action i) := by
  rw [← expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i i_mem
  unfold GameTheory.StochasticGame.stageEUAt
  rw [expect_const_mul]

private theorem weightedExpectedStagePayoff_eq_expect
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (weight : ι → ℝ) (profile : G.BehaviorProfile)
    (s₀ : G.State) (time : ℕ) :
    (∑ i, weight i * G.expectedStagePayoff profile s₀ time i) =
      expect (G.histDist profile s₀ time)
        (fun history => ∑ i, weight i * G.stageEUAt profile history i) := by
  rw [← expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i i_mem
  unfold GameTheory.StochasticGame.expectedStagePayoff
  rw [expect_const_mul]

/-- A bounded universal weighted-welfare Bellman bias gives the semantic
uniform welfare cap, with the usual `2 * bound / T` endpoint loss. -/
theorem hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (certificate : HasWeightedWelfareBias G weight v) :
    HasUniformWeightedWelfareCap G s₀ weight v := by
  classical
  obtain ⟨bias, bound, bound_nonneg, bias_bound, bellman⟩ := certificate
  intro error error_pos
  obtain ⟨cutoff, cutoff_gt⟩ := exists_nat_gt (2 * bound / error)
  refine ⟨max 1 (cutoff + 1), fun profile T T_ge => ?_⟩
  have T_pos : 0 < T := by
    have : 1 ≤ T := (Nat.le_max_left 1 (cutoff + 1)).trans T_ge
    omega
  have cutoff_lt_T : cutoff < T := by
    have : cutoff + 1 ≤ T :=
      (Nat.le_max_right 1 (cutoff + 1)).trans T_ge
    omega
  let target : ℝ := ∑ i, weight i * v i
  have expectedStep (time : ℕ) :
      (∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          G.expectedStateValue profile s₀ (time + 1) bias ≤
        target + G.expectedStateValue profile s₀ time bias := by
    rw [weightedExpectedStagePayoff_eq_expect]
    rw [G.expectedStateValue_succ]
    rw [← expect_add]
    calc
      expect (G.histDist profile s₀ time)
          (fun history =>
            (∑ i, weight i * G.stageEUAt profile history i) +
              expect (G.stageActionDist profile history)
                (fun action => expect (G.transition history.2 action) bias)) ≤
          expect (G.histDist profile s₀ time)
            (fun history => target + bias history.2) := by
        apply expect_mono
        intro history
        rw [weightedStageEU_eq_expect, ← expect_add]
        calc
          expect (G.stageActionDist profile history)
              (fun action =>
                (∑ i, weight i * G.stagePayoff history.2 action i) +
                  expect (G.transition history.2 action) bias) ≤
              expect (G.stageActionDist profile history)
                (fun _ => target + bias history.2) := by
            apply expect_mono
            intro action
            simpa only [target] using bellman history.2 action
          _ = target + bias history.2 := expect_const _ _
      _ = target + G.expectedStateValue profile s₀ time bias := by
        rw [expect_add, expect_const]
        rfl
  have telescope : ∀ horizon : ℕ,
      (∑ time ∈ Finset.range horizon,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) +
          G.expectedStateValue profile s₀ horizon bias ≤
        (horizon : ℝ) * target + bias s₀ := by
    intro horizon
    induction horizon with
    | zero => simp [GameTheory.StochasticGame.expectedStateValue_zero]
    | succ horizon inductionHypothesis =>
      rw [Finset.sum_range_succ]
      push_cast
      linarith [expectedStep horizon]
  have expectedBias_abs :
      |G.expectedStateValue profile s₀ T bias| ≤ bound := by
    unfold GameTheory.StochasticGame.expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun history => bias_bound history.2
  have totalStageCap :
      (∑ time ∈ Finset.range T,
          ∑ i, weight i * G.expectedStagePayoff profile s₀ time i) ≤
        (T : ℝ) * target + 2 * bound := by
    have initialBiasUpper := (abs_le.mp (bias_bound s₀)).2
    have terminalBiasLower := (abs_le.mp expectedBias_abs).1
    linarith [telescope T]
  have weightedAverage_eq :
      (∑ i, weight i * G.finiteAveragePayoff s₀ T profile i) =
        (T : ℝ)⁻¹ *
          ∑ time ∈ Finset.range T,
            ∑ i, weight i * G.expectedStagePayoff profile s₀ time i := by
    simp_rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    calc
      (∑ i, weight i *
          ((T : ℝ)⁻¹ *
            ∑ time ∈ Finset.range T,
              G.expectedStagePayoff profile s₀ time i)) =
          (T : ℝ)⁻¹ *
            ∑ i, weight i *
              ∑ time ∈ Finset.range T,
                G.expectedStagePayoff profile s₀ time i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i i_mem
        ring
      _ = (T : ℝ)⁻¹ *
          ∑ i, ∑ time ∈ Finset.range T,
            weight i * G.expectedStagePayoff profile s₀ time i := by
        congr 1
        apply Finset.sum_congr rfl
        intro i i_mem
        rw [Finset.mul_sum]
      _ = (T : ℝ)⁻¹ *
          ∑ time ∈ Finset.range T,
            ∑ i, weight i * G.expectedStagePayoff profile s₀ time i := by
        congr 1
        rw [Finset.sum_comm]
  have T_real_pos : (0 : ℝ) < T := by exact_mod_cast T_pos
  have cutoff_real_lt : (cutoff : ℝ) < T := by exact_mod_cast cutoff_lt_T
  have boundary_lt : 2 * bound / (T : ℝ) < error := by
    have positiveProduct : (cutoff : ℝ) * error < (T : ℝ) * error :=
      mul_lt_mul_of_pos_right cutoff_real_lt error_pos
    rw [div_lt_iff₀ error_pos] at cutoff_gt
    apply (div_lt_iff₀ T_real_pos).2
    linarith
  rw [weightedAverage_eq]
  have scaledCap := mul_le_mul_of_nonneg_left totalStageCap
    (inv_nonneg.mpr T_real_pos.le)
  have inverse_mul_T : (T : ℝ)⁻¹ * T = 1 := inv_mul_cancel₀ T_real_pos.ne'
  rw [mul_add, ← mul_assoc, inverse_mul_T, one_mul] at scaledCap
  rw [show (T : ℝ)⁻¹ * (2 * bound) = 2 * bound / T by
    rw [div_eq_mul_inv]
    ring] at scaledCap
  dsimp only [target] at scaledCap ⊢
  linarith

/-- Concrete composition: one-sided security guarantees together with a
bounded universal social Bellman bias imply a uniform equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (weight_ge_one : ∀ i, 1 ≤ weight i)
    (security : ∀ i, G.IsOneSidedGuaranteeCertificate s₀ i (v i))
    (bias : HasWeightedWelfareBias G weight v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap
    G s₀ weight v weight_ge_one security
      (hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
        G s₀ weight v bias)

/-- Strictly positive one-sided security weights and a bounded universal
weighted-welfare Bellman bias assemble directly into a uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareBias
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (weight : ι → ℝ) (v : Payoff ι)
    (weight_pos : ∀ i, 0 < weight i)
    (security : ∀ i, G.IsOneSidedGuaranteeCertificate s₀ i (v i))
    (bias : HasWeightedWelfareBias G weight v) :
    G.IsUniformEquilibriumPayoff s₀ v :=
  isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap
    G s₀ weight v weight_pos security
      (hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
        G s₀ weight v bias)

end StochasticGame

end GameTheory
