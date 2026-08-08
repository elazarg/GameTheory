/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Architectures.PublicResponse.ArbitraryStartPrescribedDeliveryTelescope
import UniformEquilibrium.Quitting.Examples.FTV.CyclicCredibility

/-!
# Finite-horizon delivery in the FTV three-cycle

This file makes the timing convention in `quittingGame` quantitative.  A live
state pays zero in the current stage; if somebody quits, the terminal reward
starts at the following stage.  Under the prescribed FTV cycle, the resulting
coordinatewise delivery remainders from phase zero are `16/7`, `22/7`, and
`18/7`.  Thus the current model has the uniform modulus `22 / (7 * T)`.

The proof is an exact Poisson-bias telescope.  No asymptotic absorption
argument or credibility converse is used.
-/

noncomputable section

namespace GameTheory
namespace FTVCyclicCredibility

open Math.Probability StochasticGame

/-- The Poisson bias for prescribed delivery.  It is zero after absorption;
on the three live phases its rows are cyclic permutations of
`(-16/7,-22/7,-18/7)`. -/
def deliveryBias : Config → Payoff Player
  | Sum.inl c =>
      ![![-(16 / 7), -(22 / 7), -(18 / 7)],
        ![-(18 / 7), -(16 / 7), -(22 / 7)],
        ![-(22 / 7), -(18 / 7), -(16 / 7)]] c
  | Sum.inr _ => fun _ => 0

/-- Coordinatewise finite-horizon constants at the phase-zero entry. -/
def deliveryConstant : Player → ℝ := ![16 / 7, 22 / 7, 18 / 7]

@[simp] theorem deliveryBias_start (who : Player) :
    deliveryBias architecture.start who = -deliveryConstant who := by
  fin_cases who <;> norm_num [deliveryBias, deliveryConstant]

/-- In the repository's quitting-game convention, a live configuration pays
zero even on the stage at which quitting occurs. -/
@[simp] theorem prescribedStagePayoff_live (c who : Player) :
    architecture.prescribedStagePayoff (Sum.inl c) who = 0 := by
  simp [StochasticGame.FiniteResponseArchitecture.prescribedStagePayoff,
    StochasticGame.FiniteResponseArchitecture.prescribedActionDist,
    game, quittingGame, publicState]

/-- The explicit live-phase bias solves the prescribed Poisson equation. -/
theorem expect_deliveryBias_live (c who : Player) :
    expect (architecture.prescribedConfigDist (Sum.inl c))
        (fun z => deliveryBias z who) =
      target (Sum.inl c) who + deliveryBias (Sum.inl c) who := by
  simp only [StochasticGame.FiniteResponseArchitecture.prescribedConfigDist,
    StochasticGame.FiniteResponseArchitecture.prescribedActionDist,
    expect_bind, expect_pure]
  change expect (Math.PMFProduct.pmfPi (play (Sum.inl c))) (fun act =>
      expect ((quittingGame terminalReward).transition none act) (fun s' =>
        deliveryBias (step (Sum.inl c) act s') who)) = _
  rw [expect_pmfPi_fin3_bool]
  fin_cases c <;> fin_cases who <;>
    simp [play, game, quittingGame, step, target, phaseTarget, nextPhase,
      deliveryBias, terminalReward] <;> norm_num

/-- The prescribed target and bias satisfy the exact one-step delivery
identity at every controller configuration. -/
theorem prescribed_deliveryBias_equation (z : Config) (who : Player) :
    target z who + deliveryBias z who =
      architecture.prescribedStagePayoff z who +
        expect (architecture.prescribedConfigDist z)
          (fun y => deliveryBias y who) := by
  cases z with
  | inl c =>
      rw [prescribedStagePayoff_live, zero_add, expect_deliveryBias_live]
  | inr S =>
      rw [deliveryBias, add_zero, prescribedStagePayoff_child]
      simp [deliveryBias,
        StochasticGame.FiniteResponseArchitecture.prescribedConfigDist,
        StochasticGame.FiniteResponseArchitecture.prescribedActionDist,
        architecture, game, quittingGame, publicState, step]

/-- Every bias coordinate lies in the common interval `[-22/7,0]`. -/
theorem deliveryBias_mem_interval (z : Config) (who : Player) :
    -(22 / 7 : ℝ) ≤ deliveryBias z who ∧ deliveryBias z who ≤ 0 := by
  cases z with
  | inl c =>
      fin_cases c <;> fin_cases who <;> norm_num [deliveryBias]
  | inr S => constructor <;> norm_num [deliveryBias]

/-- The expected horizon bias remains in the same common interval. -/
theorem expectedHistoryValue_deliveryBias_mem_interval (who : Player)
    (T : ℕ) :
    -(22 / 7 : ℝ) ≤
        game.expectedHistoryValue architecture.phaseProfile.behaviorProfile
          initialState (fun t h => deliveryBias (architecture.configAt t h) who) T ∧
      game.expectedHistoryValue architecture.phaseProfile.behaviorProfile
          initialState (fun t h => deliveryBias (architecture.configAt t h) who) T ≤ 0 := by
  unfold StochasticGame.expectedHistoryValue
  constructor
  · calc
      -(22 / 7 : ℝ) =
          expect (game.histDist architecture.phaseProfile.behaviorProfile
            initialState T) (fun _ => -(22 / 7 : ℝ)) := by
              rw [expect_const]
      _ ≤ expect (game.histDist architecture.phaseProfile.behaviorProfile
            initialState T)
          (fun h => deliveryBias (architecture.configAt T h) who) :=
        expect_mono _ _ _ fun h => (deliveryBias_mem_interval _ who).1
  · calc
      expect (game.histDist architecture.phaseProfile.behaviorProfile
            initialState T)
          (fun h => deliveryBias (architecture.configAt T h) who) ≤
          expect (game.histDist architecture.phaseProfile.behaviorProfile
            initialState T) (fun _ => (0 : ℝ)) :=
        expect_mono _ _ _ fun h => (deliveryBias_mem_interval _ who).2
      _ = 0 := expect_const _ _

/-- Exact finite-horizon prescribed-payoff identity at the phase-zero entry. -/
theorem finiteAveragePayoff_eq_initialTarget_add_biasRemainder
    (who : Player) {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff initialState T
        architecture.phaseProfile.behaviorProfile who =
      initialTarget who +
        (deliveryBias architecture.start who -
          game.expectedHistoryValue architecture.phaseProfile.behaviorProfile
            initialState
            (fun t h => deliveryBias (architecture.configAt t h) who) T) / T := by
  let R := architecture.reachableRegion
  have hT0 : architecture.IsPrescribedTargetHarmonicOn R target := by
    intro player z hz
    exact isPrescribedTargetHarmonic player z
  have hbias : ∀ z : Config, R.prescribed z →
      target z who + deliveryBias z who =
        architecture.prescribedStagePayoff z who +
          expect (architecture.prescribedConfigDist z)
            (fun y => deliveryBias y who) := by
    intro z hz
    exact prescribed_deliveryBias_equation z who
  rw [← target_start who]
  exact architecture.finiteAveragePayoff_prescribed_eq_on
    hT0 who (fun z => deliveryBias z who) hbias hT

/-- Exact coordinatewise `O(1/T)` delivery bounds in the active-zero
quitting-game convention. -/
theorem abs_finiteAveragePayoff_sub_initialTarget_le
    (who : Player) {T : ℕ} (hT : 0 < T) :
    |game.finiteAveragePayoff initialState T
        architecture.phaseProfile.behaviorProfile who - initialTarget who| ≤
      deliveryConstant who / T := by
  have havg := finiteAveragePayoff_eq_initialTarget_add_biasRemainder who hT
  let endpoint :=
    game.expectedHistoryValue architecture.phaseProfile.behaviorProfile
      initialState
      (fun t h => deliveryBias (architecture.configAt t h) who) T
  have hend : -(22 / 7 : ℝ) ≤ endpoint ∧ endpoint ≤ 0 :=
    expectedHistoryValue_deliveryBias_mem_interval who T
  have hnum :
      |deliveryBias architecture.start who - endpoint| ≤ deliveryConstant who := by
    rw [deliveryBias_start, abs_le]
    constructor <;> fin_cases who <;>
      norm_num [deliveryConstant] at * <;> linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  rw [havg, add_sub_cancel_left, abs_div, abs_of_pos hTreal]
  exact (div_le_div_iff_of_pos_right hTreal).2 hnum

/-- Uniform three-player version of the coordinatewise estimate. -/
theorem abs_finiteAveragePayoff_sub_initialTarget_le_twentyTwo_sevenths
    (who : Player) {T : ℕ} (hT : 0 < T) :
    |game.finiteAveragePayoff initialState T
        architecture.phaseProfile.behaviorProfile who - initialTarget who| ≤
      (22 / 7 : ℝ) / T := by
  calc
    |game.finiteAveragePayoff initialState T
        architecture.phaseProfile.behaviorProfile who - initialTarget who| ≤
        deliveryConstant who / T :=
      abs_finiteAveragePayoff_sub_initialTarget_le who hT
    _ ≤ (22 / 7 : ℝ) / T := by
      have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
      apply (div_le_div_iff_of_pos_right hTreal).2
      fin_cases who <;> norm_num [deliveryConstant]

end FTVCyclicCredibility
end GameTheory
