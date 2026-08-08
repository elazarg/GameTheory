/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.SystemEnforcementLedger

/-!
# Finite-time target bounds for adaptive potentials

An adaptive-potential certificate only anchors its three potentials at time
zero.  Their expectation-level monotonicity and Cesàro charge bounds
nevertheless keep the prescribed expectations close to the target at every
finite time.

The key scalar lemma is elementary and uses no limiting theorem.  If an
antitone value sequence dominates stage payoffs up to a charge whose Cesàro
average is bounded above, while the payoff Cesàro average is bounded below,
then every value is bounded below by the target minus the two errors.  A
finite prefix cannot affect the conclusion: assuming a strict failure, one
chooses one sufficiently long finite horizon and obtains a contradiction.

Applied to an adaptive system at error `error`, the prescribed lower, upper,
and deviation-potential expectations all stay within `3 * error` of the
target.  The factor three is the sum of the existing `2 * error` prescribed
payoff bound and the `error` charge bound.  The opposite one-sided estimate
uses the potential's initial anchor and monotonicity and is sharper.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

/-- An antitone value sequence with a payoff lower bound and charge upper
bound cannot fall below the target minus the two errors.

This is a purely finite-horizon argument.  No convergence or boundedness
assumption on the sequences is used. -/
theorem antitoneValue_ge_target_sub_errors_of_cesaro
    (value payoff charge : ℕ → ℝ)
    (target payoffError chargeError : ℝ) (horizon time : ℕ)
    (value_antitone : Antitone value)
    (stage_le : ∀ stage, payoff stage ≤ value stage + charge stage)
    (payoff_cesaro : ∀ total, horizon ≤ total →
      target - payoffError ≤
        (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage)
    (charge_cesaro : ∀ total, horizon ≤ total →
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, charge stage ≤
        chargeError) :
    target - payoffError - chargeError ≤ value time := by
  by_contra failure
  have strict :
      value time < target - payoffError - chargeError := by
    exact lt_of_not_ge failure
  let gap : ℝ :=
    target - payoffError - chargeError - value time
  have gap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have value_time_le_zero := value_antitone (Nat.zero_le time)
  let prefixCost : ℝ :=
    (time : ℝ) * (value 0 - value time)
  have prefixCost_nonneg : 0 ≤ prefixCost := by
    dsimp [prefixCost]
    positivity
  obtain ⟨large, large_gt⟩ :=
    exists_nat_gt (prefixCost / gap)
  let total : ℕ := max (max horizon time) large + 1
  have horizon_le_total : horizon ≤ total := by
    dsimp [total]
    omega
  have time_le_total : time ≤ total := by
    dsimp [total]
    omega
  have large_lt_total : large < total := by
    dsimp [total]
    omega
  have total_pos : 0 < total := lt_of_le_of_lt (Nat.zero_le large) large_lt_total
  have total_real_pos : (0 : ℝ) < total := by
    exact_mod_cast total_pos
  have prefix_small :
      prefixCost < (total : ℝ) * gap := by
    have large_real_lt_total : (large : ℝ) < total := by
      exact_mod_cast large_lt_total
    have ratio_lt_total :
        prefixCost / gap < (total : ℝ) :=
      large_gt.trans large_real_lt_total
    rw [div_lt_iff₀ gap_pos] at ratio_lt_total
    exact ratio_lt_total
  have prefix_bound :
      ∑ stage ∈ Finset.range time, value stage ≤
        (time : ℝ) * value 0 := by
    calc
      ∑ stage ∈ Finset.range time, value stage ≤
          ∑ _stage ∈ Finset.range time, value 0 := by
            apply Finset.sum_le_sum
            intro stage stage_mem
            exact value_antitone (Nat.zero_le stage)
      _ = (time : ℝ) * value 0 := by
        simp [nsmul_eq_mul]
  have tail_bound :
      ∑ stage ∈ Finset.Ico time total, value stage ≤
        ((total - time : ℕ) : ℝ) * value time := by
    calc
      ∑ stage ∈ Finset.Ico time total, value stage ≤
          ∑ _stage ∈ Finset.Ico time total, value time := by
            apply Finset.sum_le_sum
            intro stage stage_mem
            exact value_antitone (Finset.mem_Ico.mp stage_mem).1
      _ = ((total - time : ℕ) : ℝ) * value time := by
        simp [Nat.card_Ico, time_le_total, nsmul_eq_mul]
  have value_sum_bound :
      ∑ stage ∈ Finset.range total, value stage ≤
        (total : ℝ) * value time + prefixCost := by
    rw [← Finset.sum_range_add_sum_Ico _ time_le_total]
    calc
      ∑ stage ∈ Finset.range time, value stage +
          ∑ stage ∈ Finset.Ico time total, value stage ≤
        (time : ℝ) * value 0 +
          ((total - time : ℕ) : ℝ) * value time :=
            add_le_add prefix_bound tail_bound
      _ = (total : ℝ) * value time + prefixCost := by
        dsimp [prefixCost]
        rw [Nat.cast_sub time_le_total]
        ring
  have stage_sum_bound :
      ∑ stage ∈ Finset.range total, payoff stage ≤
        ∑ stage ∈ Finset.range total, value stage +
          ∑ stage ∈ Finset.range total, charge stage := by
    calc
      ∑ stage ∈ Finset.range total, payoff stage ≤
          ∑ stage ∈ Finset.range total,
            (value stage + charge stage) := by
              apply Finset.sum_le_sum
              intro stage stage_mem
              exact stage_le stage
      _ =
          ∑ stage ∈ Finset.range total, value stage +
            ∑ stage ∈ Finset.range total, charge stage := by
              rw [Finset.sum_add_distrib]
  have averaged_value_bound :
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, value stage <
        value time + gap := by
    calc
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, value stage ≤
        (total : ℝ)⁻¹ *
          ((total : ℝ) * value time + prefixCost) := by
            exact mul_le_mul_of_nonneg_left value_sum_bound
              (inv_nonneg.mpr total_real_pos.le)
      _ = value time + prefixCost / (total : ℝ) := by
        field_simp
      _ < value time + gap := by
        have divided :
            prefixCost / (total : ℝ) < gap := by
          apply (div_lt_iff₀ total_real_pos).2
          simpa only [mul_comm] using prefix_small
        linarith
  have averaged_stage_bound :
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage <
        value time + gap + chargeError := by
    calc
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage ≤
        (total : ℝ)⁻¹ *
          (∑ stage ∈ Finset.range total, value stage +
            ∑ stage ∈ Finset.range total, charge stage) := by
              exact mul_le_mul_of_nonneg_left stage_sum_bound
                (inv_nonneg.mpr total_real_pos.le)
      _ =
          (total : ℝ)⁻¹ *
              ∑ stage ∈ Finset.range total, value stage +
            (total : ℝ)⁻¹ *
              ∑ stage ∈ Finset.range total, charge stage := by
                ring
      _ < value time + gap + chargeError := by
        have charge_bound := charge_cesaro total horizon_le_total
        linarith
  have payoff_lower := payoff_cesaro total horizon_le_total
  dsimp [gap] at averaged_stage_bound
  linarith

variable {ι : Type} {G : StochasticGame ι}

namespace AdaptivePotentialSystemAt

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    {profile : G.BehaviorProfile} {initial : G.State}
    {target : Payoff ι} {error : ℝ}

/-- Under prescribed play, the deviation-potential expectation at every
finite time is at least the target minus three errors. -/
theorem target_sub_three_mul_error_le_expectedDeviationPotential
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (_error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    target who - 3 * error ≤
      G.expectedHistoryValue profile initial
        (system.deviationPotential who) time := by
  let value : ℕ → ℝ := fun stage =>
    G.expectedHistoryValue profile initial
      (system.deviationPotential who) stage
  let payoff : ℕ → ℝ := fun stage =>
    G.expectedStagePayoff profile initial stage who
  let charge : ℕ → ℝ := fun stage =>
    system.deviationCharge who (profile who) stage
  have value_antitone : Antitone value := by
    apply antitone_nat_of_succ_le
    intro stage
    simpa [value] using
      system.deviation_supermartingale who (profile who) stage
  have stage_le : ∀ stage, payoff stage ≤ value stage + charge stage := by
    intro stage
    simpa [payoff, value, charge] using
      system.deviation_stage who (profile who) stage
  have payoff_cesaro : ∀ total, system.horizon ≤ total →
      target who - 2 * error ≤
        (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage := by
    intro total total_ge
    have payoff_close :=
      system.abs_finiteAveragePayoff_sub_target_le_two_mul_error
        who total total_ge
    rw [abs_le] at payoff_close
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff] at payoff_close
    dsimp [payoff]
    linarith [payoff_close.1]
  have charge_cesaro : ∀ total, system.horizon ≤ total →
      (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, charge stage ≤
        error := by
    intro total total_ge
    simpa [charge] using
      system.deviation_charge_cesaro
        who (profile who) total total_ge
  have bound :=
    antitoneValue_ge_target_sub_errors_of_cesaro
      value payoff charge (target who) (2 * error) error
      system.horizon time value_antitone stage_le
      payoff_cesaro charge_cesaro
  dsimp [value] at bound
  linarith

/-- Under prescribed play, the deviation-potential expectation at every
finite time is at most the target plus one error. -/
theorem expectedDeviationPotential_le_target_add_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (time : ℕ) :
    G.expectedHistoryValue profile initial
        (system.deviationPotential who) time ≤
      target who + error := by
  have antitone :
      Antitone fun stage =>
        G.expectedHistoryValue profile initial
          (system.deviationPotential who) stage := by
    apply antitone_nat_of_succ_le
    intro stage
    simpa using
      system.deviation_supermartingale who (profile who) stage
  have initial_le :
      system.deviationPotential who 0 (G.emptyHist initial) ≤
        target who + error := by
    have anchored := (abs_le.mp (system.deviation_initial who)).2
    linarith
  rw [← G.expectedHistoryValue_zero profile initial
    (system.deviationPotential who)] at initial_le
  exact (antitone (Nat.zero_le time)).trans initial_le

/-- The prescribed deviation-potential expectation remains within three
errors of the target at every finite time. -/
theorem abs_expectedDeviationPotential_sub_target_le_three_mul_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    |G.expectedHistoryValue profile initial
        (system.deviationPotential who) time - target who| ≤
      3 * error := by
  rw [abs_le]
  constructor
  · have lower :=
      system.target_sub_three_mul_error_le_expectedDeviationPotential
        error_nonneg who time
    linarith
  · have upper :=
      system.expectedDeviationPotential_le_target_add_error who time
    linarith

/-- Under prescribed play, the upper-potential expectation at every finite
time is at least the target minus three errors. -/
theorem target_sub_three_mul_error_le_expectedUpperPotential
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (_error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    target who - 3 * error ≤
      G.expectedHistoryValue profile initial
        (system.upperPotential who) time := by
  let value : ℕ → ℝ := fun stage =>
    G.expectedHistoryValue profile initial
      (system.upperPotential who) stage
  let payoff : ℕ → ℝ := fun stage =>
    G.expectedStagePayoff profile initial stage who
  let charge : ℕ → ℝ := fun stage =>
    system.upperCharge who stage
  have value_antitone : Antitone value :=
    antitone_nat_of_succ_le (system.upper_supermartingale who)
  have stage_le : ∀ stage, payoff stage ≤ value stage + charge stage :=
    system.upper_stage who
  have payoff_cesaro : ∀ total, system.horizon ≤ total →
      target who - 2 * error ≤
        (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage := by
    intro total total_ge
    have payoff_close :=
      system.abs_finiteAveragePayoff_sub_target_le_two_mul_error
        who total total_ge
    rw [abs_le] at payoff_close
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff] at payoff_close
    dsimp [payoff]
    linarith [payoff_close.1]
  have bound :=
    antitoneValue_ge_target_sub_errors_of_cesaro
      value payoff charge (target who) (2 * error) error
      system.horizon time value_antitone stage_le
      payoff_cesaro (system.upper_charge_cesaro who)
  dsimp [value] at bound
  linarith

/-- Under prescribed play, the upper-potential expectation at every finite
time is at most the target plus one error. -/
theorem expectedUpperPotential_le_target_add_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (time : ℕ) :
    G.expectedHistoryValue profile initial
        (system.upperPotential who) time ≤
      target who + error := by
  have antitone :
      Antitone fun stage =>
        G.expectedHistoryValue profile initial
          (system.upperPotential who) stage :=
    antitone_nat_of_succ_le (system.upper_supermartingale who)
  have initial_le :
      system.upperPotential who 0 (G.emptyHist initial) ≤
        target who + error := by
    have anchored := (abs_le.mp (system.upper_initial who)).2
    linarith
  rw [← G.expectedHistoryValue_zero profile initial
    (system.upperPotential who)] at initial_le
  exact (antitone (Nat.zero_le time)).trans initial_le

/-- The prescribed upper-potential expectation remains within three errors
of the target at every finite time. -/
theorem abs_expectedUpperPotential_sub_target_le_three_mul_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    |G.expectedHistoryValue profile initial
        (system.upperPotential who) time - target who| ≤
      3 * error := by
  rw [abs_le]
  constructor
  · have lower :=
      system.target_sub_three_mul_error_le_expectedUpperPotential
        error_nonneg who time
    linarith
  · have upper :=
      system.expectedUpperPotential_le_target_add_error who time
    linarith

/-- Under prescribed play, the lower-potential expectation at every finite
time is at most the target plus three errors. -/
theorem expectedLowerPotential_le_target_add_three_mul_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (_error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    G.expectedHistoryValue profile initial
        (system.lowerPotential who) time ≤
      target who + 3 * error := by
  let value : ℕ → ℝ := fun stage =>
    -G.expectedHistoryValue profile initial
      (system.lowerPotential who) stage
  let payoff : ℕ → ℝ := fun stage =>
    -G.expectedStagePayoff profile initial stage who
  let charge : ℕ → ℝ := fun stage =>
    system.lowerCharge who stage
  have value_antitone : Antitone value := by
    intro left right left_le
    dsimp [value]
    exact neg_le_neg
      ((monotone_nat_of_le_succ
        (system.lower_submartingale who)) left_le)
  have stage_le : ∀ stage, payoff stage ≤ value stage + charge stage := by
    intro stage
    dsimp [payoff, value, charge]
    have lower_stage := system.lower_stage who stage
    linarith
  have payoff_cesaro : ∀ total, system.horizon ≤ total →
      -target who - 2 * error ≤
        (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total, payoff stage := by
    intro total total_ge
    have payoff_close :=
      system.abs_finiteAveragePayoff_sub_target_le_two_mul_error
        who total total_ge
    rw [abs_le] at payoff_close
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff] at payoff_close
    dsimp [payoff]
    rw [Finset.sum_neg_distrib]
    nlinarith [payoff_close.2]
  have bound :=
    antitoneValue_ge_target_sub_errors_of_cesaro
      value payoff charge (-target who) (2 * error) error
      system.horizon time value_antitone stage_le
      payoff_cesaro (system.lower_charge_cesaro who)
  dsimp [value] at bound
  linarith

/-- Under prescribed play, the lower-potential expectation at every finite
time is at least the target minus one error. -/
theorem target_sub_error_le_expectedLowerPotential
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (time : ℕ) :
    target who - error ≤
      G.expectedHistoryValue profile initial
        (system.lowerPotential who) time := by
  have monotone :
      Monotone fun stage =>
        G.expectedHistoryValue profile initial
          (system.lowerPotential who) stage :=
    monotone_nat_of_le_succ (system.lower_submartingale who)
  have initial_ge :
      target who - error ≤
        system.lowerPotential who 0 (G.emptyHist initial) := by
    have anchored := (abs_le.mp (system.lower_initial who)).1
    linarith
  rw [← G.expectedHistoryValue_zero profile initial
    (system.lowerPotential who)] at initial_ge
  exact initial_ge.trans (monotone (Nat.zero_le time))

/-- The prescribed lower-potential expectation remains within three errors
of the target at every finite time. -/
theorem abs_expectedLowerPotential_sub_target_le_three_mul_error
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (error_nonneg : 0 ≤ error) (who : ι) (time : ℕ) :
    |G.expectedHistoryValue profile initial
        (system.lowerPotential who) time - target who| ≤
      3 * error := by
  rw [abs_le]
  constructor
  · have lower :=
      system.target_sub_error_le_expectedLowerPotential who time
    linarith
  · have upper :=
      system.expectedLowerPotential_le_target_add_three_mul_error
        error_nonneg who time
    linarith

end AdaptivePotentialSystemAt

end StochasticGame
end GameTheory
