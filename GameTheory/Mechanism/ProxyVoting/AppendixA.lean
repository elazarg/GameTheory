/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Dynamics
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Appendix A: better-response dynamics can converge to a worse outcome

The Bielous–Meir Appendix A configuration: peaks −11, −13, −13, −13, 12 with
followers at 5, 5, 1, 0 (true median 0, truthful outcome −11, social cost
84).  Six Euclidean better responses lead to the state (4, 9, 8, 7, 5) with
outcome 5 — closer to the true median than the truthful outcome, yet with
social cost 86.  Over the integer grid this state is a pure Nash
equilibrium; over the reals it is not, since the winner can still nudge
inside the runner-up's distance. -/

namespace GameTheory

namespace ProxyVoting

open Finset

/-- Peaks for the Appendix A configuration. -/
def appendixAPeaks : Fin 5 → ℝ
  | 0 => -11
  | 1 => -13
  | 2 => -13
  | 3 => -13
  | 4 => 12

/-- Followers for the Appendix A configuration; the true median is 0. -/
def appendixAFollowers : Fin 4 → ℝ
  | 0 => 5
  | 1 => 5
  | 2 => 1
  | 3 => 0

/-- After the right proxy's better response to 10. -/
def appendixAState1 : Fin 5 → ℝ
  | 0 => -11
  | 1 => -13
  | 2 => -13
  | 3 => -13
  | 4 => 10

/-- After the first left proxy's better response to 9. -/
def appendixAState2 : Fin 5 → ℝ
  | 0 => -11
  | 1 => 9
  | 2 => -13
  | 3 => -13
  | 4 => 10

/-- After the second left proxy's better response to 8. -/
def appendixAState3 : Fin 5 → ℝ
  | 0 => -11
  | 1 => 9
  | 2 => 8
  | 3 => -13
  | 4 => 10

/-- After the third left proxy's better response to 7. -/
def appendixAState4 : Fin 5 → ℝ
  | 0 => -11
  | 1 => 9
  | 2 => 8
  | 3 => 7
  | 4 => 10

/-- After the truthful winner's better response to 4. -/
def appendixAState5 : Fin 5 → ℝ
  | 0 => 4
  | 1 => 9
  | 2 => 8
  | 3 => 7
  | 4 => 10

/-- After the right proxy's better response to 5 — the final state. -/
def appendixAState6 : Fin 5 → ℝ
  | 0 => 4
  | 1 => 9
  | 2 => 8
  | 3 => 7
  | 4 => 5

private theorem appA_update1 :
    Function.update appendixAPeaks 4 10 = appendixAState1 := by
  funext i
  fin_cases i <;> simp [appendixAPeaks, appendixAState1]

private theorem appA_update2 :
    Function.update appendixAState1 1 9 = appendixAState2 := by
  funext i
  fin_cases i <;> simp [appendixAState1, appendixAState2]

private theorem appA_update3 :
    Function.update appendixAState2 2 8 = appendixAState3 := by
  funext i
  fin_cases i <;> simp [appendixAState2, appendixAState3]

private theorem appA_update4 :
    Function.update appendixAState3 3 7 = appendixAState4 := by
  funext i
  fin_cases i <;> simp [appendixAState3, appendixAState4]

private theorem appA_update5 :
    Function.update appendixAState4 0 4 = appendixAState5 := by
  funext i
  fin_cases i <;> simp [appendixAState4, appendixAState5]

private theorem appA_update6 :
    Function.update appendixAState5 4 5 = appendixAState6 := by
  funext i
  fin_cases i <;> simp [appendixAState5, appendixAState6]

private theorem appA_s0_cum_zero :
    Math.cumWeight (allPos appendixAPeaks appendixAFollowers) (fun _ => 1) 0
      = 5 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAPeaks, appendixAFollowers]

private theorem appA_s0_cum_neg13 :
    Math.cumWeight (allPos appendixAPeaks appendixAFollowers) (fun _ => 1)
      (-13) = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAPeaks, appendixAFollowers]

private theorem appA_s0_cum_neg11 :
    Math.cumWeight (allPos appendixAPeaks appendixAFollowers) (fun _ => 1)
      (-11) = 4 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAPeaks, appendixAFollowers]

private theorem appA_median_s0 :
    socialMedian appendixAPeaks appendixAFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 3, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appA_s0_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixAPeaks appendixAFollowers)
            (fun _ => 1) (-11) < Math.totalWeight fun _ => 1
          rw [appA_s0_cum_neg11, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAPeaks appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s0_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAPeaks appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s0_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAPeaks appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s0_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAPeaks] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt

private theorem appA_median_s1 :
    socialMedian appendixAState1 appendixAFollowers = 0 := by
  rw [← appA_update1,
    socialMedian_update_eq_of_proxy_gt
      (by rw [appA_median_s0]; norm_num [appendixAPeaks])
      (by rw [appA_median_s0]; norm_num),
    appA_median_s0]

private theorem appA_s2_cum_one :
    Math.cumWeight (allPos appendixAState2 appendixAFollowers) (fun _ => 1) 1
      = 5 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState2, appendixAFollowers]

private theorem appA_s2_cum_neg13 :
    Math.cumWeight (allPos appendixAState2 appendixAFollowers) (fun _ => 1)
      (-13) = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState2, appendixAFollowers]

private theorem appA_s2_cum_neg11 :
    Math.cumWeight (allPos appendixAState2 appendixAFollowers) (fun _ => 1)
      (-11) = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState2, appendixAFollowers]

private theorem appA_s2_cum_zero :
    Math.cumWeight (allPos appendixAState2 appendixAFollowers) (fun _ => 1) 0
      = 4 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState2, appendixAFollowers]

private theorem appA_median_s2 :
    socialMedian appendixAState2 appendixAFollowers = 1 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 2, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appA_s2_cum_one]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixAState2 appendixAFollowers)
            (fun _ => 1) (-11) < Math.totalWeight fun _ => 1
          rw [appA_s2_cum_neg11, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAState2] at hzlt
        · change 2 * Math.cumWeight (allPos appendixAState2 appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s2_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAState2 appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s2_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAState2] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos appendixAState2 appendixAFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [appA_s2_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem appA_s3_cum_five :
    Math.cumWeight (allPos appendixAState3 appendixAFollowers) (fun _ => 1) 5
      = 6 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState3, appendixAFollowers]

private theorem appA_s3_cum_neg13 :
    Math.cumWeight (allPos appendixAState3 appendixAFollowers) (fun _ => 1)
      (-13) = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState3, appendixAFollowers]

private theorem appA_s3_cum_neg11 :
    Math.cumWeight (allPos appendixAState3 appendixAFollowers) (fun _ => 1)
      (-11) = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState3, appendixAFollowers]

private theorem appA_s3_cum_zero :
    Math.cumWeight (allPos appendixAState3 appendixAFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState3, appendixAFollowers]

private theorem appA_s3_cum_one :
    Math.cumWeight (allPos appendixAState3 appendixAFollowers) (fun _ => 1) 1
      = 4 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState3, appendixAFollowers]

private theorem appA_median_s3 :
    socialMedian appendixAState3 appendixAFollowers = 5 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appA_s3_cum_five]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixAState3 appendixAFollowers)
            (fun _ => 1) (-11) < Math.totalWeight fun _ => 1
          rw [appA_s3_cum_neg11, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAState3] at hzlt
        · norm_num [allPos, appendixAState3] at hzlt
        · change 2 * Math.cumWeight (allPos appendixAState3 appendixAFollowers)
            (fun _ => 1) (-13) < Math.totalWeight fun _ => 1
          rw [appA_s3_cum_neg13, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAState3] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos appendixAState3 appendixAFollowers)
            (fun _ => 1) 1 < Math.totalWeight fun _ => 1
          rw [appA_s3_cum_one, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAState3 appendixAFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [appA_s3_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem appA_s4_cum_five :
    Math.cumWeight (allPos appendixAState4 appendixAFollowers) (fun _ => 1) 5
      = 5 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState4, appendixAFollowers]

private theorem appA_s4_cum_neg11 :
    Math.cumWeight (allPos appendixAState4 appendixAFollowers) (fun _ => 1)
      (-11) = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState4, appendixAFollowers]

private theorem appA_s4_cum_zero :
    Math.cumWeight (allPos appendixAState4 appendixAFollowers) (fun _ => 1) 0
      = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState4, appendixAFollowers]

private theorem appA_s4_cum_one :
    Math.cumWeight (allPos appendixAState4 appendixAFollowers) (fun _ => 1) 1
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  norm_num [allPos, appendixAState4, appendixAFollowers]

private theorem appA_median_s4 :
    socialMedian appendixAState4 appendixAFollowers = 5 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appA_s4_cum_five]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixAState4 appendixAFollowers)
            (fun _ => 1) (-11) < Math.totalWeight fun _ => 1
          rw [appA_s4_cum_neg11, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixAState4] at hzlt
        · norm_num [allPos, appendixAState4] at hzlt
        · norm_num [allPos, appendixAState4] at hzlt
        · norm_num [allPos, appendixAState4] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, appendixAFollowers] at hzlt
        · norm_num [allPos, appendixAFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos appendixAState4 appendixAFollowers)
            (fun _ => 1) 1 < Math.totalWeight fun _ => 1
          rw [appA_s4_cum_one, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixAState4 appendixAFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [appA_s4_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem appA_median_s5 :
    socialMedian appendixAState5 appendixAFollowers = 5 := by
  rw [← appA_update5,
    socialMedian_update_eq_of_proxy_lt
      (by rw [appA_median_s4]; norm_num [appendixAState4])
      (by rw [appA_median_s4]; norm_num),
    appA_median_s4]

private theorem appA_median_s6 :
    socialMedian appendixAState6 appendixAFollowers = 5 := by
  rw [← appA_update6,
    socialMedian_update_eq_of_proxy_gt
      (by rw [appA_median_s5]; norm_num [appendixAState5])
      (by rw [appA_median_s5]),
    appA_median_s5]

private theorem appA_winner_s0 : winner appendixAPeaks appendixAFollowers = 0 := by
  unfold winner
  rw [appA_median_s0]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAPeaks]

private theorem appA_winner_s1 : winner appendixAState1 appendixAFollowers = 4 := by
  unfold winner
  rw [appA_median_s1]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState1]

private theorem appA_winner_s2 : winner appendixAState2 appendixAFollowers = 1 := by
  unfold winner
  rw [appA_median_s2]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState2]

private theorem appA_winner_s3 : winner appendixAState3 appendixAFollowers = 2 := by
  unfold winner
  rw [appA_median_s3]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState3]

private theorem appA_winner_s4 : winner appendixAState4 appendixAFollowers = 3 := by
  unfold winner
  rw [appA_median_s4]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState4]

private theorem appA_winner_s5 : winner appendixAState5 appendixAFollowers = 0 := by
  unfold winner
  rw [appA_median_s5]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState5]

private theorem appA_winner_s6 : winner appendixAState6 appendixAFollowers = 4 := by
  unfold winner
  rw [appA_median_s6]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i <;> first | exact absurd rfl hi | norm_num [appendixAState6]

private theorem appA_outcome_s0 :
    outcome appendixAPeaks appendixAFollowers = -11 := by
  unfold outcome
  rw [appA_winner_s0]
  rfl

private theorem appA_outcome_s1 :
    outcome appendixAState1 appendixAFollowers = 10 := by
  unfold outcome
  rw [appA_winner_s1]
  rfl

private theorem appA_outcome_s2 :
    outcome appendixAState2 appendixAFollowers = 9 := by
  unfold outcome
  rw [appA_winner_s2]
  rfl

private theorem appA_outcome_s3 :
    outcome appendixAState3 appendixAFollowers = 8 := by
  unfold outcome
  rw [appA_winner_s3]
  rfl

private theorem appA_outcome_s4 :
    outcome appendixAState4 appendixAFollowers = 7 := by
  unfold outcome
  rw [appA_winner_s4]
  rfl

private theorem appA_outcome_s5 :
    outcome appendixAState5 appendixAFollowers = 4 := by
  unfold outcome
  rw [appA_winner_s5]
  rfl

private theorem appA_outcome_s6 :
    outcome appendixAState6 appendixAFollowers = 5 := by
  unfold outcome
  rw [appA_winner_s6]
  rfl

/-- Appendix A, the realized path: six Euclidean better responses from the
truthful state to the final state, with outcomes −11, 10, 9, 8, 7, 4, 5. -/
theorem appendixA_dynamics_steps :
    IsBetterResponse appendixAPeaks appendixAFollowers appendixAPeaks 4 10
      ∧ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState1 1 9
      ∧ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState2 2 8
      ∧ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState3 3 7
      ∧ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState4 0 4
      ∧ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState5 4 5
      := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine isBetterResponse_of_prefers ?_ <;>
    unfold Prefers
  · rw [appA_update1, appA_outcome_s1, appA_outcome_s0]
    norm_num [appendixAPeaks]
  · rw [appA_update2, appA_outcome_s2, appA_outcome_s1]
    norm_num [appendixAPeaks]
  · rw [appA_update3, appA_outcome_s3, appA_outcome_s2]
    norm_num [appendixAPeaks]
  · rw [appA_update4, appA_outcome_s4, appA_outcome_s3]
    norm_num [appendixAPeaks]
  · rw [appA_update5, appA_outcome_s5, appA_outcome_s4]
    norm_num [appendixAPeaks]
  · rw [appA_update6, appA_outcome_s6, appA_outcome_s5]
    norm_num [appendixAPeaks]

/-- At the final state the median is pinned at 5 whatever any single proxy
reports: the other eight positions place enough weight on each side. -/
private theorem appA_s6_median_pinned (j : Fin 5) (y : ℝ) :
    socialMedian (Function.update appendixAState6 j y) appendixAFollowers
      = 5 := by
  fin_cases j <;>
    (refine socialMedian_update_eq_of_pinned
      ⟨(Sum.inr 0 : Fin 5 ⊕ Fin 4), by simp, rfl⟩ ?_ ?_ y <;>
      (rw [Math.totalWeight_one, Fintype.card_sum, Finset.sum_filter,
        Fintype.sum_sum_type]
       simp only [Fin.sum_univ_five, Fin.sum_univ_four]
       norm_num [allPos, appendixAState6, appendixAFollowers,
         Sum.inr_ne_inl, Sum.inl_ne_inr, Fin.ext_iff]))

/-- At the final state no proxy other than the winner can move the outcome at
all, whatever real position it reports: the winner sits exactly on the
pinned median, so it survives every deviation, up to the tie at the median
itself — which the deviator can only win by reporting the same position. -/
private theorem appA_s6_outcome_pinned (j : Fin 5) (hj : j ≠ 4) (y : ℝ) :
    outcome (Function.update appendixAState6 j y) appendixAFollowers = 5 := by
  unfold outcome winner
  rw [appA_s6_median_pinned j y]
  by_cases hy5 : y = 5
  · have hdel : delegate (Function.update appendixAState6 j y) 5 = j := by
      refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
      · rw [Function.update_self, hy5, show |(5:ℝ) - 5| = 0 by norm_num]
        exact abs_nonneg _
      · rw [Function.update_self, hy5, show |(5:ℝ) - 5| = 0 by norm_num,
          Function.update_of_ne (ne_of_lt hi)]
        fin_cases i
        · norm_num [appendixAState6]
        · norm_num [appendixAState6]
        · norm_num [appendixAState6]
        · norm_num [appendixAState6]
        · exact absurd hi (not_lt.mpr (Fin.le_last j))
    rw [hdel, Function.update_self]
    exact hy5
  · have hdel : delegate (Function.update appendixAState6 j y) 5 = 4 := by
      refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
      · rw [Function.update_of_ne (Ne.symm hj),
          show appendixAState6 4 = 5 from rfl, show |(5:ℝ) - 5| = 0 by norm_num]
        exact abs_nonneg _
      · rw [Function.update_of_ne (Ne.symm hj),
          show appendixAState6 4 = 5 from rfl, show |(5:ℝ) - 5| = 0 by norm_num]
        by_cases hij : i = j
        · rw [hij, Function.update_self]
          exact abs_pos.mpr (sub_ne_zero.mpr hy5)
        · rw [Function.update_of_ne hij]
          fin_cases i
          · norm_num [appendixAState6]
          · norm_num [appendixAState6]
          · norm_num [appendixAState6]
          · norm_num [appendixAState6]
          · exact absurd hi (lt_irrefl _)
    rw [hdel, Function.update_of_ne (Ne.symm hj)]
    rfl

/-- **Appendix A** (Bielous–Meir): over the integer grid the realized
better-response path terminates — at its final state no proxy has an integer
better response.  Non-winners cannot change the outcome at all, even with
real reports; the winner's integer deviations either keep the outcome at 5
or hand the win to the runner-up at 4, which single-peakedness at peak 12
refutes. -/
theorem appendixA_integer_pne (j : Fin 5) (y : ℤ) :
    ¬ IsBetterResponse appendixAPeaks appendixAFollowers appendixAState6 j
      (y : ℝ) := by
  rintro ⟨hchange, hnr⟩
  by_cases hj4 : j = 4
  · subst hj4
    by_cases hy5 : (y : ℝ) = 5
    · rw [hy5, show Function.update appendixAState6 4 (5:ℝ) = appendixAState6
        from Function.update_eq_self 4 appendixAState6] at hchange
      exact hchange rfl
    · have hyz : y ≠ 5 := fun h => hy5 (by exact_mod_cast h)
      have habs : (1:ℝ) ≤ |(y:ℝ) - 5| := by
        have h1 : (1:ℤ) ≤ |y - 5| := Int.one_le_abs (by omega)
        have h2 : |(y:ℝ) - 5| = ((|y - 5| : ℤ) : ℝ) := by
          push_cast
          rfl
        rw [h2]
        exact_mod_cast h1
      have hdel : delegate (Function.update appendixAState6 4 (y:ℝ)) 5 = 0 := by
        refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_)
          (fun i hi => ?_)
        · rw [Function.update_of_ne (show (0:Fin 5) ≠ 4 by decide),
            show appendixAState6 0 = 4 from rfl,
            show |(4:ℝ) - 5| = 1 by norm_num]
          by_cases hi4 : i = 4
          · rw [hi4, Function.update_self]
            exact habs
          · rw [Function.update_of_ne hi4]
            fin_cases i
            · norm_num [appendixAState6]
            · norm_num [appendixAState6]
            · norm_num [appendixAState6]
            · norm_num [appendixAState6]
            · exact absurd rfl hi4
        · exact absurd hi (Fin.not_lt_zero i)
      have hout : outcome (Function.update appendixAState6 4 (y:ℝ))
          appendixAFollowers = 4 := by
        unfold outcome winner
        rw [appA_s6_median_pinned 4 (y:ℝ), hdel,
          Function.update_of_ne (show (0:Fin 5) ≠ 4 by decide)]
        rfl
      rw [hout, appA_outcome_s6] at hnr
      exact hnr (Or.inr ⟨by norm_num, by norm_num [appendixAPeaks]⟩)
  · exact hchange
      ((appA_s6_outcome_pinned j hj4 (y:ℝ)).trans appA_outcome_s6.symm)

/-- Over the reals the final state is *not* an equilibrium: the winner can
nudge inside the runner-up's distance, so the discreteness of the grid is
essential to Appendix A's equilibrium claim. -/
theorem appendixA_not_pne_real :
    IsBetterResponse appendixAPeaks appendixAFollowers appendixAState6 4
      (11 / 2) := by
  refine isBetterResponse_of_prefers ?_
  have hdel : delegate (Function.update appendixAState6 4 (11 / 2 : ℝ)) 5
      = 4 := by
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rw [Function.update_self, show |(11 / 2 : ℝ) - 5| = 1 / 2 by norm_num,
      Function.update_of_ne hi]
    fin_cases i
    · norm_num [appendixAState6]
    · norm_num [appendixAState6]
    · norm_num [appendixAState6]
    · norm_num [appendixAState6]
    · exact absurd rfl hi
  have hout : outcome (Function.update appendixAState6 4 (11 / 2 : ℝ))
      appendixAFollowers = 11 / 2 := by
    unfold outcome winner
    rw [appA_s6_median_pinned 4 (11 / 2 : ℝ), hdel, Function.update_self]
  unfold Prefers
  rw [hout, appA_outcome_s6]
  norm_num [appendixAPeaks]

/-- Appendix A, the social-cost comparison: the truthful outcome −11 costs
84 and the final outcome 5 costs 86 — the better-response dynamics ends at a
socially worse outcome, although 5 is strictly closer to the true median
than −11 is. -/
theorem appendixA_socialCost :
    socialCost appendixAPeaks appendixAFollowers (-11) = 84
      ∧ socialCost appendixAPeaks appendixAFollowers 5 = 86 := by
  constructor <;>
  · unfold socialCost
    rw [Fintype.sum_sum_type]
    simp only [Fin.sum_univ_five, Fin.sum_univ_four]
    norm_num [allPos, appendixAPeaks, appendixAFollowers]

end ProxyVoting

end GameTheory
