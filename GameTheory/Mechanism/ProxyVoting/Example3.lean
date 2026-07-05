/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.PartialInformation
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bielous--Meir Example 3

The paper's Example 3 is an infinite monotone better-response dynamics that
does not converge to the true median.  This file formalizes the example in
the actual proxy-voting model.  There are two proxies, with truthful positions
`-1` and `3/2`, and one follower at `0`.  Starting from truth, the losing
proxy alternately moves to the opposite side's dyadic distance

`δ n = 1/2 + (1/2)^(n+1)`,

so the selected outcome alternates sides while its distance from the true
median stays strictly above `1/2`.
-/

namespace GameTheory

namespace ProxyVoting

open Filter

/-! ## The instance and dyadic path -/

/-- Example 3 proxy peaks: the left proxy is at `-1`, the right proxy at
`3/2`. -/
noncomputable def example3Peaks : Fin 2 → ℝ
  | 0 => -1
  | 1 => 3 / 2

/-- Example 3's single follower is at the true median `0`. -/
def example3Followers : Unit → ℝ := fun _ => 0

/-- The paper's dyadic distances from the true median: `1, 3/4, 5/8, ...`,
converging to `1/2`. -/
noncomputable def example3Delta (n : ℕ) : ℝ :=
  (1 : ℝ) / 2 + ((1 : ℝ) / 2) ^ (n + 1)

/-- The Example 3 state sequence.  At even times the left proxy wins at
`-δ t`; at odd times the right proxy wins at `δ t`.  The non-winning report is
the previous winning report, except at time `0`, where the state is truthful. -/
noncomputable def example3State (t : ℕ) : Fin 2 → ℝ
  | 0 => if Even t then -example3Delta t else -example3Delta (t - 1)
  | 1 => if Even t then if t = 0 then 3 / 2 else example3Delta (t - 1)
      else example3Delta t

private theorem example3Delta_zero : example3Delta 0 = 1 := by
  norm_num [example3Delta]

private theorem example3Delta_pos (n : ℕ) : 0 < example3Delta n := by
  unfold example3Delta
  positivity

private theorem example3Delta_half_lt (n : ℕ) : (1 : ℝ) / 2 < example3Delta n := by
  unfold example3Delta
  have hpow : 0 < ((1 : ℝ) / 2) ^ (n + 1) := by positivity
  linarith

private theorem example3Delta_lt_prev {n : ℕ} (hn : 0 < n) :
    example3Delta n < example3Delta (n - 1) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      unfold example3Delta
      rw [Nat.succ_sub_one]
      have hpow : ((1 : ℝ) / 2) ^ (n + 2) < ((1 : ℝ) / 2) ^ (n + 1) := by
        rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
        have hpos : 0 < ((1 : ℝ) / 2) ^ (n + 1) := by positivity
        nlinarith
      linarith

private theorem example3Delta_le_one (n : ℕ) : example3Delta n ≤ 1 := by
  induction n with
  | zero => norm_num [example3Delta]
  | succ n ih =>
      exact (le_of_lt (example3Delta_lt_prev (Nat.succ_pos n))).trans ih

private theorem example3_cumWeight_zero :
    Math.cumWeight (allPos example3Peaks example3Followers) (fun _ => 1) 0 = 2 := by
  rw [Math.cumWeight]
  have hfilter :
      (Finset.univ.filter fun x : Fin 2 ⊕ Unit =>
        allPos example3Peaks example3Followers x ≤ 0)
        = ({Sum.inl (0 : Fin 2), Sum.inr ()} : Finset (Fin 2 ⊕ Unit)) := by
    ext x
    cases x with
    | inl j => fin_cases j <;> simp [allPos, example3Peaks]
    | inr u => cases u; simp [allPos, example3Followers]
  rw [hfilter]
  decide

private theorem example3_cumWeight_neg_one :
    Math.cumWeight (allPos example3Peaks example3Followers) (fun _ => 1) (-1) = 1 := by
  rw [Math.cumWeight]
  have hfilter :
      (Finset.univ.filter fun x : Fin 2 ⊕ Unit =>
        allPos example3Peaks example3Followers x ≤ -1)
        = ({Sum.inl (0 : Fin 2)} : Finset (Fin 2 ⊕ Unit)) := by
    ext x
    cases x with
    | inl j => fin_cases j <;> norm_num [allPos, example3Peaks]
    | inr u => cases u; simp [allPos, example3Followers]
  rw [hfilter]
  decide

private theorem example3_socialMedian_truth :
    socialMedian example3Peaks example3Followers = 0 := by
  change Math.weightedMedian (allPos example3Peaks example3Followers) (fun _ => 1) = 0
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image_of_mem (allPos example3Peaks example3Followers)
      (Finset.mem_univ (Sum.inr ()))
  · rw [example3_cumWeight_zero]
    norm_num [Math.totalWeight]
  · intro q hq hq0
    rw [Finset.mem_image] at hq
    obtain ⟨a, -, rfl⟩ := hq
    cases a with
    | inl j =>
        fin_cases j
        · change 2 *
            Math.cumWeight (allPos example3Peaks example3Followers) (fun _ => 1) (-1)
              < Math.totalWeight (fun _ : Fin 2 ⊕ Unit => 1)
          rw [example3_cumWeight_neg_one]
          norm_num [Math.totalWeight]
        · norm_num [allPos, example3Peaks] at hq0
    | inr u =>
        norm_num [allPos, example3Followers] at hq0

private theorem example3_state_zero :
    example3State 0 = example3Peaks := by
  funext j
  fin_cases j <;> norm_num [example3State, example3Peaks, example3Delta_zero]

private theorem example3State_left_neg (t : ℕ) : example3State t 0 < 0 := by
  by_cases ht : Even t
  · simp [example3State, ht, example3Delta_pos]
  · simp [example3State, ht, example3Delta_pos]

private theorem example3State_right_pos (t : ℕ) : 0 < example3State t 1 := by
  by_cases ht : Even t
  · by_cases h0 : t = 0
    · simp [example3State, h0]
    · simp [example3State, ht, h0, example3Delta_pos]
  · simp [example3State, ht, example3Delta_pos]

private theorem example3_socialMedian_state (t : ℕ) :
    socialMedian (example3State t) example3Followers = 0 := by
  rw [socialMedian_eq_of_weakMonotoneReports (pp := example3Peaks)
    (q := example3Followers) (s := example3State t)]
  · exact example3_socialMedian_truth
  · intro j hj
    rw [example3_socialMedian_truth] at hj ⊢
    fin_cases j
    · exact le_of_lt (example3State_left_neg t)
    · norm_num [example3Peaks] at hj
  · intro j hj
    rw [example3_socialMedian_truth] at hj ⊢
    fin_cases j
    · norm_num [example3Peaks] at hj
    · exact le_of_lt (example3State_right_pos t)

/-! ## Winners and outcomes -/

private theorem example3_delegate_even {t : ℕ} (ht : Even t) :
    delegate (example3State t) 0 = 0 := by
  have h2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  refine delegate_eq_of_forall_lt fun j hj => ?_
  rcases h2 j with h0j | h1j
  · exact absurd h0j hj
  · rw [h1j]
    by_cases h0 : t = 0
    · norm_num [example3State, h0, example3Delta_zero]
    · have hpos : 0 < t := Nat.pos_of_ne_zero h0
      have hlt := example3Delta_lt_prev hpos
      rw [show example3State t 0 = -example3Delta t by simp [example3State, ht],
        show example3State t 1 = example3Delta (t - 1) by simp [example3State, ht, h0]]
      rw [abs_of_neg (by linarith [example3Delta_pos t] : -example3Delta t - 0 < 0),
        abs_of_pos (by linarith [example3Delta_pos (t - 1)] :
          example3Delta (t - 1) - 0 > 0)]
      linarith

private theorem example3_delegate_odd {t : ℕ} (ht : ¬ Even t) :
    delegate (example3State t) 0 = 1 := by
  have h2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  refine delegate_eq_of_forall_lt fun j hj => ?_
  rcases h2 j with h0j | h1j
  · rw [h0j]
    have hodd : Odd t := Nat.not_even_iff_odd.mp ht
    have hpos : 0 < t := Nat.pos_of_ne_zero (fun h0 => by
      subst h0
      exact ht ⟨0, rfl⟩)
    have hlt := example3Delta_lt_prev hpos
    rw [show example3State t 0 = -example3Delta (t - 1) by simp [example3State, ht],
      show example3State t 1 = example3Delta t by simp [example3State, ht]]
    rw [abs_of_pos (by linarith [example3Delta_pos t] : example3Delta t - 0 > 0),
      abs_of_neg (by linarith [example3Delta_pos (t - 1)] :
        -example3Delta (t - 1) - 0 < 0)]
    linarith
  · exact absurd h1j hj

private theorem example3_winner_even {t : ℕ} (ht : Even t) :
    winner (example3State t) example3Followers = 0 := by
  unfold winner
  rw [example3_socialMedian_state t]
  exact example3_delegate_even ht

private theorem example3_winner_odd {t : ℕ} (ht : ¬ Even t) :
    winner (example3State t) example3Followers = 1 := by
  unfold winner
  rw [example3_socialMedian_state t]
  exact example3_delegate_odd ht

theorem example3_outcome_even {t : ℕ} (ht : Even t) :
    outcome (example3State t) example3Followers = -example3Delta t := by
  unfold outcome
  rw [example3_winner_even ht]
  simp [example3State, ht]

theorem example3_outcome_odd {t : ℕ} (ht : ¬ Even t) :
    outcome (example3State t) example3Followers = example3Delta t := by
  unfold outcome
  rw [example3_winner_odd ht]
  simp [example3State, ht]

theorem example3_abs_outcome :
    |outcome (example3State t) example3Followers
        - socialMedian example3Peaks example3Followers| = example3Delta t := by
  rw [example3_socialMedian_truth]
  by_cases ht : Even t
  · rw [example3_outcome_even ht]
    rw [abs_of_neg (by linarith [example3Delta_pos t])]
    ring
  · rw [example3_outcome_odd ht]
    rw [sub_zero, abs_of_pos (example3Delta_pos t)]

/-! ## Each step is a monotone better response -/

private theorem example3State_succ_even {t : ℕ} (ht : Even t) :
    example3State (t + 1) = Function.update (example3State t) 1 (example3Delta (t + 1)) := by
  funext j
  have ht1 : ¬ Even (t + 1) := by
    rw [Nat.even_add_one]
    exact not_not.mpr ht
  fin_cases j
  · change example3State (t + 1) 0 =
      Function.update (example3State t) 1 (example3Delta (t + 1)) 0
    rw [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    change (if Even (t + 1) then -example3Delta (t + 1)
        else -example3Delta (t + 1 - 1)) = example3State t 0
    rw [if_neg ht1, show t + 1 - 1 = t by omega]
    simp [example3State, ht]
  · change example3State (t + 1) 1 =
      Function.update (example3State t) 1 (example3Delta (t + 1)) 1
    rw [Function.update_self]
    change (if Even (t + 1) then if t + 1 = 0 then 3 / 2 else example3Delta (t + 1 - 1)
        else example3Delta (t + 1)) = example3Delta (t + 1)
    rw [if_neg ht1]

private theorem example3State_succ_odd {t : ℕ} (ht : ¬ Even t) :
    example3State (t + 1) = Function.update (example3State t) 0 (-example3Delta (t + 1)) := by
  funext j
  have ht1 : Even (t + 1) := by
    rw [Nat.even_add_one]
    exact ht
  fin_cases j
  · change example3State (t + 1) 0 =
      Function.update (example3State t) 0 (-example3Delta (t + 1)) 0
    rw [Function.update_self]
    change (if Even (t + 1) then -example3Delta (t + 1)
        else -example3Delta (t + 1 - 1)) = -example3Delta (t + 1)
    rw [if_pos ht1]
  · change example3State (t + 1) 1 =
      Function.update (example3State t) 0 (-example3Delta (t + 1)) 1
    rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
    change (if Even (t + 1) then if t + 1 = 0 then 3 / 2 else example3Delta (t + 1 - 1)
        else example3Delta (t + 1)) = example3State t 1
    rw [if_pos ht1, if_neg (by omega : t + 1 ≠ 0), show t + 1 - 1 = t by omega]
    simp [example3State, ht]

private theorem example3_monotone_right {t : ℕ} :
    MonotoneReport example3Peaks example3Followers 1 (example3Delta (t + 1)) := by
  rw [MonotoneReport, example3_socialMedian_truth]
  norm_num [example3Peaks, example3Delta_pos]

private theorem example3_monotone_left {t : ℕ} :
    MonotoneReport example3Peaks example3Followers 0 (-example3Delta (t + 1)) := by
  rw [MonotoneReport, example3_socialMedian_truth]
  norm_num [example3Peaks, example3Delta_pos]

private theorem example3_better_right {t : ℕ} (ht : Even t) :
    IsBetterResponse example3Peaks example3Followers (example3State t) 1
      (example3Delta (t + 1)) := by
  refine isBetterResponse_of_prefers ?_
  rw [Prefers, ← example3State_succ_even ht]
  have ht1 : ¬ Even (t + 1) := by
    rw [Nat.even_add_one]
    exact not_not.mpr ht
  rw [example3_outcome_odd ht1, example3_outcome_even ht]
  have hlt : example3Delta (t + 1) < example3Delta t :=
    example3Delta_lt_prev (Nat.succ_pos t)
  have hpeak : example3Peaks 1 = (3 : ℝ) / 2 := rfl
  rw [hpeak]
  rw [abs_of_nonpos (by linarith [example3Delta_le_one (t + 1)] :
      example3Delta (t + 1) - 3 / 2 ≤ 0),
    abs_of_nonpos (by linarith [example3Delta_pos t] :
      -example3Delta t - 3 / 2 ≤ 0)]
  linarith [example3Delta_half_lt (t + 1), hlt]

private theorem example3_better_left {t : ℕ} (ht : ¬ Even t) :
    IsBetterResponse example3Peaks example3Followers (example3State t) 0
      (-example3Delta (t + 1)) := by
  refine isBetterResponse_of_prefers ?_
  rw [Prefers, ← example3State_succ_odd ht]
  have ht1 : Even (t + 1) := by
    rw [Nat.even_add_one]
    exact ht
  rw [example3_outcome_even ht1, example3_outcome_odd ht]
  have hlt : example3Delta (t + 1) < example3Delta t :=
    example3Delta_lt_prev (Nat.succ_pos t)
  have hpeak : example3Peaks 0 = (-1 : ℝ) := rfl
  rw [hpeak]
  rw [abs_of_nonneg (by linarith [example3Delta_le_one (t + 1)] :
      0 ≤ -example3Delta (t + 1) - (-1)),
    abs_of_nonneg (by linarith [example3Delta_half_lt t] :
      0 ≤ example3Delta t - (-1))]
  linarith [example3Delta_half_lt t, example3Delta_pos (t + 1), hlt]

/-- Example 3, mechanized as an actual monotone better-response dynamics from
truth. -/
theorem example3_isMonotoneDynamics :
    IsMonotoneDynamics example3Peaks example3Followers example3State := by
  constructor
  · exact example3_state_zero
  · intro t
    by_cases ht : Even t
    · left
      refine ⟨1, example3Delta (t + 1), example3_better_right ht,
        example3_monotone_right, ?_⟩
      exact example3State_succ_even ht
    · left
      refine ⟨0, -example3Delta (t + 1), example3_better_left ht,
        example3_monotone_left, ?_⟩
      exact example3State_succ_odd ht

/-- At an even Example 3 state, the next right-proxy move is strong-monotone
over the winner-poll information set: every profile consistent with the left
proxy winning has median left of the next right report. -/
private theorem example3_strongMonotone_right {t : ℕ} (ht : Even t) :
    StrongMonotoneOver (example3State t)
      (winnerInfoSet (F := Unit) (example3State t)
        (winner (example3State t) example3Followers))
      1 (example3Delta (t + 1)) := by
  intro q hq
  have hwtrue : winner (example3State t) example3Followers = 0 :=
    example3_winner_even ht
  have hwin : winner (example3State t) q = 0 := by
    simpa [winnerInfoSet, hwtrue] using hq
  have hdel : delegate (example3State t) (socialMedian (example3State t) q) = 0 := by
    simpa [winner] using hwin
  have hlt : example3State t 0 < example3State t 1 := by
    linarith [example3State_left_neg t, example3State_right_pos t]
  have hd := delegate_dist_le (example3State t) (socialMedian (example3State t) q) 1
  rw [hdel] at hd
  have hmed_le_mid :
      socialMedian (example3State t) q ≤
        (example3State t 0 + example3State t 1) / 2 :=
    (abs_left_sub_le_abs_right_sub_iff hlt).mp hd
  have hmid_lt_next :
      (example3State t 0 + example3State t 1) / 2 < example3Delta (t + 1) := by
    by_cases h0 : t = 0
    · subst h0
      norm_num [example3State, example3Delta]
    · rw [show example3State t 0 = -example3Delta t by simp [example3State, ht],
        show example3State t 1 = example3Delta (t - 1) by simp [example3State, ht, h0]]
      have hprev : example3Delta (t - 1) ≤ 1 := example3Delta_le_one (t - 1)
      have hnext : (1 : ℝ) / 2 < example3Delta (t + 1) :=
        example3Delta_half_lt (t + 1)
      have hpos : 0 < example3Delta t := example3Delta_pos t
      linarith
  have hmed_lt_next : socialMedian (example3State t) q < example3Delta (t + 1) :=
    lt_of_le_of_lt hmed_le_mid hmid_lt_next
  have hmid_lt_right : (example3State t 0 + example3State t 1) / 2
      < example3State t 1 := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro hright_lt_med
    exfalso
    linarith
  · intro _
    exact hmed_lt_next
  · intro heq
    exfalso
    linarith

/-- Odd-state mirror of `example3_strongMonotone_right`. -/
private theorem example3_strongMonotone_left {t : ℕ} (ht : ¬ Even t) :
    StrongMonotoneOver (example3State t)
      (winnerInfoSet (F := Unit) (example3State t)
        (winner (example3State t) example3Followers))
      0 (-example3Delta (t + 1)) := by
  intro q hq
  have hwtrue : winner (example3State t) example3Followers = 1 :=
    example3_winner_odd ht
  have hwin : winner (example3State t) q = 1 := by
    simpa [winnerInfoSet, hwtrue] using hq
  have hdel : delegate (example3State t) (socialMedian (example3State t) q) = 1 := by
    simpa [winner] using hwin
  have hlt : example3State t 0 < example3State t 1 := by
    linarith [example3State_left_neg t, example3State_right_pos t]
  have hd := delegate_dist_le (example3State t) (socialMedian (example3State t) q) 0
  rw [hdel] at hd
  have hmid_le_med :
      (example3State t 0 + example3State t 1) / 2
        ≤ socialMedian (example3State t) q :=
    (abs_right_sub_le_abs_left_sub_iff hlt).mp hd
  have hnext_lt_mid :
      -example3Delta (t + 1) < (example3State t 0 + example3State t 1) / 2 := by
    rw [show example3State t 0 = -example3Delta (t - 1) by simp [example3State, ht],
      show example3State t 1 = example3Delta t by simp [example3State, ht]]
    have hprev : example3Delta (t - 1) ≤ 1 := example3Delta_le_one (t - 1)
    have hnext : (1 : ℝ) / 2 < example3Delta (t + 1) :=
      example3Delta_half_lt (t + 1)
    have hpos : 0 < example3Delta t := example3Delta_pos t
    linarith
  have hnext_lt_med : -example3Delta (t + 1) < socialMedian (example3State t) q :=
    lt_of_lt_of_le hnext_lt_mid hmid_le_med
  have hleft_lt_mid : example3State t 0
      < (example3State t 0 + example3State t 1) / 2 := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact hnext_lt_med
  · intro hmed_lt_left
    exfalso
    linarith
  · intro heq
    exfalso
    linarith

/-- Example 3 is already a strong-monotone dynamics for the winner-poll
partial-information set used in section 5.  Strong monotonicity of every move
therefore does not imply convergence of outcomes to the preserved median; a
contraction/decrease condition is required.  This does not by itself refute
the stronger minimax-regret headline; that would also require showing these
moves are minimax-regret reports. -/
theorem example3_isStrongMonotoneDynamics :
    IsStrongMonotoneDynamics example3Followers example3State := by
  intro t
  by_cases ht : Even t
  · left
    exact ⟨1, example3Delta (t + 1), example3_strongMonotone_right ht,
      example3State_succ_even ht⟩
  · left
    exact ⟨0, -example3Delta (t + 1), example3_strongMonotone_left ht,
      example3State_succ_odd ht⟩

/-- Example 3 preserves the population median at every state.  Thus median
invariance by itself is not a convergence principle; the non-convergence
theorem below is the missing half. -/
theorem example3_socialMedian_preserved (t : ℕ) :
    socialMedian (example3State t) example3Followers
      = socialMedian (example3State 0) example3Followers := by
  exact (socialMedian_eq_of_isMonotoneDynamics example3_isMonotoneDynamics t).trans
    (socialMedian_eq_of_isMonotoneDynamics example3_isMonotoneDynamics 0).symm

/-! ## Non-convergence to the true median -/

theorem example3_delta_tendsto :
    Tendsto example3Delta atTop (nhds ((1 : ℝ) / 2)) := by
  unfold example3Delta
  have hpow : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1 : ℝ) / 2)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)
  simpa using (hpow.const_add ((1 : ℝ) / 2))

/-- The Example 3 outcome does not converge to the true median.  In fact, its
distance from the true median is always strictly above `1/2`. -/
theorem example3_not_tendsto_socialMedian :
    ¬ Tendsto (fun t => outcome (example3State t) example3Followers) atTop
        (nhds (socialMedian example3Peaks example3Followers)) := by
  intro h
  have hdist : Tendsto
      (fun t => |outcome (example3State t) example3Followers
        - socialMedian example3Peaks example3Followers|) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    simpa [Real.norm_eq_abs] using h
  have hlim : Tendsto
      (fun t => |outcome (example3State t) example3Followers
        - socialMedian example3Peaks example3Followers|) atTop
        (nhds ((1 : ℝ) / 2)) := by
    simpa [example3_abs_outcome] using example3_delta_tendsto
  have huniq := tendsto_nhds_unique hdist hlim
  norm_num at huniq

/-- Example 3 also does not converge to the initial state's median.  This is
the direct counterexample shape for any partial-information argument that has
only proved median invariance and lacks a preserved contraction/decrease
hypothesis. -/
theorem example3_not_tendsto_initial_socialMedian :
    ¬ Tendsto (fun t => outcome (example3State t) example3Followers) atTop
        (nhds (socialMedian (example3State 0) example3Followers)) := by
  intro h
  exact example3_not_tendsto_socialMedian
    (by
      simpa [socialMedian_eq_of_isMonotoneDynamics example3_isMonotoneDynamics 0] using h)

/-- Compact form: the Example 3 dynamics has invariant median but its
outcome does not converge to that invariant median. -/
theorem example3_median_preserved_and_not_tendsto :
    (∀ t, socialMedian (example3State t) example3Followers
        = socialMedian (example3State 0) example3Followers)
      ∧ ¬ Tendsto (fun t => outcome (example3State t) example3Followers) atTop
          (nhds (socialMedian (example3State 0) example3Followers)) :=
  ⟨example3_socialMedian_preserved, example3_not_tendsto_initial_socialMedian⟩

/-- Counterexample to the monotonicity-only route: even for the winner-poll
partial-information set, strong monotonicity of every move does not imply
convergence of outcomes to the preserved median; a contraction/decrease
condition is required, as in the convergence theorems in
`PartialInformation`.  The minimax endpoint analogue is separated out in
`Counterexamples.minimaxTrap_minimaxRegretInfo_not_tendsto`; Example 3 itself
only refutes the monotonicity-only route. -/
theorem example3_strongMonotone_not_tendsto :
    IsStrongMonotoneDynamics example3Followers example3State
      ∧ ¬ Tendsto (fun t => outcome (example3State t) example3Followers) atTop
          (nhds (socialMedian (example3State 0) example3Followers)) :=
  ⟨example3_isStrongMonotoneDynamics, example3_not_tendsto_initial_socialMedian⟩

/-- Example 3 does not even satisfy the identity-window fixed-factor
contraction condition.  If it did, the abstract windowed-contraction theorem
would force the outcome distance to tend to zero, contradicting the proved
limit `1/2`. -/
theorem example3_no_identity_windowed_contraction :
    let d : ℕ → ℝ := fun t =>
      |outcome (example3State t) example3Followers
        - socialMedian (example3State t) example3Followers|
    ∀ α, 0 ≤ α → α < 1 →
      ¬ (∀ k, ∃ k', k ≤ k' ∧ d (k' + 1) ≤ α * d k') := by
  intro d α hα0 hα1 hbig
  have hd_eq : ∀ t, d t = example3Delta t := by
    intro t
    dsimp [d]
    rw [example3_socialMedian_preserved t,
      socialMedian_eq_of_isMonotoneDynamics example3_isMonotoneDynamics 0]
    exact example3_abs_outcome
  have hd0 : ∀ t, 0 ≤ d t := fun t => by
    rw [hd_eq t]
    exact le_of_lt (example3Delta_pos t)
  have hwindow : ∀ k u, id k ≤ u → u ≤ id (k + 1) → d u ≤ d (id k) := by
    intro k u hku huk
    change k ≤ u at hku
    change u ≤ k + 1 at huk
    change d u ≤ d k
    rw [hd_eq u, hd_eq k]
    rcases eq_or_lt_of_le hku with hku_eq | hku_lt
    · subst u
      rfl
    · have hu : u = k + 1 := by omega
      subst u
      exact le_of_lt (example3Delta_lt_prev (Nat.succ_pos k))
  have htop : Tendsto (id : ℕ → ℕ) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => ha⟩
  have hzero : Tendsto d atTop (nhds 0) :=
    Math.tendsto_zero_of_windowed_contraction
      (d := d) (b := id) (α := α) hd0 rfl monotone_id htop hwindow hα0 hα1
      (by simpa using hbig)
  have hlim : Tendsto d atTop (nhds ((1 : ℝ) / 2)) := by
    have hd_fun : d = example3Delta := by
      funext t
      exact hd_eq t
    rw [hd_fun]
    exact example3_delta_tendsto
  have huniq := tendsto_nhds_unique hzero hlim
  norm_num at huniq

end ProxyVoting

end GameTheory
