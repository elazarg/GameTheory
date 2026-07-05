/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.PartialInformation
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Appendix B: dominating dynamics can converge to a worse social outcome

The Bielous–Meir Appendix B configuration: proxies with peaks −30 and 90 and
followers at −50, 0, 10, so the true median is 0 and the truthful outcome is
−30 with social cost 210.  Reporting 29 is a dominating manipulation for the
right proxy, then 25 for the left proxy.  At the resulting state the left
proxy has no dominating manipulation at all, while the right proxy retains
dominating manipulations that never move the realized outcome — the
dominating dynamics converges (in outcome) to 25, with social cost 235,
strictly worse than truth even though 25 is strictly closer to the true
median than −30 is. -/

namespace GameTheory

namespace ProxyVoting

/-- Peaks for the Appendix B configuration. -/
def appendixBPeaks : Fin 2 → ℝ
  | 0 => -30
  | 1 => 90

/-- Followers for the Appendix B configuration; the true median is 0. -/
def appendixBFollowers : Fin 3 → ℝ
  | 0 => -50
  | 1 => 0
  | 2 => 10

/-- The state after the right proxy's dominating manipulation to 29. -/
def appendixBState1 : Fin 2 → ℝ
  | 0 => -30
  | 1 => 29

/-- The state after the left proxy's dominating manipulation to 25. -/
def appendixBState2 : Fin 2 → ℝ
  | 0 => 25
  | 1 => 29

/-- The continuing Appendix B states: the left proxy remains at 25, while the
right proxy reports `y`. -/
def appendixBStateY (y : ℝ) : Fin 2 → ℝ
  | 0 => 25
  | 1 => y

/-- The information accumulated along the realized play: the winner
observations at the truthful state and after each manipulation. -/
def appendixBHistory : Set (Fin 3 → ℝ) :=
  winnerInfoSet appendixBPeaks 0 ∩ winnerInfoSet appendixBState1 1
    ∩ winnerInfoSet appendixBState2 0

/-- The accumulated history after additionally observing that the left proxy
still wins at the current state `(25,y)`. -/
def appendixBHistoryAt (y : ℝ) : Set (Fin 3 → ℝ) :=
  appendixBHistory ∩ winnerInfoSet (appendixBStateY y) 0

private theorem appB_card : Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

private theorem appB_update1 :
    Function.update appendixBPeaks 1 29 = appendixBState1 := by
  funext i
  fin_cases i <;> simp [appendixBPeaks, appendixBState1]

private theorem appB_update2 :
    Function.update appendixBState1 0 25 = appendixBState2 := by
  funext i
  fin_cases i <;> simp [appendixBState1, appendixBState2]

/-- Two-proxy delegation, left version: index 0 wins weak ties. -/
private theorem delegate_pair_zero {s : Fin 2 → ℝ} {m : ℝ}
    (h : |s 0 - m| ≤ |s 1 - m|) : delegate s m = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro k
    fin_cases k
    · exact le_rfl
    · exact h
  · intro b _
    exact Fin.zero_le b

/-- Two-proxy delegation, right version: index 1 needs a strict win. -/
private theorem delegate_pair_one {s : Fin 2 → ℝ} {m : ℝ}
    (h : |s 1 - m| < |s 0 - m|) : delegate s m = 1 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  rcases h2 (delegate s m) with hd | hd
  · have hle := delegate_dist_le s m 1
    rw [hd] at hle
    exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)
  · exact hd

/-- The outcome of a two-proxy state is one of the two reports. -/
private theorem outcome_pair (s : Fin 2 → ℝ) (q : Fin 3 → ℝ) :
    outcome s q = s 0 ∨ outcome s q = s 1 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  unfold outcome
  rcases h2 (winner s q) with hw | hw <;> rw [hw]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Point-mass profiles with common position in `(−1/2, 27]` are consistent
with the entire observation history. -/
private theorem appB_const_mem_history {μ : ℝ} (h1 : -(1 / 2 : ℝ) < μ)
    (h2 : μ ≤ 27) : (fun _ : Fin 3 => μ) ∈ appendixBHistory := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [winnerInfoSet, Set.mem_setOf_eq]
    unfold winner
    rw [socialMedian_const appB_card]
    refine delegate_pair_zero ?_
    have e0 : appendixBPeaks 0 = -30 := rfl
    have e1 : appendixBPeaks 1 = 90 := rfl
    rw [e0, e1, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · simp only [winnerInfoSet, Set.mem_setOf_eq]
    unfold winner
    rw [socialMedian_const appB_card]
    refine delegate_pair_one ?_
    have e0 : appendixBState1 0 = -30 := rfl
    have e1 : appendixBState1 1 = 29 := rfl
    rw [e0, e1, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · simp only [winnerInfoSet, Set.mem_setOf_eq]
    unfold winner
    rw [socialMedian_const appB_card]
    refine delegate_pair_zero ?_
    have e0 : appendixBState2 0 = 25 := rfl
    have e1 : appendixBState2 1 = 29 := rfl
    rw [e0, e1]
    rcases le_or_gt μ 25 with hc | hc
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith

private theorem appB_truth_cum_zero :
    Math.cumWeight (allPos appendixBPeaks appendixBFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBPeaks, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_truth_cum_neg30 :
    Math.cumWeight (allPos appendixBPeaks appendixBFollowers) (fun _ => 1) (-30)
      = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBPeaks, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_truth_cum_neg50 :
    Math.cumWeight (allPos appendixBPeaks appendixBFollowers) (fun _ => 1) (-50)
      = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBPeaks, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_median_truth :
    socialMedian appendixBPeaks appendixBFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 1, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appB_truth_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixBPeaks appendixBFollowers)
            (fun _ => 1) (-30) < Math.totalWeight fun _ => 1
          rw [appB_truth_cum_neg30, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixBPeaks] at hzlt
    | inr f =>
        fin_cases f
        · change 2 * Math.cumWeight (allPos appendixBPeaks appendixBFollowers)
            (fun _ => 1) (-50) < Math.totalWeight fun _ => 1
          rw [appB_truth_cum_neg50, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixBFollowers] at hzlt
        · norm_num [allPos, appendixBFollowers] at hzlt

private theorem appB_median_state1 :
    socialMedian appendixBState1 appendixBFollowers = 0 := by
  rw [← appB_update1,
    socialMedian_update_eq_of_proxy_gt
      (by rw [appB_median_truth]; norm_num [appendixBPeaks])
      (by rw [appB_median_truth]; norm_num),
    appB_median_truth]

private theorem appB_state2_cum_ten :
    Math.cumWeight (allPos appendixBState2 appendixBFollowers) (fun _ => 1) 10
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBState2, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_state2_cum_zero :
    Math.cumWeight (allPos appendixBState2 appendixBFollowers) (fun _ => 1) 0
      = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBState2, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_state2_cum_neg50 :
    Math.cumWeight (allPos appendixBState2 appendixBFollowers) (fun _ => 1) (-50)
      = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBState2, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_median_state2 :
    socialMedian appendixBState2 appendixBFollowers = 10 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 2, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appB_state2_cum_ten]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j <;> norm_num [allPos, appendixBState2] at hzlt
    | inr f =>
        fin_cases f
        · change 2 * Math.cumWeight (allPos appendixBState2 appendixBFollowers)
            (fun _ => 1) (-50) < Math.totalWeight fun _ => 1
          rw [appB_state2_cum_neg50, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · change 2 * Math.cumWeight (allPos appendixBState2 appendixBFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [appB_state2_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixBFollowers] at hzlt

/-- Appendix B, the realized play: the truthful outcome is −30, then 29
after the right proxy's manipulation, then 25 after the left proxy's. -/
theorem appendixB_realized_outcomes :
    outcome appendixBPeaks appendixBFollowers = -30
      ∧ outcome appendixBState1 appendixBFollowers = 29
      ∧ outcome appendixBState2 appendixBFollowers = 25 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold outcome winner
    rw [appB_median_truth, delegate_pair_zero (by norm_num [appendixBPeaks])]
    rfl
  · unfold outcome winner
    rw [appB_median_state1, delegate_pair_one (by norm_num [appendixBState1])]
    rfl
  · unfold outcome winner
    rw [appB_median_state2, delegate_pair_zero (by norm_num [appendixBState2])]
    rfl

/-- Appendix B, first move: at the truthful state with the left proxy
observed winning, reporting 29 is a dominating manipulation for the right
proxy. -/
theorem appendixB_right_dominating_29 :
    IsDominatingManipulation (Fin 3) appendixBPeaks appendixBPeaks 0 1 29 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hwq : winner appendixBPeaks q = 0 := hq
    have hout : outcome appendixBPeaks q = -30 := by
      unfold outcome
      rw [hwq]
      rfl
    rw [appB_update1, hout]
    rcases outcome_pair appendixBState1 q with h | h <;> rw [h] <;>
      norm_num [appendixBState1, appendixBPeaks]
  · refine ⟨fun _ : Fin 3 => (0:ℝ),
      (appB_const_mem_history (by norm_num) (by norm_num)).1.1, ?_⟩
    have hnew : outcome (Function.update appendixBPeaks 1 29)
        (fun _ : Fin 3 => (0:ℝ)) = 29 := by
      rw [appB_update1]
      unfold outcome winner
      rw [socialMedian_const appB_card,
        delegate_pair_one (by norm_num [appendixBState1])]
      rfl
    have hold : outcome appendixBPeaks (fun _ : Fin 3 => (0:ℝ)) = -30 := by
      unfold outcome winner
      rw [socialMedian_const appB_card,
        delegate_pair_zero (by norm_num [appendixBPeaks])]
      rfl
    unfold Prefers
    rw [hnew, hold]
    norm_num [appendixBPeaks]

/-- Appendix B, second move: after the first manipulation, with the right
proxy observed winning, reporting 25 is a dominating manipulation for the
left proxy. -/
theorem appendixB_left_dominating_25 :
    IsDominatingManipulation (Fin 3) appendixBPeaks appendixBState1 1 0 25 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hwq : winner appendixBState1 q = 1 := hq
    have hout : outcome appendixBState1 q = 29 := by
      unfold outcome
      rw [hwq]
      rfl
    rw [appB_update2, hout]
    rcases outcome_pair appendixBState2 q with h | h <;> rw [h] <;>
      norm_num [appendixBState2, appendixBPeaks]
  · refine ⟨fun _ : Fin 3 => (0:ℝ),
      (appB_const_mem_history (by norm_num) (by norm_num)).1.2, ?_⟩
    have hnew : outcome (Function.update appendixBState1 0 25)
        (fun _ : Fin 3 => (0:ℝ)) = 25 := by
      rw [appB_update2]
      unfold outcome winner
      rw [socialMedian_const appB_card,
        delegate_pair_zero (by norm_num [appendixBState2])]
      rfl
    have hold : outcome appendixBState1 (fun _ : Fin 3 => (0:ℝ)) = 29 := by
      unfold outcome winner
      rw [socialMedian_const appB_card,
        delegate_pair_one (by norm_num [appendixBState1])]
      rfl
    unfold Prefers
    rw [hnew, hold]
    norm_num [appendixBPeaks]

/-- **Appendix B, the trap**: at the third state, with the accumulated
observation history, the left proxy has *no* dominating manipulation.  Any
report left of its winning position can hand the win to 29 against a
consistent median just below the tie point; any report right of it moves the
outcome rightward against the low-median profiles; staying put never
strictly helps. -/
theorem appendixB_left_has_no_dominating (r : ℝ) :
    ¬ DominatesOver appendixBPeaks appendixBState2 appendixBHistory 0 r := by
  rintro ⟨hweak, hstrict⟩
  rcases lt_trichotomy r 25 with hr | hr | hr
  · obtain ⟨μ, hμ1, hμ2, hμ3⟩ :
        ∃ μ, (r + 29) / 2 < μ ∧ -(1 / 2 : ℝ) < μ ∧ μ < 27 := by
      refine ⟨(max ((r + 29) / 2) (-(1 / 2)) + 27) / 2, ?_, ?_, ?_⟩
      · have ha := le_max_left ((r + 29) / 2) (-(1 / 2) : ℝ)
        have hb := max_lt (show (r + 29) / 2 < 27 by linarith)
          (show (-(1 / 2) : ℝ) < 27 by norm_num)
        linarith
      · have ha := le_max_right ((r + 29) / 2) (-(1 / 2) : ℝ)
        have hb := max_lt (show (r + 29) / 2 < 27 by linarith)
          (show (-(1 / 2) : ℝ) < 27 by norm_num)
        linarith
      · have hb := max_lt (show (r + 29) / 2 < 27 by linarith)
          (show (-(1 / 2) : ℝ) < 27 by norm_num)
        linarith
    have hmem := appB_const_mem_history hμ2 (le_of_lt hμ3)
    have hw := hweak _ hmem
    have hwin : winner appendixBState2 (fun _ : Fin 3 => μ) = 0 := hmem.2
    have hold : outcome appendixBState2 (fun _ : Fin 3 => μ) = 25 := by
      unfold outcome
      rw [hwin]
      rfl
    have hdel : delegate (Function.update appendixBState2 0 r) μ = 1 := by
      refine delegate_pair_one ?_
      rw [Function.update_of_ne (by decide), Function.update_self]
      have e1 : appendixBState2 1 = 29 := rfl
      rw [e1, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    have hnew : outcome (Function.update appendixBState2 0 r)
        (fun _ : Fin 3 => μ) = 29 := by
      unfold outcome winner
      rw [socialMedian_const appB_card, hdel, Function.update_of_ne (by decide)]
      rfl
    rw [hnew, hold] at hw
    norm_num [appendixBPeaks] at hw
  · subst hr
    obtain ⟨q, -, hpref⟩ := hstrict
    rw [show Function.update appendixBState2 0 (25:ℝ) = appendixBState2 from
      Function.update_eq_self 0 appendixBState2] at hpref
    exact absurd hpref (lt_irrefl _)
  · have hmem := appB_const_mem_history (μ := 10) (by norm_num) (by norm_num)
    have hw := hweak _ hmem
    have hwin : winner appendixBState2 (fun _ : Fin 3 => (10:ℝ)) = 0 := hmem.2
    have hold : outcome appendixBState2 (fun _ : Fin 3 => (10:ℝ)) = 25 := by
      unfold outcome
      rw [hwin]
      rfl
    rw [hold] at hw
    rcases outcome_pair (Function.update appendixBState2 0 r)
        (fun _ => (10:ℝ)) with h | h <;> rw [h] at hw
    · rw [Function.update_self] at hw
      have habs : |r - appendixBPeaks 0| = r + 30 := by
        have e0 : appendixBPeaks 0 = -30 := rfl
        rw [e0, show r - (-30 : ℝ) = r + 30 by ring]
        exact abs_of_pos (by linarith)
      rw [habs] at hw
      norm_num [appendixBPeaks] at hw
      linarith
    · rw [Function.update_of_ne (by decide)] at hw
      norm_num [appendixBState2, appendixBPeaks] at hw

/-- Appendix B: the right proxy retains a dominating manipulation at the
trapped state — reporting 27 dominates over the full observation history —
so the dominating dynamics needn't terminate. -/
theorem appendixB_right_dominating_27 :
    DominatesOver appendixBPeaks appendixBState2 appendixBHistory 1 27 := by
  refine ⟨?_, ?_⟩
  · rintro q ⟨-, hq2⟩
    have hwq : winner appendixBState2 q = 0 := hq2
    have hout : outcome appendixBState2 q = 25 := by
      unfold outcome
      rw [hwq]
      rfl
    rw [hout]
    rcases outcome_pair (Function.update appendixBState2 1 27) q with h | h <;>
      rw [h]
    · rw [Function.update_of_ne (by decide)]
      norm_num [appendixBState2, appendixBPeaks]
    · rw [Function.update_self]
      norm_num [appendixBPeaks]
  · refine ⟨fun _ : Fin 3 => (53 / 2 : ℝ),
      appB_const_mem_history (by norm_num) (by norm_num), ?_⟩
    have hwin : winner appendixBState2 (fun _ : Fin 3 => (53 / 2 : ℝ)) = 0 :=
      (appB_const_mem_history (μ := 53 / 2) (by norm_num) (by norm_num)).2
    have hold : outcome appendixBState2 (fun _ : Fin 3 => (53 / 2 : ℝ))
        = 25 := by
      unfold outcome
      rw [hwin]
      rfl
    have hdel : delegate (Function.update appendixBState2 1 27) (53 / 2 : ℝ)
        = 1 := by
      refine delegate_pair_one ?_
      rw [Function.update_self, Function.update_of_ne (by decide)]
      norm_num [appendixBState2]
    have hnew : outcome (Function.update appendixBState2 1 27)
        (fun _ : Fin 3 => (53 / 2 : ℝ)) = 27 := by
      unfold outcome winner
      rw [socialMedian_const appB_card, hdel, Function.update_self]
    unfold Prefers
    rw [hnew, hold]
    norm_num [appendixBPeaks]

/-- Appendix B, continuing family: whenever the right proxy reports
`y ∈ (25,29]` and the observed history still has the left proxy winning, moving
halfway back toward 25 is a dominating manipulation over the accumulated
history.  Thus the example is not just a single extra move: the right proxy can
continue with reports `29, 27, 26, ...`, while the realized outcome remains
pinned at 25. -/
theorem appendixB_right_continuing_dominating {y : ℝ} (hy25 : 25 < y) (hy29 : y ≤ 29) :
    DominatesOver appendixBPeaks (appendixBStateY y) (appendixBHistoryAt y) 1
      ((25 + y) / 2) := by
  set y' : ℝ := (25 + y) / 2 with hy'
  have hy'25 : 25 < y' := by rw [hy']; linarith
  have hy'y : y' < y := by rw [hy']; linarith
  have hy'90 : y' ≤ 90 := by rw [hy']; linarith
  refine ⟨?_, ?_⟩
  · rintro q ⟨-, hcur⟩
    have hold : outcome (appendixBStateY y) q = 25 := by
      unfold outcome
      rw [show winner (appendixBStateY y) q = 0 from hcur]
      rfl
    rw [hold]
    rcases outcome_pair (Function.update (appendixBStateY y) 1 y') q with hnew | hnew
    · rw [hnew, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      rfl
    · rw [hnew, Function.update_self]
      have hleft : |(25 : ℝ) - appendixBPeaks 1| = 65 := by
        norm_num [appendixBPeaks]
      have hright : |y' - appendixBPeaks 1| = 90 - y' := by
        rw [show appendixBPeaks 1 = (90 : ℝ) from rfl]
        simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hy'90)
      rw [hleft, hright]
      linarith
  · let μ : ℝ := (((25 + y') / 2) + y') / 2
    have hμ_lower : (25 + y') / 2 < μ := by
      dsimp [μ]
      linarith [hy'25]
    have hμ_upper : μ < y' := by
      dsimp [μ]
      linarith [hy'25]
    have hμ_cur : μ ≤ (25 + y) / 2 := by
      rw [← hy']
      exact le_of_lt hμ_upper
    have hμ_neg : -(1 / 2 : ℝ) < μ := by
      linarith [hμ_lower, hy'25]
    have hμ_27 : μ ≤ 27 := by
      rw [← hy'] at hμ_cur
      have hy'le27 : y' ≤ 27 := by
        rw [hy']
        linarith
      exact le_trans (le_of_lt hμ_upper) hy'le27
    have hhist : (fun _ : Fin 3 => μ) ∈ appendixBHistory :=
      appB_const_mem_history hμ_neg hμ_27
    have hcur : (fun _ : Fin 3 => μ) ∈ winnerInfoSet (appendixBStateY y) 0 := by
      simp only [winnerInfoSet, Set.mem_setOf_eq]
      unfold winner
      rw [socialMedian_const appB_card]
      refine delegate_pair_zero ?_
      rw [show appendixBStateY y 0 = (25 : ℝ) from rfl,
        show appendixBStateY y 1 = y from rfl]
      have hμ_lt_y : μ < y := lt_trans hμ_upper hy'y
      rw [abs_of_nonpos (by linarith [hμ_lower, hy'25]),
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt hμ_lt_y))]
      linarith [hμ_cur]
    refine ⟨fun _ : Fin 3 => μ, ⟨hhist, hcur⟩, ?_⟩
    have hold : outcome (appendixBStateY y) (fun _ : Fin 3 => μ) = 25 := by
      unfold outcome
      rw [show winner (appendixBStateY y) (fun _ : Fin 3 => μ) = 0 from hcur]
      rfl
    have hdel : delegate (Function.update (appendixBStateY y) 1 y') μ = 1 := by
      refine delegate_pair_one ?_
      rw [Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        show appendixBStateY y 0 = (25 : ℝ) from rfl]
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
    have hnew : outcome (Function.update (appendixBStateY y) 1 y')
        (fun _ : Fin 3 => μ) = y' := by
      unfold outcome winner
      rw [socialMedian_const appB_card, hdel, Function.update_self]
    unfold Prefers
    rw [hnew, hold, show appendixBPeaks 1 = (90 : ℝ) from rfl]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by norm_num)]
    linarith

/-- Appendix B: on the realized profile the outcome is pinned — any report
of the right proxy weakly beyond the left proxy's winning position (in
particular the paper's whole dominating range `(25, 29)`) leaves the
realized outcome at 25, so the dominating dynamics converges in outcome. -/
theorem appendixB_outcome_stuck {y : ℝ} (hy : 25 ≤ y) :
    outcome (Function.update appendixBState2 1 y) appendixBFollowers = 25 := by
  have h1 : socialMedian appendixBState2 appendixBFollowers
      < appendixBState2 1 := by
    rw [appB_median_state2]
    norm_num [appendixBState2]
  have h2 : socialMedian appendixBState2 appendixBFollowers ≤ y := by
    rw [appB_median_state2]
    linarith
  have hmed := socialMedian_update_eq_of_proxy_gt h1 h2
  have hdel : delegate (Function.update appendixBState2 1 y) 10 = 0 := by
    refine delegate_pair_zero ?_
    rw [Function.update_of_ne (by decide), Function.update_self]
    have e0 : appendixBState2 0 = 25 := rfl
    rw [e0, abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith)]
    linarith
  unfold outcome winner
  rw [hmed, appB_median_state2, hdel, Function.update_of_ne (by decide)]
  rfl

/-- Appendix B, continuing family on the realized profile: every report
`y ≥ 25` in the continuing family leaves the realized outcome pinned at 25. -/
theorem appendixB_continuing_realized_outcome {y : ℝ} (hy : 25 ≤ y) :
    outcome (appendixBStateY y) appendixBFollowers = 25 := by
  have hstate : appendixBStateY y = Function.update appendixBState2 1 y := by
    funext i
    fin_cases i <;> simp [appendixBStateY, appendixBState2]
  rw [hstate]
  exact appendixB_outcome_stuck (y := y) hy

/-- The tempting stronger reading of Appendix B is false over the whole
accumulated history: after the second displayed move, there is a
history-consistent profile and a report in `(25,29)` whose outcome is not 25.
The pinning statement is about the realized follower profile, or about the
history after the additional winner observation is incorporated. -/
theorem appendixB_history_profile_outcome_not_stuck :
    ∃ (y : ℝ) (q : Fin 3 → ℝ),
      25 < y ∧ y < 29 ∧ q ∈ appendixBHistory ∧
        outcome (Function.update appendixBState2 1 y) q ≠ 25 := by
  refine ⟨27, fun _ : Fin 3 => (53 / 2 : ℝ), by norm_num, by norm_num,
    appB_const_mem_history (by norm_num) (by norm_num), ?_⟩
  have hdel : delegate (Function.update appendixBState2 1 27) (53 / 2 : ℝ) = 1 := by
    refine delegate_pair_one ?_
    rw [Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    norm_num [appendixBState2]
  have hnew : outcome (Function.update appendixBState2 1 27)
      (fun _ : Fin 3 => (53 / 2 : ℝ)) = 27 := by
    unfold outcome winner
    rw [socialMedian_const appB_card, hdel, Function.update_self]
  rw [hnew]
  norm_num

/-- Appendix B: the social-cost comparison.  The truthful outcome −30 costs
210 and the limit outcome 25 costs 235 — the dominating dynamics converges
to a strictly worse social outcome, although 25 is strictly closer to the
true median than −30 is. -/
theorem appendixB_socialCost :
    socialCost appendixBPeaks appendixBFollowers (-30) = 210
      ∧ socialCost appendixBPeaks appendixBFollowers 25 = 235 := by
  constructor <;>
  · unfold socialCost
    rw [Fintype.sum_sum_type]
    norm_num [allPos, appendixBPeaks, appendixBFollowers,
      Fin.sum_univ_two, Fin.sum_univ_three]

/-! ### Complete information breaks the trap

The last sentence of the appendix observes that complete information prevents
the incomplete-information convergence: with the true median public, the
trapped left proxy has a better response, so the trap `s^3` is not an
equilibrium.  Here that better response is mechanized — proxy `1` (index `0`,
peak `-30`) reports `-25`, the reflection of the trapped outcome `25` across
the true median `0`, winning at `-25`, strictly nearer its peak than `25`. -/

/-- The complete-information deviation of the trapped left proxy: it reports the
reflection of the trapped outcome across the true median. -/
def appendixBStateCI : Fin 2 → ℝ
  | 0 => -25
  | 1 => 29

private theorem appB_updateCI :
    Function.update appendixBState2 0 (-25) = appendixBStateCI := by
  funext i
  fin_cases i <;> simp [appendixBState2, appendixBStateCI]

private theorem appB_ci_cum_zero :
    Math.cumWeight (allPos appendixBStateCI appendixBFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBStateCI, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_ci_cum_neg25 :
    Math.cumWeight (allPos appendixBStateCI appendixBFollowers) (fun _ => 1) (-25)
      = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBStateCI, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_ci_cum_neg50 :
    Math.cumWeight (allPos appendixBStateCI appendixBFollowers) (fun _ => 1) (-50)
      = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  norm_num [allPos, appendixBStateCI, appendixBFollowers,
    Fin.sum_univ_two, Fin.sum_univ_three]

private theorem appB_median_ci :
    socialMedian appendixBStateCI appendixBFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 1, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, appB_ci_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos appendixBStateCI appendixBFollowers)
            (fun _ => 1) (-25) < Math.totalWeight fun _ => 1
          rw [appB_ci_cum_neg25, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixBStateCI] at hzlt
    | inr f =>
        fin_cases f
        · change 2 * Math.cumWeight (allPos appendixBStateCI appendixBFollowers)
            (fun _ => 1) (-50) < Math.totalWeight fun _ => 1
          rw [appB_ci_cum_neg50, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, appendixBFollowers] at hzlt
        · norm_num [allPos, appendixBFollowers] at hzlt

private theorem appB_ci_delegate : delegate appendixBStateCI 0 = 0 := by
  refine delegate_pair_zero ?_
  have e0 : appendixBStateCI 0 = -25 := rfl
  have e1 : appendixBStateCI 1 = 29 := rfl
  rw [e0, e1, abs_of_nonpos (by norm_num), abs_of_nonneg (by norm_num)]
  norm_num

private theorem appB_ci_outcome :
    outcome appendixBStateCI appendixBFollowers = -25 := by
  unfold outcome winner
  rw [appB_median_ci, appB_ci_delegate]
  rfl

/-- **Complete information breaks the incomplete-information trap.**  At the
trapped state `s^3`, where the left proxy has no dominating manipulation under
partial information, complete information gives it a genuine better response:
reporting `-25` (the reflection of the outcome `25` across the true median `0`)
moves the outcome to `-25`, strictly nearer its peak `-30`.  So `s^3` is not a
pure Nash equilibrium under complete information. -/
theorem appendixB_complete_information_better_response :
    IsBetterResponse appendixBPeaks appendixBFollowers appendixBState2 0 (-25) := by
  refine isBetterResponse_of_prefers ?_
  have hnew : outcome (Function.update appendixBState2 0 (-25)) appendixBFollowers
      = -25 := by
    rw [appB_updateCI]; exact appB_ci_outcome
  rw [hnew, appendixB_realized_outcomes.2.2]
  simp only [Prefers, show appendixBPeaks 0 = (-30 : ℝ) from rfl]
  norm_num

end ProxyVoting

end GameTheory
