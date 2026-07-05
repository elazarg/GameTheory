/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.PeakAnchored

/-!
# Truth-oriented proxy-voting dynamics

Truth-oriented proxy policies select the true peak whenever truthful reporting
is itself a better response and is weakly best among better responses.

At states satisfying the monotone-dynamics invariants, every non-anchored
monotone better response makes truthful reporting a weakly best better
response.  Consequently a truth-oriented monotone dynamics is peak-anchored,
and the `Delta` outcome bound follows without any history induction.

This is the monotone-dynamics safety layer.  The full non-monotone Theorem 3
lives in `GameTheory.Mechanism.ProxyVoting.Bounded`, whose forcing theorems
build on the notions defined here.
-/

namespace GameTheory

namespace ProxyVoting

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]

section TruthOriented

variable {pp : P → ℝ} {q : F → ℝ}

/-- Truthful reporting is in the better-response set and is weakly best, under
the order comparisons forced by single-peakedness, among all better responses. -/
def TruthWeaklyBestAmongBetterResponses
    (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) : Prop :=
  IsBetterResponse pp q s j (pp j) ∧
    ∀ r, IsBetterResponse pp q s j r →
      SPWeaklyPrefers (pp j)
        (outcome (Function.update s j (pp j)) q)
        (outcome (Function.update s j r) q)

theorem truthWeaklyBestAmongBetterResponses_of_truth_outcome_eq_peak
    {s : P → ℝ} {j : P}
    (hbr : IsBetterResponse pp q s j (pp j))
    (hout : outcome (Function.update s j (pp j)) q = pp j) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  refine ⟨hbr, ?_⟩
  intro r _hr
  rw [hout]
  by_cases hle : pp j ≤ outcome (Function.update s j r) q
  · exact Or.inl ⟨le_rfl, hle⟩
  · exact Or.inr ⟨le_of_lt (lt_of_not_ge hle), le_rfl⟩

theorem truth_isBetterResponse_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    IsBetterResponse pp q s j (pp j) := by
  have htruth_mono : MonotoneReport pp q j (pp j) := sameSide_self pp q j
  have hmed_truth :
      socialMedian (Function.update s j (pp j)) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed htruth_mono
  have hmed_report :
      socialMedian (Function.update s j r) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed hmono
  have hd := dist_peak_lt_dist_report_of_not_peakAnchoredReport hnot
  have hout_or :
      outcome (Function.update s j (pp j)) q = pp j
        ∨ outcome (Function.update s j (pp j)) q
          = outcome (Function.update s j r) q := by
    unfold outcome winner
    rw [hmed_truth, hmed_report]
    exact update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := socialMedian pp q) (p := pp j) (r := r) hd
  exact hbr.truth_of_outcome_eq_peak_or_eq hout_or

theorem truth_outcome_eq_peak_or_current_outcome_eq_report_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    outcome (Function.update s j (pp j)) q = pp j ∨ outcome s q = s j := by
  have htruth_mono : MonotoneReport pp q j (pp j) := sameSide_self pp q j
  have hmed_truth :
      socialMedian (Function.update s j (pp j)) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed htruth_mono
  have hmed_report :
      socialMedian (Function.update s j r) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed hmono
  have hd := dist_peak_lt_dist_report_of_not_peakAnchoredReport hnot
  have hout_or :
      outcome (Function.update s j (pp j)) q = pp j
        ∨ outcome (Function.update s j (pp j)) q
          = outcome (Function.update s j r) q := by
    unfold outcome winner
    rw [hmed_truth, hmed_report]
    exact update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := socialMedian pp q) (p := pp j) (r := r) hd
  by_cases hpeak : outcome (Function.update s j (pp j)) q = pp j
  · exact Or.inl hpeak
  · right
    rcases hout_or with hpeak' | hsame_report
    · exact absurd hpeak' hpeak
    have htruth_ne_old : outcome (Function.update s j (pp j)) q ≠ outcome s q := by
      intro hold
      exact hbr.1 (by rw [← hsame_report, hold])
    have hsj_le_peak : |s j - socialMedian pp q| ≤ |pp j - socialMedian pp q| := by
      by_contra hle
      have hdist_s : |pp j - socialMedian pp q| < |s j - socialMedian pp q| :=
        lt_of_not_ge hle
      have hor :
          outcome (Function.update s j (pp j)) q = pp j
            ∨ outcome (Function.update s j (pp j)) q = outcome s q := by
        have hraw := update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
          (m := socialMedian pp q) (p := pp j) (r := s j) hdist_s
        simpa [outcome, winner, hmed_truth, hmed, Function.update_eq_self] using hraw
      rcases hor with hp | hold
      · exact absurd hp hpeak
      · exact htruth_ne_old hold
    have hdist_sr : |s j - socialMedian pp q| < |r - socialMedian pp q| :=
      lt_of_le_of_lt hsj_le_peak hd
    have hor :
        outcome s q = s j ∨ outcome s q = outcome (Function.update s j r) q := by
      have hraw := update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
        (m := socialMedian pp q) (p := s j) (r := r) hdist_sr
      simpa [outcome, winner, hmed, hmed_report, Function.update_eq_self] using hraw
    rcases hor with hold_report | hold_report
    · exact hold_report
    · exact absurd hold_report.symm hbr.1

theorem current_report_peakAnchored_of_truth_outcome_ne_peak_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r)
    (htruth_ne : outcome (Function.update s j (pp j)) q ≠ pp j) :
    PeakAnchoredReport pp q j (s j) := by
  have htruth_mono : MonotoneReport pp q j (pp j) := sameSide_self pp q j
  have hmed_truth :
      socialMedian (Function.update s j (pp j)) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed htruth_mono
  have hmed_report :
      socialMedian (Function.update s j r) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed hmono
  have hd := dist_peak_lt_dist_report_of_not_peakAnchoredReport hnot
  have hout_or :
      outcome (Function.update s j (pp j)) q = pp j
        ∨ outcome (Function.update s j (pp j)) q
          = outcome (Function.update s j r) q := by
    unfold outcome winner
    rw [hmed_truth, hmed_report]
    exact update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := socialMedian pp q) (p := pp j) (r := r) hd
  rcases hout_or with hpeak | hsame_report
  · exact absurd hpeak htruth_ne
  by_contra hle
  have hdist_s : |pp j - socialMedian pp q| < |s j - socialMedian pp q| :=
    lt_of_not_ge hle
  have hor :
      outcome (Function.update s j (pp j)) q = pp j
        ∨ outcome (Function.update s j (pp j)) q = outcome s q := by
    have hraw := update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := socialMedian pp q) (p := pp j) (r := s j) hdist_s
    simpa [outcome, winner, hmed_truth, hmed, Function.update_eq_self] using hraw
  rcases hor with hp | hold
  · exact htruth_ne hp
  · exact hbr.1 (by rw [← hsame_report, hold])

private theorem lt_of_not_spPrefers_of_left {p old new : ℝ}
    (hpold : p ≤ old) (hne : new ≠ old) (hnot : ¬ SPPrefers p old new) :
    new < old := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · exfalso
    exact hnot (Or.inl ⟨hpold, hgt⟩)

private theorem lt_of_not_spPrefers_of_right {p old new : ℝ}
    (holdp : old ≤ p) (hne : new ≠ old) (hnot : ¬ SPPrefers p old new) :
    old < new := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    exact hnot (Or.inr ⟨hlt, holdp⟩)
  · exact hgt

theorem truth_outcome_spWeaklyPrefers_all_betterResponses_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    ∀ u, IsBetterResponse pp q s j u →
      SPWeaklyPrefers (pp j)
        (outcome (Function.update s j (pp j)) q)
        (outcome (Function.update s j u) q) := by
  intro u hbru
  by_cases htruth_peak : outcome (Function.update s j (pp j)) q = pp j
  · rw [htruth_peak]
    by_cases hle : pp j ≤ outcome (Function.update s j u) q
    · exact Or.inl ⟨le_rfl, hle⟩
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge hle), le_rfl⟩
  have htruth_br :=
    truth_isBetterResponse_of_not_peakAnchoredReport hside hmed hbr hmono hnot
  have hcurrent :=
    current_report_peakAnchored_of_truth_outcome_ne_peak_of_not_peakAnchoredReport
      hside hmed hbr hmono hnot htruth_peak
  have hold_report :
      outcome s q = s j :=
    (truth_outcome_eq_peak_or_current_outcome_eq_report_of_not_peakAnchoredReport
      hside hmed hbr hmono hnot).resolve_left htruth_peak
  set m := socialMedian pp q
  set st := Function.update s j (pp j)
  set su := Function.update s j u
  set T := outcome st q
  set U := outcome su q
  have htruth_mono : MonotoneReport pp q j (pp j) := sameSide_self pp q j
  have hmed_truth : socialMedian st q = m := by
    simpa [st, m] using socialMedian_update_eq_of_sameSide hside hmed htruth_mono
  set k := delegate st m
  have hT_eq : T = st k := by
    simp [T, outcome, winner, hmed_truth, k]
  have hk_ne : k ≠ j := by
    intro hkj
    apply htruth_peak
    rw [hT_eq]
    simp [st, hkj]
  have hsu_k : su k = T := by
    rw [hT_eq]
    simp [su, st, hk_ne]
  have hT_ne_old : T ≠ s j := by
    intro hTold
    exact htruth_br.1 (by simpa [T, st, hold_report] using hTold)
  have hU_ne_old : U ≠ s j := by
    intro hUold
    exact hbru.1 (by simpa [U, su, hold_report] using hUold)
  have hT_delegate_dist : |T - m| ≤ |pp j - m| := by
    have hdist := delegate_dist_le st m j
    simpa [hT_eq, st, k] using hdist
  rcases lt_trichotomy (pp j) m with hp | hp | hp
  · have hsj_lt_m : s j < m := by
      simpa [m] using (hside j).1 (by simpa [m] using hp)
    have hp_sj : pp j ≤ s j := by
      unfold PeakAnchoredReport at hcurrent
      rw [abs_of_neg (by linarith [hsj_lt_m]), abs_of_neg (by linarith [hp])] at hcurrent
      linarith
    have hT_lt_sj : T < s j := by
      exact lt_of_not_spPrefers_of_left hp_sj hT_ne_old
        (by simpa [T, hold_report] using htruth_br.2)
    have hT_lt_m : T < m := lt_trans hT_lt_sj hsj_lt_m
    have hpT : pp j ≤ T := by
      by_contra hle
      have hT_lt_p : T < pp j := lt_of_not_ge hle
      rw [abs_of_neg (by linarith [hT_lt_m]), abs_of_neg (by linarith [hp])] at hT_delegate_dist
      linarith
    have hT_le_U : T ≤ U := by
      by_contra hle
      have hU_lt_T : U < T := lt_of_not_ge hle
      have hU_lt_m : U < m := lt_trans hU_lt_T hT_lt_m
      rcases le_or_gt u m with hu | hu
      · have hmed_u : socialMedian su q = m := by
          have h := socialMedian_update_eq_of_proxy_lt (s := s) (q := q)
            (j := j) (r := u) (by rwa [hmed]) (by rwa [hmed])
          simpa [su, m] using h.trans hmed
        have hd : |U - m| ≤ |T - m| := by
          have hdist := delegate_dist_le su (socialMedian su q) k
          simpa [U, outcome, winner, hmed_u, hsu_k] using hdist
        rw [abs_of_neg (by linarith [hU_lt_m]), abs_of_neg (by linarith [hT_lt_m])] at hd
        linarith
      · have hm_le_medu : m ≤ socialMedian su q := by
          have hsj_le_u : s j ≤ u := le_of_lt (lt_trans hsj_lt_m hu)
          have h := socialMedian_le_update_proxy (s := s) (q := q) (j := j) (r := u) hsj_le_u
          simpa [su, m, hmed] using h
        have hd : |U - socialMedian su q| ≤ |T - socialMedian su q| := by
          have hdist := delegate_dist_le su (socialMedian su q) k
          simpa [U, outcome, winner, hsu_k] using hdist
        rw [abs_of_neg (by linarith [hU_lt_m, hm_le_medu]),
          abs_of_neg (by linarith [hT_lt_m, hm_le_medu])] at hd
        linarith
    exact Or.inl ⟨hpT, hT_le_U⟩
  · exfalso
    apply hnot
    unfold PeakAnchoredReport
    rw [hmono.2.2 (by simpa [m] using hp), hp]
  · have hm_lt_sj : m < s j := by
      simpa [m] using (hside j).2.1 (by simpa [m] using hp)
    have hsj_le_p : s j ≤ pp j := by
      unfold PeakAnchoredReport at hcurrent
      rw [abs_of_pos (by linarith [hm_lt_sj]), abs_of_pos (by linarith [hp])] at hcurrent
      linarith
    have hsj_lt_T : s j < T := by
      exact lt_of_not_spPrefers_of_right hsj_le_p hT_ne_old
        (by simpa [T, hold_report] using htruth_br.2)
    have hm_lt_T : m < T := lt_trans hm_lt_sj hsj_lt_T
    have hTp : T ≤ pp j := by
      by_contra hle
      have hp_lt_T : pp j < T := lt_of_not_ge hle
      rw [abs_of_pos (by linarith [hm_lt_T]), abs_of_pos (by linarith [hp])] at hT_delegate_dist
      linarith
    have hU_le_T : U ≤ T := by
      by_contra hle
      have hT_lt_U : T < U := lt_of_not_ge hle
      have hm_lt_U : m < U := lt_trans hm_lt_T hT_lt_U
      rcases le_or_gt m u with hu | hu
      · have hmed_u : socialMedian su q = m := by
          have h := socialMedian_update_eq_of_proxy_gt (s := s) (q := q)
            (j := j) (r := u) (by rwa [hmed]) (by rwa [hmed])
          simpa [su, m] using h.trans hmed
        have hd : |U - m| ≤ |T - m| := by
          have hdist := delegate_dist_le su (socialMedian su q) k
          simpa [U, outcome, winner, hmed_u, hsu_k] using hdist
        rw [abs_of_pos (by linarith [hm_lt_U]), abs_of_pos (by linarith [hm_lt_T])] at hd
        linarith
      · have hmedu_le_m : socialMedian su q ≤ m := by
          have hu_le_sj : u ≤ s j := le_of_lt (lt_trans hu hm_lt_sj)
          have h := socialMedian_update_proxy_le (s := s) (q := q) (j := j) (r := u) hu_le_sj
          simpa [su, m, hmed] using h
        have hd : |U - socialMedian su q| ≤ |T - socialMedian su q| := by
          have hdist := delegate_dist_le su (socialMedian su q) k
          simpa [U, outcome, winner, hsu_k] using hdist
        rw [abs_of_pos (by linarith [hm_lt_U, hmedu_le_m]),
          abs_of_pos (by linarith [hm_lt_T, hmedu_le_m])] at hd
        linarith
    exact Or.inr ⟨hU_le_T, hTp⟩

theorem truth_outcome_dist_le_all_betterResponses_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    ∀ u, IsBetterResponse pp q s j u →
      |outcome (Function.update s j (pp j)) q - pp j|
        ≤ |outcome (Function.update s j u) q - pp j| := by
  intro u hu
  exact (truth_outcome_spWeaklyPrefers_all_betterResponses_of_not_peakAnchoredReport
    hside hmed hbr hmono hnot u hu).abs_le

theorem truthWeaklyBestAmongBetterResponses_of_not_peakAnchoredReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    (hbr : IsBetterResponse pp q s j r) (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    TruthWeaklyBestAmongBetterResponses pp q s j :=
  ⟨truth_isBetterResponse_of_not_peakAnchoredReport hside hmed hbr hmono hnot,
    truth_outcome_spWeaklyPrefers_all_betterResponses_of_not_peakAnchoredReport
      hside hmed hbr hmono hnot⟩

/-- A report is truth-oriented at a state if it switches to the true peak
whenever truthful reporting is a weakly best better response. -/
def TruthOrientedChoice
    (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) (r : ℝ) : Prop :=
  TruthWeaklyBestAmongBetterResponses pp q s j → r = pp j

/-- A monotone better-response step whose chosen report satisfies the
truth-oriented choice rule. -/
def TruthOrientedMonotoneStep
    (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ MonotoneReport pp q j r
    ∧ TruthOrientedChoice pp q s j r ∧ s' = Function.update s j r

/-- Truth-oriented monotone dynamics from the truthful state, with rest steps
allowed as in `IsMonotoneDynamics`. -/
def IsTruthOrientedMonotoneDynamics
    (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp
    ∧ ∀ t, TruthOrientedMonotoneStep pp q (σ t) (σ (t + 1))
      ∨ σ (t + 1) = σ t

omit [LinearOrder P] in
theorem peakAnchoredReport_truthful (j : P) :
    PeakAnchoredReport pp q j (pp j) := by
  simp [PeakAnchoredReport]

theorem TruthOrientedMonotoneStep.toMonotoneStep {s s' : P → ℝ}
    (h : TruthOrientedMonotoneStep pp q s s') : MonotoneStep pp q s s' := by
  obtain ⟨j, r, hbr, hmono, _htruth, hs'⟩ := h
  exact ⟨j, r, hbr, hmono, hs'⟩

theorem IsTruthOrientedMonotoneDynamics.toIsMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsTruthOrientedMonotoneDynamics pp q σ) :
    IsMonotoneDynamics pp q σ := by
  constructor
  · exact h.1
  · intro t
    rcases h.2 t with hstep | hrest
    · exact Or.inl hstep.toMonotoneStep
    · exact Or.inr hrest

/-- A truth-oriented monotone step at a state satisfying the monotone-dynamics
invariants is peak-anchored. -/
theorem TruthOrientedMonotoneStep.toPeakAnchoredStep {s s' : P → ℝ}
    (h : TruthOrientedMonotoneStep pp q s s')
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q) :
    PeakAnchoredStep pp q s s' := by
  obtain ⟨j, r, hbr, hmono, htruth, hs'⟩ := h
  refine ⟨j, r, hbr, hmono, ?_, hs'⟩
  by_cases hanchor : PeakAnchoredReport pp q j r
  · exact hanchor
  · have hbest :=
      truthWeaklyBestAmongBetterResponses_of_not_peakAnchoredReport
        hside hmed hbr hmono hanchor
    rw [htruth hbest]
    exact peakAnchoredReport_truthful j

/-- Dynamics-level bridge from truth-oriented monotone dynamics to the
peak-anchored invariant. -/
theorem IsTruthOrientedMonotoneDynamics.toIsPeakAnchoredDynamics {σ : ℕ → P → ℝ}
    (h : IsTruthOrientedMonotoneDynamics pp q σ) :
    IsPeakAnchoredDynamics pp q σ := by
  have hmono := h.toIsMonotoneDynamics
  constructor
  · exact h.1
  · intro t
    rcases h.2 t with hstep | hrest
    · have hinv := sameSide_and_socialMedian_eq_of_isMonotoneDynamics hmono t
      exact Or.inl (hstep.toPeakAnchoredStep hinv.1 hinv.2)
    · exact Or.inr hrest

/-- The `Delta` outcome bound for truth-oriented monotone dynamics, factored
through the peak-anchored invariant. -/
theorem outcome_dist_le_delta_of_truthOrientedMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsTruthOrientedMonotoneDynamics pp q σ) (t : ℕ) :
    |outcome (σ t) q - socialMedian pp q|
      ≤ |outcome pp q - socialMedian pp q| :=
  outcome_dist_le_delta_of_dynamics h.toIsPeakAnchoredDynamics t

/-- Along truth-oriented monotone dynamics, reports remain between their peak
and the true population median. -/
theorem betweenPeakAndMedian_of_truthOrientedMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsTruthOrientedMonotoneDynamics pp q σ) (t : ℕ) (j : P) :
    BetweenPeakAndMedian pp q j (σ t j) :=
  betweenPeakAndMedian_of_dynamics h.toIsPeakAnchoredDynamics t j

end TruthOriented

end ProxyVoting

end GameTheory
