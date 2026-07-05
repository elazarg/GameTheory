/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Dynamics

/-!
# Peak-anchored proxy-voting dynamics

Bielous–Meir prove a `Delta`-neighborhood safety bound for truth-oriented proxy
dynamics.  The monotone case has a sharper reusable invariant: if each moving
proxy keeps its report no farther from the true population median than its peak
is, then every report stays between the proxy's peak and the true median.  The
paper's `Delta` bound follows immediately.

This file packages that invariant in a behavioral-agnostic form; policy-specific
truth-oriented conditions can prove safety by deriving the per-step
peak-anchor condition.
-/

namespace GameTheory

namespace ProxyVoting

open Finset

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]

section PeakAnchored

variable {pp : P → ℝ} {q : F → ℝ}

/-- A report is no farther from the true population median than the proxy's
peak.  Together with monotonicity, this says the report lies between the peak
and the median. -/
def PeakAnchoredReport (pp : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) : Prop :=
  |r - socialMedian pp q| ≤ |pp j - socialMedian pp q|

omit [LinearOrder P] in
theorem dist_peak_lt_dist_report_of_not_peakAnchoredReport {j : P} {r : ℝ}
    (h : ¬ PeakAnchoredReport pp q j r) :
    |pp j - socialMedian pp q| < |r - socialMedian pp q| := by
  exact lt_of_not_ge h

/-- A report lies in the closed interval between the proxy's peak and the true
population median, with the endpoint at the median kept strict on the side
conditions inherited from `MonotoneReport`. -/
def BetweenPeakAndMedian (pp : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) : Prop :=
  (pp j < socialMedian pp q → pp j ≤ r ∧ r < socialMedian pp q) ∧
    (socialMedian pp q < pp j → socialMedian pp q < r ∧ r ≤ pp j) ∧
    (pp j = socialMedian pp q → r = socialMedian pp q)

omit [LinearOrder P] in
theorem BetweenPeakAndMedian.monotoneReport {j : P} {r : ℝ}
    (h : BetweenPeakAndMedian pp q j r) : MonotoneReport pp q j r :=
  ⟨fun hp => (h.1 hp).2, fun hp => (h.2.1 hp).1, h.2.2⟩

omit [LinearOrder P] in
theorem BetweenPeakAndMedian.peakAnchoredReport {j : P} {r : ℝ}
    (h : BetweenPeakAndMedian pp q j r) : PeakAnchoredReport pp q j r := by
  unfold PeakAnchoredReport
  rcases lt_trichotomy (pp j) (socialMedian pp q) with hp | hp | hp
  · have hr := h.1 hp
    rw [abs_of_neg (by linarith [hr.2]), abs_of_neg (by linarith [hp])]
    linarith
  · have hr := h.2.2 hp
    rw [hr, hp]
  · have hr := h.2.1 hp
    rw [abs_of_pos (by linarith [hr.1]), abs_of_pos (by linarith [hp])]
    linarith

/-- A monotone better-response step whose moving report is peak-anchored. -/
def PeakAnchoredStep (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ MonotoneReport pp q j r ∧
    PeakAnchoredReport pp q j r ∧ s' = Function.update s j r

/-- A peak-anchored monotone dynamics from the truthful state.  Rest steps are
allowed, as in `IsMonotoneDynamics`. -/
def IsPeakAnchoredDynamics (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp ∧ ∀ t, PeakAnchoredStep pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

theorem PeakAnchoredStep.toMonotoneStep {s s' : P → ℝ}
    (h : PeakAnchoredStep pp q s s') : MonotoneStep pp q s s' := by
  obtain ⟨j, r, hbr, hmono, _hanchor, hs'⟩ := h
  exact ⟨j, r, hbr, hmono, hs'⟩

theorem IsPeakAnchoredDynamics.toIsMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsPeakAnchoredDynamics pp q σ) : IsMonotoneDynamics pp q σ := by
  constructor
  · exact h.1
  · intro t
    rcases h.2 t with hstep | hrest
    · exact Or.inl hstep.toMonotoneStep
    · exact Or.inr hrest

/-- Along a peak-anchored dynamics, every current report remains no farther
from the true population median than the proxy's peak. -/
theorem report_dist_le_peak_dist_of_dynamics {σ : ℕ → P → ℝ}
    (h : IsPeakAnchoredDynamics pp q σ) (t : ℕ) (j : P) :
    |σ t j - socialMedian pp q| ≤ |pp j - socialMedian pp q| := by
  induction t with
  | zero =>
      simp [h.1]
  | succ t ih =>
      rcases h.2 t with hstep | hrest
      · obtain ⟨k, r, _hbr, _hmono, hanchor, hs'⟩ := hstep
        rw [hs']
        by_cases hjk : j = k
        · subst hjk
          simpa [PeakAnchoredReport] using hanchor
        · rw [Function.update_apply, if_neg hjk]
          exact ih
      · rw [hrest]
        exact ih

/-- A report that is on the median side of a left peak and no farther from the
median than the peak must lie between the peak and the median. -/
private theorem le_report_of_left_peak_of_mono_of_dist_le
    {p r m : ℝ} (hp : p < m) (hr : r < m) (hd : |r - m| ≤ |p - m|) :
    p ≤ r := by
  rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hd
  linarith

/-- A report that is on the median side of a right peak and no farther from the
median than the peak must lie between the median and the peak. -/
private theorem report_le_of_right_peak_of_mono_of_dist_le
    {p r m : ℝ} (hp : m < p) (hr : m < r) (hd : |r - m| ≤ |p - m|) :
    r ≤ p := by
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hd
  linarith

omit [LinearOrder P] in
theorem betweenPeakAndMedian_of_monotoneReport_of_peakAnchoredReport
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r)
    (hanchor : PeakAnchoredReport pp q j r) :
    BetweenPeakAndMedian pp q j r := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    exact ⟨le_report_of_left_peak_of_mono_of_dist_le hp (hmono.1 hp) hanchor,
      hmono.1 hp⟩
  · intro hp
    exact ⟨hmono.2.1 hp,
      report_le_of_right_peak_of_mono_of_dist_le hp (hmono.2.1 hp) hanchor⟩
  · exact hmono.2.2

omit [LinearOrder P] in
theorem betweenPeakAndMedian_iff {j : P} {r : ℝ} :
    BetweenPeakAndMedian pp q j r ↔
      MonotoneReport pp q j r ∧ PeakAnchoredReport pp q j r :=
  ⟨fun h => ⟨h.monotoneReport, h.peakAnchoredReport⟩,
    fun h => betweenPeakAndMedian_of_monotoneReport_of_peakAnchoredReport h.1 h.2⟩

omit [LinearOrder P] in
theorem not_peakAnchoredReport_iff_overshoots_peak_of_monotoneReport
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r) :
    ¬ PeakAnchoredReport pp q j r ↔
      (pp j < socialMedian pp q ∧ r < pp j)
        ∨ (socialMedian pp q < pp j ∧ pp j < r) := by
  constructor
  · intro hnot
    rcases lt_trichotomy (pp j) (socialMedian pp q) with hp | hp | hp
    · left
      refine ⟨hp, ?_⟩
      by_contra hle
      rw [not_lt] at hle
      apply hnot
      unfold PeakAnchoredReport
      rw [abs_of_neg (by linarith [hmono.1 hp]), abs_of_neg (by linarith [hp])]
      linarith
    · exfalso
      apply hnot
      unfold PeakAnchoredReport
      rw [hmono.2.2 hp, hp]
    · right
      refine ⟨hp, ?_⟩
      by_contra hle
      rw [not_lt] at hle
      apply hnot
      unfold PeakAnchoredReport
      rw [abs_of_pos (by linarith [hmono.2.1 hp]), abs_of_pos (by linarith [hp])]
      linarith
  · rintro (⟨hp, hr⟩ | ⟨hp, hr⟩) hanchor
    · unfold PeakAnchoredReport at hanchor
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hanchor
      linarith
    · unfold PeakAnchoredReport at hanchor
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hanchor
      linarith

omit [LinearOrder P] in
theorem report_ne_peak_of_not_peakAnchoredReport_of_monotoneReport
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r)
    (hnot : ¬ PeakAnchoredReport pp q j r) :
    r ≠ pp j := by
  rcases (not_peakAnchoredReport_iff_overshoots_peak_of_monotoneReport hmono).mp hnot with
    ⟨_, hr⟩ | ⟨_, hr⟩
  · exact ne_of_lt hr
  · exact ne_of_gt hr

theorem betweenPeakAndMedian_of_dynamics {σ : ℕ → P → ℝ}
    (h : IsPeakAnchoredDynamics pp q σ) (t : ℕ) (j : P) :
    BetweenPeakAndMedian pp q j (σ t j) := by
  have hmono := sameSide_and_socialMedian_eq_of_isMonotoneDynamics
    h.toIsMonotoneDynamics t |>.1
  have hdist := report_dist_le_peak_dist_of_dynamics h t j
  exact betweenPeakAndMedian_of_monotoneReport_of_peakAnchoredReport (hmono j) hdist

/-- Bielous–Meir's `Delta` bound as a corollary of the sharper report invariant:
the current outcome stays within the truthful outcome's distance from the true
population median. -/
theorem outcome_dist_le_delta_of_dynamics {σ : ℕ → P → ℝ}
    (h : IsPeakAnchoredDynamics pp q σ) (t : ℕ) :
    |outcome (σ t) q - socialMedian pp q|
      ≤ |outcome pp q - socialMedian pp q| := by
  have hnear := abs_outcome_sub_le_of_isMonotoneDynamics h.toIsMonotoneDynamics t (winner pp q)
  have hreport := report_dist_le_peak_dist_of_dynamics h t (winner pp q)
  exact hnear.trans hreport

end PeakAnchored

end ProxyVoting

end GameTheory
