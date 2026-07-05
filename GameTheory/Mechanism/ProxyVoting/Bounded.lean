/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.TruthOriented

/-!
# Bounded truth-oriented proxy-voting dynamics

This file contains the non-monotone infrastructure for Bielous–Meir's
truth-oriented safety theorem.  The invariant is weaker than the peak-anchored
invariant for monotone dynamics: reports are only bounded by the initial
`Delta` band around the truthful population median (`WeakPeakBand`, with
median-peaked proxies controlled on both sides), and the initial winner never
crosses past its own peak (`InitialWinnerAnchored`).

Structural geometry: every peak lies at distance at least `Delta` from the
truthful population median (`initialDelta_le_abs_peak_sub` — the truthful
winner's peak is the nearest), so the open `Delta` band around the median
contains no peaks at all, and the band invariant in fact confines each report
to the median side of its own peak's `Delta`-shifted boundary.

The outcome is band-bounded at every invariant state
(`outcome_mem_band_of_strongBandInvariant`), so every better response of a
weak-left-family proxy strictly lowers the outcome and mirror.  Step
preservation splits into two forcing theorems, both of which conclude that
truthful reporting is a weakly best better response.  For an initial-winner
drift (`truthWeaklyBestAmongBetterResponses_of_initialWinnerDriftReport`),
truth and the drift share a median, so the truthful outcome is the winner's
peak or the drift outcome; landing strictly beyond the truth-state median
would place the current outcome strictly between the peak and the drift
outcome, refuting the drift.  For a band violation
(`truthWeaklyBestAmongBetterResponses_of_bandViolatingReport`), the truthful
outcome again stays weakly on the peak's side of the truth-state median —
otherwise the truth-state winner's report caps the current median while the
violation's winner sits strictly below it, above the truthful outcome — and
in both cases the truth-state winner's surviving report caps every
alternative report, not merely every better response.

Together these discharge the forcing hypothesis unconditionally: truth-oriented
better-response dynamics preserve the invariant
(`strongBandInvariant_of_isTruthOrientedDynamics`, Theorem 3), and the median
and outcome stay in the closed `Delta` band
(`median_and_outcome_mem_band_of_isTruthOrientedDynamics`, Corollary 1).

The finite configurations showing that the band alone does not force truth
and that band violations can be better responses live in
`GameTheory.Mechanism.ProxyVoting.Counterexamples`.
-/

namespace GameTheory

namespace ProxyVoting

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]

section Bounded

variable {pp : P → ℝ} {q : F → ℝ}

/-- The initial distance between the truthful population median and the
truthful winning position. -/
noncomputable def initialDelta (pp : P → ℝ) (q : F → ℝ) : ℝ :=
  |outcome pp q - socialMedian pp q|

/-- A state satisfies the weak `Delta`-band report invariant when every proxy
whose peak is weakly left of the truthful median reports at most `Delta` to the
right of it, and every proxy whose peak is weakly right reports at most `Delta`
to the left of it.  Median-peaked proxies are therefore bounded on both sides. -/
def WeakPeakBand (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  ∀ j,
    (pp j ≤ socialMedian pp q → s j ≤ socialMedian pp q + initialDelta pp q) ∧
      (socialMedian pp q ≤ pp j → socialMedian pp q - initialDelta pp q ≤ s j)

/-- The initial winner has not crossed past its truthful winning position. -/
def InitialWinnerAnchored (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  (outcome pp q ≤ socialMedian pp q → outcome pp q ≤ s (winner pp q)) ∧
    (socialMedian pp q ≤ outcome pp q → s (winner pp q) ≤ outcome pp q)

/-- The invariant carried by the non-monotone Theorem 3: the weak report
band together with the Lemma-2 initial-winner drift clause. -/
def StrongBandInvariant (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  WeakPeakBand pp q s ∧ InitialWinnerAnchored pp q s

/-- A truth-oriented better-response step without the monotonicity restriction. -/
def TruthOrientedStep (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ TruthOrientedChoice pp q s j r ∧
    s' = Function.update s j r

/-- Truth-oriented better-response dynamics from the truthful state, without
the monotonicity restriction.  Rest steps are allowed as in the monotone layer. -/
def IsTruthOrientedDynamics (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp ∧
    ∀ t, TruthOrientedStep pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

/-- A report violates the weak `Delta` band if it crosses the forbidden side
for one of the two weak peak families. -/
def BandViolatingReport (pp : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) : Prop :=
  (pp j ≤ socialMedian pp q ∧ socialMedian pp q + initialDelta pp q < r) ∨
    (socialMedian pp q ≤ pp j ∧ r < socialMedian pp q - initialDelta pp q)

/-- A report by the initial winner violates the Lemma-2 drift clause. -/
def InitialWinnerDriftReport (pp : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) : Prop :=
  j = winner pp q ∧
    ((outcome pp q ≤ socialMedian pp q ∧ r < outcome pp q) ∨
      (socialMedian pp q ≤ outcome pp q ∧ outcome pp q < r))

theorem initialDelta_nonneg (pp : P → ℝ) (q : F → ℝ) :
    0 ≤ initialDelta pp q := by
  simp [initialDelta]

/-- Every peak lies at distance at least `Delta` from the truthful population
median: the truthful winner's peak is the nearest one, and its distance is
`Delta` by definition.  Consequently the open `Delta` band around the median
contains no peaks. -/
theorem initialDelta_le_abs_peak_sub (pp : P → ℝ) (q : F → ℝ) (k : P) :
    initialDelta pp q ≤ |pp k - socialMedian pp q| :=
  delegate_dist_le pp (socialMedian pp q) k

/-- A peak weakly left of the truthful median is at least `Delta` left of it. -/
theorem peak_le_sub_initialDelta_of_le {k : P} (h : pp k ≤ socialMedian pp q) :
    pp k ≤ socialMedian pp q - initialDelta pp q := by
  have hd := initialDelta_le_abs_peak_sub pp q k
  rw [abs_of_nonpos (by linarith)] at hd
  linarith

/-- A peak weakly right of the truthful median is at least `Delta` right of it. -/
theorem add_initialDelta_le_peak_of_le {k : P} (h : socialMedian pp q ≤ pp k) :
    socialMedian pp q + initialDelta pp q ≤ pp k := by
  have hd := initialDelta_le_abs_peak_sub pp q k
  rw [abs_of_nonneg (by linarith)] at hd
  linarith

theorem sub_initialDelta_le_socialMedian (pp : P → ℝ) (q : F → ℝ) :
    socialMedian pp q - initialDelta pp q ≤ socialMedian pp q := by
  linarith [initialDelta_nonneg pp q]

theorem socialMedian_le_add_initialDelta (pp : P → ℝ) (q : F → ℝ) :
    socialMedian pp q ≤ socialMedian pp q + initialDelta pp q := by
  linarith [initialDelta_nonneg pp q]

theorem weakPeakBand_self (pp : P → ℝ) (q : F → ℝ) : WeakPeakBand pp q pp := by
  intro j
  constructor
  · intro h
    exact le_trans h (socialMedian_le_add_initialDelta pp q)
  · intro h
    exact le_trans (sub_initialDelta_le_socialMedian pp q) h

theorem initialWinnerAnchored_self (pp : P → ℝ) (q : F → ℝ) :
    InitialWinnerAnchored pp q pp := by
  constructor <;> intro _ <;> rfl

theorem strongBandInvariant_self (pp : P → ℝ) (q : F → ℝ) :
    StrongBandInvariant pp q pp :=
  ⟨weakPeakBand_self pp q, initialWinnerAnchored_self pp q⟩

theorem not_bandViolatingReport_truthful (j : P) :
    ¬ BandViolatingReport pp q j (pp j) := by
  rintro (⟨hjm, hlt⟩ | ⟨hmj, hlt⟩)
  · exact absurd (lt_of_lt_of_le hlt (le_trans hjm (socialMedian_le_add_initialDelta pp q)))
      (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt (le_trans (sub_initialDelta_le_socialMedian pp q) hmj) hlt)
      (lt_irrefl _)

theorem not_initialWinnerDriftReport_truthful (j : P) :
    ¬ InitialWinnerDriftReport pp q j (pp j) := by
  rintro ⟨hj, (⟨_hleft, hlt⟩ | ⟨_hright, hlt⟩)⟩
  · rw [hj] at hlt
    exact absurd hlt (lt_irrefl _)
  · rw [hj] at hlt
    exact absurd hlt (lt_irrefl _)

theorem WeakPeakBand.update_of_not_bandViolatingReport {s : P → ℝ} {j : P} {r : ℝ}
    (hband : WeakPeakBand pp q s)
    (hnot : ¬ BandViolatingReport pp q j r) :
    WeakPeakBand pp q (Function.update s j r) := by
  intro k
  by_cases hkj : k = j
  · subst hkj
    constructor
    · intro hkm
      rw [Function.update_self]
      by_contra hle
      exact hnot (Or.inl ⟨hkm, lt_of_not_ge hle⟩)
    · intro hmk
      rw [Function.update_self]
      by_contra hle
      exact hnot (Or.inr ⟨hmk, lt_of_not_ge hle⟩)
  · constructor
    · intro hkm
      rw [Function.update_apply, if_neg hkj]
      exact (hband k).1 hkm
    · intro hmk
      rw [Function.update_apply, if_neg hkj]
      exact (hband k).2 hmk

theorem InitialWinnerAnchored.update_of_not_initialWinnerDriftReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hanchor : InitialWinnerAnchored pp q s)
    (hnot : ¬ InitialWinnerDriftReport pp q j r) :
    InitialWinnerAnchored pp q (Function.update s j r) := by
  constructor
  · intro hleft
    by_cases hj : j = winner pp q
    · rw [Function.update_apply, if_pos hj.symm]
      by_contra hle
      exact hnot ⟨hj, Or.inl ⟨hleft, lt_of_not_ge hle⟩⟩
    · rw [Function.update_apply, if_neg (fun h => hj h.symm)]
      exact hanchor.1 hleft
  · intro hright
    by_cases hj : j = winner pp q
    · rw [Function.update_apply, if_pos hj.symm]
      by_contra hle
      exact hnot ⟨hj, Or.inr ⟨hright, lt_of_not_ge hle⟩⟩
    · rw [Function.update_apply, if_neg (fun h => hj h.symm)]
      exact hanchor.2 hright

theorem StrongBandInvariant.update_of_not_violating {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hband : ¬ BandViolatingReport pp q j r)
    (hanchor : ¬ InitialWinnerDriftReport pp q j r) :
    StrongBandInvariant pp q (Function.update s j r) :=
  ⟨hinv.1.update_of_not_bandViolatingReport hband,
    hinv.2.update_of_not_initialWinnerDriftReport hanchor⟩

theorem strongBandInvariant_of_isTruthOrientedDynamics_of_forcing {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamics pp q σ)
    (hforce : ∀ t j r, StrongBandInvariant pp q (σ t) →
      IsBetterResponse pp q (σ t) j r →
        (BandViolatingReport pp q j r ∨ InitialWinnerDriftReport pp q j r) →
          TruthWeaklyBestAmongBetterResponses pp q (σ t) j) :
    ∀ t, StrongBandInvariant pp q (σ t) := by
  intro t
  induction t with
  | zero =>
      rw [hdyn.1]
      exact strongBandInvariant_self pp q
  | succ t ih =>
      rcases hdyn.2 t with hstep | hrest
      · obtain ⟨j, r, hbr, htruth, hs'⟩ := hstep
        rw [hs']
        refine ih.update_of_not_violating ?_ ?_
        · intro hv
          have hbest := hforce t j r ih hbr (Or.inl hv)
          rw [htruth hbest] at hv
          exact not_bandViolatingReport_truthful (pp := pp) (q := q) j hv
        · intro hv
          have hbest := hforce t j r ih hbr (Or.inr hv)
          rw [htruth hbest] at hv
          exact not_initialWinnerDriftReport_truthful (pp := pp) (q := q) j hv
      · rw [hrest]
        exact ih

theorem socialMedian_le_upper_of_weakPeakBand {s : P → ℝ}
    (hband : WeakPeakBand pp q s) :
    socialMedian s q ≤ socialMedian pp q + initialDelta pp q := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_le_of_imp_weightedMedian_lt
    (pos := allPos pp q) (pos' := allPos s q) (w := fun _ : P ⊕ F => 1)
    Math.totalWeight_one_pos ?_
  intro a ha
  cases a with
  | inl j =>
      by_contra hle
      rw [not_lt] at hle
      have hs := (hband j).1 hle
      exact absurd (lt_of_lt_of_le ha hs) (lt_irrefl _)
  | inr i =>
      exact lt_of_le_of_lt (socialMedian_le_add_initialDelta pp q) ha

theorem lower_le_socialMedian_of_weakPeakBand {s : P → ℝ}
    (hband : WeakPeakBand pp q s) :
    socialMedian pp q - initialDelta pp q ≤ socialMedian s q := by
  classical
  unfold socialMedian
  refine Math.le_weightedMedian_of_imp_lt_weightedMedian
    (pos := allPos pp q) (pos' := allPos s q) (w := fun _ : P ⊕ F => 1)
    Math.totalWeight_one_pos ?_
  intro a ha
  cases a with
  | inl j =>
      by_contra hle
      rw [not_lt] at hle
      have hs := (hband j).2 hle
      exact absurd (lt_of_lt_of_le ha hs) (lt_irrefl _)
  | inr i =>
      exact lt_of_lt_of_le ha (sub_initialDelta_le_socialMedian pp q)

/-- The report-band invariant pins the current population median inside the
initial `Delta` band. -/
theorem socialMedian_mem_initialDelta_band_of_weakPeakBand {s : P → ℝ}
    (hband : WeakPeakBand pp q s) :
    socialMedian pp q - initialDelta pp q ≤ socialMedian s q ∧
      socialMedian s q ≤ socialMedian pp q + initialDelta pp q :=
  ⟨lower_le_socialMedian_of_weakPeakBand hband,
    socialMedian_le_upper_of_weakPeakBand hband⟩

/-- The initial winner's report always lies in the closed `Delta` band: on the
peak's side it is anchored past the peak, on the other side it is banded. -/
theorem initialWinner_report_mem_band {s : P → ℝ}
    (hband : WeakPeakBand pp q s) (hanchor : InitialWinnerAnchored pp q s) :
    socialMedian pp q - initialDelta pp q ≤ s (winner pp q) ∧
      s (winner pp q) ≤ socialMedian pp q + initialDelta pp q := by
  rcases le_total (outcome pp q) (socialMedian pp q) with hleft | hright
  · constructor
    · have h := hanchor.1 hleft
      rw [initialDelta, abs_of_nonpos (sub_nonpos.mpr hleft)]
      have : socialMedian pp q - -(outcome pp q - socialMedian pp q) = outcome pp q := by
        ring
      rw [this]
      exact h
    · exact (hband (winner pp q)).1 (by simpa [outcome] using hleft)
  · constructor
    · exact (hband (winner pp q)).2 (by simpa [outcome] using hright)
    · have h := hanchor.2 hright
      rw [initialDelta, abs_of_nonneg (sub_nonneg.mpr hright)]
      have : socialMedian pp q + (outcome pp q - socialMedian pp q) = outcome pp q := by
        ring
      rw [this]
      exact h

/-- **Corollary 1, outcome upper half** (Bielous–Meir), state form: at any
state satisfying the band and winner-anchor invariants, the outcome does not
exceed the `Delta` band.  If it did, every weak-left-family report would be
pinned strictly below the current median — by delegate optimality against the
out-of-band winner — and together with the followers at most the truthful
median this embeds half the population strictly below the current median,
which is impossible. -/
theorem outcome_le_upper_of_strongBandInvariant {s : P → ℝ}
    (hinv : StrongBandInvariant pp q s) :
    outcome s q ≤ socialMedian pp q + initialDelta pp q := by
  by_contra hO
  rw [not_le] at hO
  have hband := hinv.1
  have hw := initialWinner_report_mem_band hinv.1 hinv.2
  have hms_ub := socialMedian_le_upper_of_weakPeakBand hinv.1
  have hwd := abs_outcome_sub_socialMedian_le s q (winner pp q)
  have hOms : socialMedian s q < outcome s q := lt_of_le_of_lt hms_ub hO
  have habsO : |outcome s q - socialMedian s q| = outcome s q - socialMedian s q :=
    abs_of_pos (by linarith)
  rw [habsO] at hwd
  rcases le_or_gt (socialMedian s q) (s (winner pp q)) with hcase | hcase
  · -- The winner's banded report caps the outcome directly.
    rw [abs_of_nonneg (by linarith)] at hwd
    linarith [hw.2]
  · rw [abs_of_neg (by linarith)] at hwd
    rcases le_or_gt (socialMedian s q) (socialMedian pp q) with hmsm | hmsm
    · -- A current median at most the truthful one reflects the outcome into
      -- the band.
      linarith [hw.1]
    · -- Counting: every weak-left-family report sits at most
      -- `max m (2·ms − O) < ms`, so the truthful half-mass at `m` embeds
      -- strictly below the current median.
      have hleft_reports : ∀ k : P, pp k ≤ socialMedian pp q →
          s k ≤ max (socialMedian pp q) (2 * socialMedian s q - outcome s q) := by
        intro k hk
        have hdk := abs_outcome_sub_socialMedian_le s q k
        rw [habsO] at hdk
        rcases le_or_gt (s k) (socialMedian s q) with hks | hks
        · rw [abs_of_nonpos (by linarith)] at hdk
          exact le_max_of_le_right (by linarith)
        · rw [abs_of_pos (by linarith)] at hdk
          have hkb := (hband k).1 hk
          linarith
      have hcum : Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian pp q)
          ≤ Math.cumWeight (allPos s q) (fun _ => 1)
            (max (socialMedian pp q) (2 * socialMedian s q - outcome s q)) := by
        refine Math.cumWeight_le_cumWeight_of_imp _ ?_
        intro a ha
        rcases a with k | i
        · exact hleft_reports k ha
        · exact le_trans ha (le_max_left _ _)
      have hqual : Math.totalWeight (fun _ : P ⊕ F => 1)
          ≤ 2 * Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian pp q) :=
        Math.totalWeight_le_two_mul_cumWeight_weightedMedian (allPos pp q) _
      have hx₀ : max (socialMedian pp q) (2 * socialMedian s q - outcome s q)
          < socialMedian s q := max_lt hmsm (by linarith)
      have hstrict : 2 * Math.cumWeight (allPos s q) (fun _ => 1)
            (max (socialMedian pp q) (2 * socialMedian s q - outcome s q))
          < Math.totalWeight (fun _ : P ⊕ F => 1) :=
        Math.two_mul_cumWeight_lt_of_lt_weightedMedian Math.totalWeight_one_pos hx₀
      omega

/-- **Corollary 1, outcome lower half** (Bielous–Meir), state form: at any
state satisfying the band and winner-anchor invariants, the outcome does not
fall below the `Delta` band.  If it did, no report at all could sit at or
below the current median — right-family reports are banded away from the
sub-band winner, and left-family peaks below the current median would put the
current sub-median mass inside the truthful strictly-sub-median mass. -/
theorem lower_le_outcome_of_strongBandInvariant {s : P → ℝ}
    (hinv : StrongBandInvariant pp q s) :
    socialMedian pp q - initialDelta pp q ≤ outcome s q := by
  by_contra hO
  rw [not_le] at hO
  have hband := hinv.1
  have hw := initialWinner_report_mem_band hinv.1 hinv.2
  have hms_lb := lower_le_socialMedian_of_weakPeakBand hinv.1
  have hwd := abs_outcome_sub_socialMedian_le s q (winner pp q)
  have hOms : outcome s q < socialMedian s q := lt_of_lt_of_le hO hms_lb
  have habsO : |outcome s q - socialMedian s q|
      = socialMedian s q - outcome s q := by
    rw [abs_of_neg (by linarith)]
    ring
  rw [habsO] at hwd
  rcases le_or_gt (s (winner pp q)) (socialMedian s q) with hcase | hcase
  · rw [abs_of_nonpos (by linarith)] at hwd
    linarith [hw.1]
  · rw [abs_of_pos (by linarith)] at hwd
    rcases le_or_gt (socialMedian pp q) (socialMedian s q) with hmsm | hmsm
    · linarith [hw.2]
    · have hright_reports : ∀ k : P, socialMedian pp q ≤ pp k →
          ¬ s k ≤ socialMedian s q := by
        intro k hk hks
        have hdk := abs_outcome_sub_socialMedian_le s q k
        rw [habsO, abs_of_nonpos (by linarith)] at hdk
        have hkb := (hband k).2 hk
        linarith
      have hcum : Math.cumWeight (allPos s q) (fun _ => 1) (socialMedian s q)
          ≤ Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian s q) := by
        refine Math.cumWeight_le_cumWeight_of_imp _ ?_
        intro a ha
        rcases a with k | i
        · have hpk : pp k ≤ socialMedian pp q := by
            by_contra hpk'
            rw [not_le] at hpk'
            exact hright_reports k (le_of_lt hpk') ha
          have hsep := peak_le_sub_initialDelta_of_le (pp := pp) (q := q) hpk
          have : allPos pp q (Sum.inl k) = pp k := rfl
          rw [this]
          linarith
        · exact ha
      have hqual : Math.totalWeight (fun _ : P ⊕ F => 1)
          ≤ 2 * Math.cumWeight (allPos s q) (fun _ => 1) (socialMedian s q) :=
        Math.totalWeight_le_two_mul_cumWeight_weightedMedian (allPos s q) _
      have hstrict : 2 * Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian s q)
          < Math.totalWeight (fun _ : P ⊕ F => 1) :=
        Math.two_mul_cumWeight_lt_of_lt_weightedMedian Math.totalWeight_one_pos hmsm
      omega

/-- The outcome at an invariant state lies in the closed `Delta` band. -/
theorem outcome_mem_band_of_strongBandInvariant {s : P → ℝ}
    (hinv : StrongBandInvariant pp q s) :
    socialMedian pp q - initialDelta pp q ≤ outcome s q ∧
      outcome s q ≤ socialMedian pp q + initialDelta pp q :=
  ⟨lower_le_outcome_of_strongBandInvariant hinv,
    outcome_le_upper_of_strongBandInvariant hinv⟩

/-- At an invariant state the outcome is weakly right of every weak-left peak:
peaks are `Delta`-separated from the truthful median and the outcome is
band-bounded. -/
theorem peak_le_outcome_of_strongBandInvariant {s : P → ℝ} {j : P}
    (hinv : StrongBandInvariant pp q s) (hj : pp j ≤ socialMedian pp q) :
    pp j ≤ outcome s q :=
  le_trans (peak_le_sub_initialDelta_of_le hj)
    (lower_le_outcome_of_strongBandInvariant hinv)

/-- At an invariant state the outcome is weakly left of every weak-right peak. -/
theorem outcome_le_peak_of_strongBandInvariant {s : P → ℝ} {j : P}
    (hinv : StrongBandInvariant pp q s) (hj : socialMedian pp q ≤ pp j) :
    outcome s q ≤ pp j :=
  le_trans (outcome_le_upper_of_strongBandInvariant hinv)
    (add_initialDelta_le_peak_of_le hj)

/-- Every better response of a weak-left-family proxy at an invariant state
strictly lowers the outcome: the outcome sits weakly right of the peak, so a
rise or a stall is refuted by single-peakedness. -/
theorem isBetterResponse_outcome_lt_of_peak_le {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r) (hj : pp j ≤ socialMedian pp q) :
    outcome (Function.update s j r) q < outcome s q := by
  have hpO := peak_le_outcome_of_strongBandInvariant hinv hj
  rcases lt_or_eq_of_le hpO with hlt | heq
  · by_contra hle
    rw [not_lt] at hle
    rcases lt_or_eq_of_le hle with hgt | hout
    · exact hbr.2 (Or.inl ⟨le_of_lt hlt, hgt⟩)
    · exact hbr.1 hout.symm
  · exfalso
    rcases lt_trichotomy (outcome (Function.update s j r) q) (outcome s q) with
      hlt | hout | hgt
    · exact hbr.2 (Or.inr ⟨hlt, le_of_eq heq.symm⟩)
    · exact hbr.1 hout
    · exact hbr.2 (Or.inl ⟨le_of_eq heq, hgt⟩)

/-- Every better response of a weak-right-family proxy at an invariant state
strictly raises the outcome. -/
theorem isBetterResponse_lt_outcome_of_le_peak {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r) (hj : socialMedian pp q ≤ pp j) :
    outcome s q < outcome (Function.update s j r) q := by
  have hpO := outcome_le_peak_of_strongBandInvariant hinv hj
  rcases lt_or_eq_of_le hpO with hlt | heq
  · by_contra hle
    rw [not_lt] at hle
    rcases lt_or_eq_of_le hle with hgt | hout
    · exact hbr.2 (Or.inr ⟨hgt, le_of_lt hlt⟩)
    · exact hbr.1 hout
  · exfalso
    rcases lt_trichotomy (outcome (Function.update s j r) q) (outcome s q) with
      hlt | hout | hgt
    · exact hbr.2 (Or.inr ⟨hlt, le_of_eq heq⟩)
    · exact hbr.1 hout
    · exact hbr.2 (Or.inl ⟨le_of_eq heq.symm, hgt⟩)

/-- A weak-left-family proxy with a better response has its peak strictly
below the outcome: at the outcome itself no deviation is acceptable. -/
theorem peak_lt_outcome_of_isBetterResponse_of_peak_le {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r) (hj : pp j ≤ socialMedian pp q) :
    pp j < outcome s q := by
  rcases lt_or_eq_of_le (peak_le_outcome_of_strongBandInvariant hinv hj) with h | h
  · exact h
  · exfalso
    rcases lt_trichotomy (outcome (Function.update s j r) q) (outcome s q) with
      hlt | hout | hgt
    · exact hbr.2 (Or.inr ⟨hlt, le_of_eq h.symm⟩)
    · exact hbr.1 hout
    · exact hbr.2 (Or.inl ⟨le_of_eq h, hgt⟩)

/-- A weak-right-family proxy with a better response has its peak strictly
above the outcome. -/
theorem outcome_lt_peak_of_isBetterResponse_of_le_peak {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r) (hj : socialMedian pp q ≤ pp j) :
    outcome s q < pp j := by
  rcases lt_or_eq_of_le (outcome_le_peak_of_strongBandInvariant hinv hj) with h | h
  · exact h
  · exfalso
    rcases lt_trichotomy (outcome (Function.update s j r) q) (outcome s q) with
      hlt | hout | hgt
    · exact hbr.2 (Or.inr ⟨hlt, le_of_eq h⟩)
    · exact hbr.1 hout
    · exact hbr.2 (Or.inl ⟨le_of_eq h.symm, hgt⟩)

/-- **Winner identification.**  At an invariant state, a band-violating better
response is available only to the current winner: if any other proxy jumps
beyond the band, the previous winning position survives the jump — the winner
at the old median is the old winner or the jump itself, and the median only
moves toward the jump — so the outcome cannot move toward the violator's peak. -/
theorem winner_eq_of_isBetterResponse_of_bandViolating_left
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : pp j ≤ socialMedian pp q)
    (hr : socialMedian pp q + initialDelta pp q < r) :
    winner s q = j := by
  by_contra hkj
  have hlt := isBetterResponse_outcome_lt_of_peak_le hinv hbr hj
  have hOb := outcome_le_upper_of_strongBandInvariant hinv
  have hsj : s j ≤ socialMedian pp q + initialDelta pp q := (hinv.1 j).1 hj
  have hms : socialMedian s q ≤ socialMedian (Function.update s j r) q :=
    socialMedian_le_update_proxy (by linarith)
  have hmono : Function.update s j r
        (delegate (Function.update s j r) (socialMedian s q))
      ≤ outcome (Function.update s j r) q :=
    delegate_pos_mono hms
  rcases update_delegate_eq_new_or_eq_of_delegate_ne (s := s) (j := j) (x := r)
      (m := socialMedian s q) hkj with h | h
  · rw [h] at hmono
    linarith
  · rw [h] at hmono
    have hOO : outcome s q ≤ outcome (Function.update s j r) q := hmono
    linarith

/-- Mirror of `winner_eq_of_isBetterResponse_of_bandViolating_left`. -/
theorem winner_eq_of_isBetterResponse_of_bandViolating_right
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : socialMedian pp q ≤ pp j)
    (hr : r < socialMedian pp q - initialDelta pp q) :
    winner s q = j := by
  by_contra hkj
  have hlt := isBetterResponse_lt_outcome_of_le_peak hinv hbr hj
  have hOb := lower_le_outcome_of_strongBandInvariant hinv
  have hsj : socialMedian pp q - initialDelta pp q ≤ s j := (hinv.1 j).2 hj
  have hms : socialMedian (Function.update s j r) q ≤ socialMedian s q :=
    socialMedian_update_proxy_le (by linarith)
  have hmono : outcome (Function.update s j r) q
      ≤ Function.update s j r
          (delegate (Function.update s j r) (socialMedian s q)) :=
    delegate_pos_mono hms
  rcases update_delegate_eq_new_or_eq_of_delegate_ne (s := s) (j := j) (x := r)
      (m := socialMedian s q) hkj with h | h
  · rw [h] at hmono
    linarith
  · rw [h] at hmono
    have hOO : outcome (Function.update s j r) q ≤ outcome s q := hmono
    linarith

/-- The truthful outcome under a left band violation is at most the peak or at
most the violation's outcome: the truth-state winner at the violation-state
median is the peak or the violation winner, and truth's median is lower. -/
theorem truth_outcome_le_peak_or_violation_left
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : pp j ≤ socialMedian pp q)
    (hr : socialMedian pp q + initialDelta pp q < r) :
    outcome (Function.update s j (pp j)) q ≤ pp j ∨
      outcome (Function.update s j (pp j)) q ≤ outcome (Function.update s j r) q := by
  have hO'lt := isBetterResponse_outcome_lt_of_peak_le hinv hbr hj
  have hOb := outcome_le_upper_of_strongBandInvariant hinv
  -- The violation-state winner is not the violator: its position is below `r`.
  have hne : delegate (Function.update s j r)
      (socialMedian (Function.update s j r) q) ≠ j := by
    intro h
    have hout : outcome (Function.update s j r) q = r := by
      unfold outcome winner
      rw [h]
      exact Function.update_self ..
    rw [hout] at hO'lt
    linarith
  -- Truth's median is at most the violation's median.
  have hmed : socialMedian (Function.update s j (pp j)) q
      ≤ socialMedian (Function.update s j r) q := by
    have h := socialMedian_le_update_proxy (s := Function.update s j (pp j))
      (q := q) (j := j) (r := r)
      (by rw [Function.update_self]; linarith [socialMedian_le_add_initialDelta pp q])
    rwa [Function.update_idem] at h
  have hdich := update_delegate_eq_new_or_eq_of_delegate_ne
    (s := Function.update s j r) (j := j) (x := pp j)
    (m := socialMedian (Function.update s j r) q) hne
  rw [Function.update_idem] at hdich
  have hmono : outcome (Function.update s j (pp j)) q
      ≤ Function.update s j (pp j)
          (delegate (Function.update s j (pp j))
            (socialMedian (Function.update s j r) q)) :=
    delegate_pos_mono hmed
  rcases hdich with h | h
  · left
    rw [h] at hmono
    exact hmono
  · right
    rw [h] at hmono
    exact hmono

/-- **Truth answers the violation.**  At an invariant state, whenever a
weak-left-family proxy has a band-violating better response, truthful
reporting is also a better response. -/
theorem truth_isBetterResponse_of_bandViolating_left
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : pp j ≤ socialMedian pp q)
    (hr : socialMedian pp q + initialDelta pp q < r) :
    IsBetterResponse pp q s j (pp j) := by
  have hO'lt := isBetterResponse_outcome_lt_of_peak_le hinv hbr hj
  have hpj_lt := peak_lt_outcome_of_isBetterResponse_of_peak_le hinv hbr hj
  have hT_lt : outcome (Function.update s j (pp j)) q < outcome s q := by
    rcases truth_outcome_le_peak_or_violation_left hinv hbr hj hr with h | h
    · linarith
    · linarith
  constructor
  · exact fun h => absurd h (ne_of_lt hT_lt)
  · rintro (⟨_, hOT⟩ | ⟨_, hOp⟩)
    · linarith
    · linarith

/-- Mirror of `truth_outcome_le_peak_or_violation_left`. -/
theorem peak_or_violation_le_truth_outcome_right
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : socialMedian pp q ≤ pp j)
    (hr : r < socialMedian pp q - initialDelta pp q) :
    pp j ≤ outcome (Function.update s j (pp j)) q ∨
      outcome (Function.update s j r) q ≤ outcome (Function.update s j (pp j)) q := by
  have hO'lt := isBetterResponse_lt_outcome_of_le_peak hinv hbr hj
  have hOb := lower_le_outcome_of_strongBandInvariant hinv
  have hne : delegate (Function.update s j r)
      (socialMedian (Function.update s j r) q) ≠ j := by
    intro h
    have hout : outcome (Function.update s j r) q = r := by
      unfold outcome winner
      rw [h]
      exact Function.update_self ..
    rw [hout] at hO'lt
    linarith
  have hmed : socialMedian (Function.update s j r) q
      ≤ socialMedian (Function.update s j (pp j)) q := by
    have h := socialMedian_update_proxy_le (s := Function.update s j (pp j))
      (q := q) (j := j) (r := r)
      (by rw [Function.update_self]; linarith [sub_initialDelta_le_socialMedian pp q])
    rwa [Function.update_idem] at h
  have hdich := update_delegate_eq_new_or_eq_of_delegate_ne
    (s := Function.update s j r) (j := j) (x := pp j)
    (m := socialMedian (Function.update s j r) q) hne
  rw [Function.update_idem] at hdich
  have hmono : Function.update s j (pp j)
        (delegate (Function.update s j (pp j))
          (socialMedian (Function.update s j r) q))
      ≤ outcome (Function.update s j (pp j)) q :=
    delegate_pos_mono hmed
  rcases hdich with h | h
  · left
    rw [h] at hmono
    exact hmono
  · right
    rw [h] at hmono
    exact hmono

/-- Mirror of `truth_isBetterResponse_of_bandViolating_left`. -/
theorem truth_isBetterResponse_of_bandViolating_right
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : socialMedian pp q ≤ pp j)
    (hr : r < socialMedian pp q - initialDelta pp q) :
    IsBetterResponse pp q s j (pp j) := by
  have hO'lt := isBetterResponse_lt_outcome_of_le_peak hinv hbr hj
  have hpj_lt := outcome_lt_peak_of_isBetterResponse_of_le_peak hinv hbr hj
  have hT_gt : outcome s q < outcome (Function.update s j (pp j)) q := by
    rcases peak_or_violation_le_truth_outcome_right hinv hbr hj hr with h | h
    · linarith
    · linarith
  constructor
  · exact fun h => absurd h (ne_of_gt hT_gt)
  · rintro (⟨hpO, hOT⟩ | ⟨hOT, _⟩)
    · linarith
    · linarith

/-- **Violation forcing** (left).  At an invariant state, a band-violating
better response by a weak-left-family proxy forces truthful reporting to be a
weakly best better response.  The truthful outcome stays weakly below the
truth-state median — otherwise the truth-state winner's report would cap the
current median while the violation's winner sits strictly below it, above the
truthful outcome — and from there the truth-state winner's surviving report
caps every deviation from below. -/
theorem truthWeaklyBestAmongBetterResponses_of_bandViolating_left
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : pp j ≤ socialMedian pp q)
    (hr : socialMedian pp q + initialDelta pp q < r) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  have htruth_br := truth_isBetterResponse_of_bandViolating_left hinv hbr hj hr
  by_cases hTp : outcome (Function.update s j (pp j)) q = pp j
  · exact truthWeaklyBestAmongBetterResponses_of_truth_outcome_eq_peak htruth_br hTp
  have hinv_t : StrongBandInvariant pp q (Function.update s j (pp j)) :=
    hinv.update_of_not_violating (not_bandViolatingReport_truthful j)
      (not_initialWinnerDriftReport_truthful j)
  have hpjT : pp j ≤ outcome (Function.update s j (pp j)) q :=
    peak_le_outcome_of_strongBandInvariant hinv_t hj
  have hk3 : winner (Function.update s j (pp j)) q ≠ j := by
    intro h
    apply hTp
    have hout : outcome (Function.update s j (pp j)) q
        = Function.update s j (pp j) (winner (Function.update s j (pp j)) q) := rfl
    rw [hout, h, Function.update_self]
  have hsk3 : s (winner (Function.update s j (pp j)) q)
      = outcome (Function.update s j (pp j)) q := by
    have hout : outcome (Function.update s j (pp j)) q
        = Function.update s j (pp j) (winner (Function.update s j (pp j)) q) := rfl
    rw [hout, Function.update_apply, if_neg hk3]
  have hT_le_mst : outcome (Function.update s j (pp j)) q
      ≤ socialMedian (Function.update s j (pp j)) q := by
    by_contra hlt
    rw [not_le] at hlt
    have hms_le_T : socialMedian s q ≤ outcome (Function.update s j (pp j)) q := by
      have h := socialMedian_update_le_of_lt (s := Function.update s j (pp j))
        (q := q) (j := j) (k := winner (Function.update s j (pp j)) q)
        (x := s j) hk3 hlt
      rwa [Function.update_idem, Function.update_eq_self] at h
    have hO'lt := isBetterResponse_outcome_lt_of_peak_le hinv hbr hj
    have hTO' : outcome (Function.update s j (pp j)) q
        ≤ outcome (Function.update s j r) q :=
      (truth_outcome_le_peak_or_violation_left hinv hbr hj hr).resolve_left
        (fun h => hTp (le_antisymm h hpjT))
    have hk2 : winner (Function.update s j r) q ≠ j := by
      intro h
      have hout : outcome (Function.update s j r) q = r := by
        have hw : outcome (Function.update s j r) q
            = Function.update s j r (winner (Function.update s j r) q) := rfl
        rw [hw, h, Function.update_self]
      have hOb := outcome_le_upper_of_strongBandInvariant hinv
      rw [hout] at hO'lt
      linarith
    have hsk2 : s (winner (Function.update s j r) q)
        = outcome (Function.update s j r) q := by
      have hout : outcome (Function.update s j r) q
          = Function.update s j r (winner (Function.update s j r) q) := rfl
      rw [hout, Function.update_apply, if_neg hk2]
    have hOk2 := abs_outcome_sub_socialMedian_le s q (winner (Function.update s j r) q)
    rw [hsk2] at hOk2
    have hO'ms : outcome (Function.update s j r) q < socialMedian s q := by
      by_contra hge
      rw [not_lt] at hge
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hOk2
      linarith
    linarith
  refine ⟨htruth_br, ?_⟩
  intro u _
  have hT_le_U : outcome (Function.update s j (pp j)) q
      ≤ outcome (Function.update s j u) q := by
    by_contra hUT
    rw [not_le] at hUT
    have hsuk3 : Function.update s j u (winner (Function.update s j (pp j)) q)
        = outcome (Function.update s j (pp j)) q := by
      rw [Function.update_apply, if_neg hk3, hsk3]
    have hd := abs_outcome_sub_socialMedian_le (Function.update s j u) q
      (winner (Function.update s j (pp j)) q)
    rw [hsuk3] at hd
    have hT_le_msu : outcome (Function.update s j (pp j)) q
        ≤ socialMedian (Function.update s j u) q := by
      rcases le_or_gt (pp j) u with hu | hu
      · have h := socialMedian_le_update_proxy (s := Function.update s j (pp j))
          (q := q) (j := j) (r := u) (by rw [Function.update_self]; exact hu)
        rw [Function.update_idem] at h
        exact le_trans hT_le_mst h
      · have hpj_lt_mst : Function.update s j (pp j) j
            < socialMedian (Function.update s j (pp j)) q := by
          rw [Function.update_self]
          rcases lt_or_eq_of_le (le_trans hpjT hT_le_mst) with h | h
          · exact h
          · exact absurd
              (le_antisymm (le_trans hT_le_mst (le_of_eq h.symm)) hpjT) hTp
        have h := socialMedian_update_eq_of_proxy_lt
          (s := Function.update s j (pp j)) (q := q) (j := j) (r := u)
          hpj_lt_mst
          (le_of_lt (lt_of_lt_of_le hu (le_trans hpjT hT_le_mst)))
        rw [Function.update_idem] at h
        rw [h]
        exact hT_le_mst
    have h1 : |outcome (Function.update s j u) q
        - socialMedian (Function.update s j u) q|
        = socialMedian (Function.update s j u) q
          - outcome (Function.update s j u) q := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have h2 : |outcome (Function.update s j (pp j)) q
        - socialMedian (Function.update s j u) q|
        = socialMedian (Function.update s j u) q
          - outcome (Function.update s j (pp j)) q := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [h1, h2] at hd
    linarith
  exact Or.inl ⟨hpjT, hT_le_U⟩

/-- Mirror of `truthWeaklyBestAmongBetterResponses_of_bandViolating_left`. -/
theorem truthWeaklyBestAmongBetterResponses_of_bandViolating_right
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hj : socialMedian pp q ≤ pp j)
    (hr : r < socialMedian pp q - initialDelta pp q) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  have htruth_br := truth_isBetterResponse_of_bandViolating_right hinv hbr hj hr
  by_cases hTp : outcome (Function.update s j (pp j)) q = pp j
  · exact truthWeaklyBestAmongBetterResponses_of_truth_outcome_eq_peak htruth_br hTp
  have hinv_t : StrongBandInvariant pp q (Function.update s j (pp j)) :=
    hinv.update_of_not_violating (not_bandViolatingReport_truthful j)
      (not_initialWinnerDriftReport_truthful j)
  have hpjT : outcome (Function.update s j (pp j)) q ≤ pp j :=
    outcome_le_peak_of_strongBandInvariant hinv_t hj
  have hk3 : winner (Function.update s j (pp j)) q ≠ j := by
    intro h
    apply hTp
    have hout : outcome (Function.update s j (pp j)) q
        = Function.update s j (pp j) (winner (Function.update s j (pp j)) q) := rfl
    rw [hout, h, Function.update_self]
  have hsk3 : s (winner (Function.update s j (pp j)) q)
      = outcome (Function.update s j (pp j)) q := by
    have hout : outcome (Function.update s j (pp j)) q
        = Function.update s j (pp j) (winner (Function.update s j (pp j)) q) := rfl
    rw [hout, Function.update_apply, if_neg hk3]
  have hmst_le_T : socialMedian (Function.update s j (pp j)) q
      ≤ outcome (Function.update s j (pp j)) q := by
    by_contra hlt
    rw [not_le] at hlt
    have hT_le_ms : outcome (Function.update s j (pp j)) q ≤ socialMedian s q := by
      have h := le_socialMedian_update_of_lt (s := Function.update s j (pp j))
        (q := q) (j := j) (k := winner (Function.update s j (pp j)) q)
        (x := s j) hk3 hlt
      rwa [Function.update_idem, Function.update_eq_self] at h
    have hO'lt := isBetterResponse_lt_outcome_of_le_peak hinv hbr hj
    have hTO' : outcome (Function.update s j r) q
        ≤ outcome (Function.update s j (pp j)) q :=
      (peak_or_violation_le_truth_outcome_right hinv hbr hj hr).resolve_left
        (fun h => hTp (le_antisymm hpjT h))
    have hk2 : winner (Function.update s j r) q ≠ j := by
      intro h
      have hout : outcome (Function.update s j r) q = r := by
        have hw : outcome (Function.update s j r) q
            = Function.update s j r (winner (Function.update s j r) q) := rfl
        rw [hw, h, Function.update_self]
      have hOb := lower_le_outcome_of_strongBandInvariant hinv
      rw [hout] at hO'lt
      linarith
    have hsk2 : s (winner (Function.update s j r) q)
        = outcome (Function.update s j r) q := by
      have hout : outcome (Function.update s j r) q
          = Function.update s j r (winner (Function.update s j r) q) := rfl
      rw [hout, Function.update_apply, if_neg hk2]
    have hOk2 := abs_outcome_sub_socialMedian_le s q (winner (Function.update s j r) q)
    rw [hsk2] at hOk2
    have hO'ms : socialMedian s q < outcome (Function.update s j r) q := by
      by_contra hge
      rw [not_lt] at hge
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hOk2
      linarith
    linarith
  refine ⟨htruth_br, ?_⟩
  intro u _
  have hU_le_T : outcome (Function.update s j u) q
      ≤ outcome (Function.update s j (pp j)) q := by
    by_contra hUT
    rw [not_le] at hUT
    have hsuk3 : Function.update s j u (winner (Function.update s j (pp j)) q)
        = outcome (Function.update s j (pp j)) q := by
      rw [Function.update_apply, if_neg hk3, hsk3]
    have hd := abs_outcome_sub_socialMedian_le (Function.update s j u) q
      (winner (Function.update s j (pp j)) q)
    rw [hsuk3] at hd
    have hmsu_le_T : socialMedian (Function.update s j u) q
        ≤ outcome (Function.update s j (pp j)) q := by
      rcases le_or_gt u (pp j) with hu | hu
      · have h := socialMedian_update_proxy_le (s := Function.update s j (pp j))
          (q := q) (j := j) (r := u) (by rw [Function.update_self]; exact hu)
        rw [Function.update_idem] at h
        exact le_trans h hmst_le_T
      · have hpj_gt_mst : socialMedian (Function.update s j (pp j)) q
            < Function.update s j (pp j) j := by
          rw [Function.update_self]
          rcases lt_or_eq_of_le (le_trans hmst_le_T hpjT) with h | h
          · exact h
          · exact absurd
              (le_antisymm hpjT (le_trans (le_of_eq h.symm) hmst_le_T)) hTp
        have h := socialMedian_update_eq_of_proxy_gt
          (s := Function.update s j (pp j)) (q := q) (j := j) (r := u)
          hpj_gt_mst
          (le_of_lt (lt_of_le_of_lt (le_trans hmst_le_T hpjT) hu))
        rw [Function.update_idem] at h
        rw [h]
        exact hmst_le_T
    have h1 : |outcome (Function.update s j u) q
        - socialMedian (Function.update s j u) q|
        = outcome (Function.update s j u) q
          - socialMedian (Function.update s j u) q :=
      abs_of_nonneg (by linarith)
    have h2 : |outcome (Function.update s j (pp j)) q
        - socialMedian (Function.update s j u) q|
        = outcome (Function.update s j (pp j)) q
          - socialMedian (Function.update s j u) q :=
      abs_of_nonneg (by linarith)
    rw [h1, h2] at hd
    linarith
  exact Or.inr ⟨hU_le_T, hpjT⟩

/-- **Violation forcing.**  At an invariant state, any band-violating better
response forces truthful reporting to be a weakly best better response. -/
theorem truthWeaklyBestAmongBetterResponses_of_bandViolatingReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hviol : BandViolatingReport pp q j r) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  rcases hviol with ⟨hj, hr⟩ | ⟨hj, hr⟩
  · exact truthWeaklyBestAmongBetterResponses_of_bandViolating_left hinv hbr hj hr
  · exact truthWeaklyBestAmongBetterResponses_of_bandViolating_right hinv hbr hj hr

theorem lower_band_eq_outcome_of_initial_winner_left
    (hleft : outcome pp q ≤ socialMedian pp q) :
    socialMedian pp q - initialDelta pp q = outcome pp q := by
  rw [initialDelta, abs_of_nonpos (sub_nonpos.mpr hleft)]
  ring

theorem upper_band_eq_outcome_of_initial_winner_right
    (hright : socialMedian pp q ≤ outcome pp q) :
    socialMedian pp q + initialDelta pp q = outcome pp q := by
  rw [initialDelta, abs_of_nonneg (sub_nonneg.mpr hright)]
  ring

private theorem not_bandViolatingReport_initialWinner_left_drift
    {r : ℝ} (hleft : outcome pp q < socialMedian pp q) (hr : r < outcome pp q) :
    ¬ BandViolatingReport pp q (winner pp q) r := by
  rintro (⟨_hpeak, hv⟩ | ⟨hpeak, _hv⟩)
  · have hdelta := socialMedian_le_add_initialDelta pp q
    linarith
  · have hpeak' : socialMedian pp q ≤ outcome pp q := by simpa [outcome] using hpeak
    exact absurd hleft (not_lt.mpr hpeak')

private theorem not_bandViolatingReport_initialWinner_right_drift
    {r : ℝ} (hright : socialMedian pp q < outcome pp q) (hr : outcome pp q < r) :
    ¬ BandViolatingReport pp q (winner pp q) r := by
  rintro (⟨hpeak, _hv⟩ | ⟨_hpeak, hv⟩)
  · have hpeak' : outcome pp q ≤ socialMedian pp q := by simpa [outcome] using hpeak
    exact absurd hright (not_lt.mpr hpeak')
  · have hdelta := sub_initialDelta_le_socialMedian pp q
    linarith

theorem truth_isBetterResponse_of_initialWinner_left_drift
    {s : P → ℝ} {r : ℝ}
    (hband : WeakPeakBand pp q s)
    (hleft : outcome pp q < socialMedian pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : r < outcome pp q) :
    IsBetterResponse pp q s (winner pp q) (pp (winner pp q)) := by
  have hband' : WeakPeakBand pp q (Function.update s (winner pp q) r) :=
    hband.update_of_not_bandViolatingReport
      (not_bandViolatingReport_initialWinner_left_drift hleft hr)
  have hmed_lower := lower_le_socialMedian_of_weakPeakBand hband'
  have hpmed : outcome pp q ≤ socialMedian (Function.update s (winner pp q) r) q := by
    rwa [lower_band_eq_outcome_of_initial_winner_left (le_of_lt hleft)] at hmed_lower
  have hout_or :
      outcome (Function.update s (winner pp q) (pp (winner pp q))) q = outcome pp q ∨
        outcome (Function.update s (winner pp q) (pp (winner pp q))) q =
          outcome (Function.update s (winner pp q) r) q := by
    simpa [outcome] using
      outcome_update_eq_self_or_eq_of_update_lt_of_le (s := s) (q := q)
        (j := winner pp q) (u := r) (p := outcome pp q) hr hpmed
  simpa [outcome] using hbr.truth_of_outcome_eq_peak_or_eq hout_or

/-- For a left-configuration initial winner attempting a drift below its peak,
truthful reporting is weakly best under the forced single-peaked comparison
against every better response.  The crux: if the truthful outcome landed
strictly beyond the truth-state median, the current outcome would lie strictly
between the peak and the drift outcome, refuting the drift as a better
response; so the truthful outcome stays weakly below that median, where the
unchanged truth-state winner caps every deviation from below.  The comparison
holds against every report `u`, not only better responses. -/
theorem truth_outcome_spWeaklyPrefers_of_initialWinner_left_drift
    {s : P → ℝ} {r : ℝ} (u : ℝ)
    (hband : WeakPeakBand pp q s) (hanchor : InitialWinnerAnchored pp q s)
    (hleft : outcome pp q < socialMedian pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : r < outcome pp q) :
    SPWeaklyPrefers (outcome pp q)
      (outcome (Function.update s (winner pp q) (outcome pp q)) q)
      (outcome (Function.update s (winner pp q) u) q) := by
  have hband' : WeakPeakBand pp q (Function.update s (winner pp q) r) :=
    hband.update_of_not_bandViolatingReport
      (not_bandViolatingReport_initialWinner_left_drift hleft hr)
  have hpmed : outcome pp q ≤ socialMedian (Function.update s (winner pp q) r) q := by
    have h := lower_le_socialMedian_of_weakPeakBand hband'
    rwa [lower_band_eq_outcome_of_initial_winner_left (le_of_lt hleft)] at h
  set st := Function.update s (winner pp q) (outcome pp q) with hst
  set T := outcome st q with hTdef
  set mt := socialMedian st q with hmt
  have hstw : st (winner pp q) = outcome pp q := by
    rw [hst]; exact Function.update_self ..
  have hmed_tr : mt = socialMedian (Function.update s (winner pp q) r) q := by
    rw [hmt, hst]
    exact socialMedian_update_eq_of_update_lt_of_le hr hpmed
  have hp_mt : outcome pp q ≤ mt := by rw [hmed_tr]; exact hpmed
  -- The peak branch: truth attains the peak, which is weakly best outright.
  by_cases hTp : T = outcome pp q
  · rw [hTp]
    rcases le_total (outcome pp q) (outcome (Function.update s (winner pp q) u) q) with
      hle | hle
    · exact Or.inl ⟨le_rfl, hle⟩
    · exact Or.inr ⟨hle, le_rfl⟩
  -- Hard branch: truth matches the drift outcome.
  have hTR : T = outcome (Function.update s (winner pp q) r) q := by
    rw [hTdef, hst]
    exact (outcome_update_eq_self_or_eq_of_update_lt_of_le (s := s) (q := q)
      (j := winner pp q) (u := r) (p := outcome pp q) hr hpmed).resolve_left
      (by rw [← hst, ← hTdef]; exact hTp)
  have hTk : T = st (delegate st mt) := rfl
  set k := delegate st mt with hk
  have hkw : k ≠ winner pp q := by
    intro hkeq
    apply hTp
    rw [hTk, hkeq, hst]
    exact Function.update_self ..
  have hsk : s k = T := by
    rw [hTk, hst, Function.update_apply, if_neg hkw]
  have hd_A : |T - mt| ≤ mt - outcome pp q := by
    have h := delegate_dist_le st mt (winner pp q)
    have habs : |st (winner pp q) - mt| = mt - outcome pp q := by
      rw [hstw, abs_of_nonpos (by linarith)]
      ring
    rw [habs] at h
    rw [hTk]
    exact h
  -- The truthful outcome cannot land strictly beyond the truth median:
  -- otherwise the current outcome would refute the drift.
  have hT_le_mt : T ≤ mt := by
    by_contra hlt
    rw [not_le] at hlt
    have hs_eq : Function.update st (winner pp q) (s (winner pp q)) = s := by
      rw [hst, Function.update_idem, Function.update_eq_self]
    have hanchor_w : outcome pp q ≤ s (winner pp q) := hanchor.1 (le_of_lt hleft)
    have hms_ge : mt ≤ socialMedian s q := by
      have h := socialMedian_le_update_proxy (s := st) (q := q)
        (j := winner pp q) (r := s (winner pp q)) (by rw [hstw]; exact hanchor_w)
      rwa [hs_eq, ← hmt] at h
    have hms_le : socialMedian s q ≤ T := by
      have h := socialMedian_update_le_of_lt (s := st) (q := q)
        (j := winner pp q) (k := k) (x := s (winner pp q)) hkw
        (by rw [← hTk, ← hmt]; exact hlt)
      rwa [hs_eq, ← hTk] at h
    have hO := abs_outcome_sub_socialMedian_le s q k
    rw [hsk] at hO
    have habsT : |T - socialMedian s q| = T - socialMedian s q :=
      abs_of_nonneg (by linarith)
    rw [habsT] at hO
    have hOle : outcome s q ≤ T := by
      have := le_abs_self (outcome s q - socialMedian s q)
      linarith
    have hOge : 2 * socialMedian s q - T ≤ outcome s q := by
      have := neg_abs_le (outcome s q - socialMedian s q)
      linarith
    have hT2 : T ≤ 2 * mt - outcome pp q := by
      have habs : |T - mt| = T - mt := abs_of_pos (by linarith)
      rw [habs] at hd_A
      linarith
    have hpO : outcome pp q ≤ outcome s q := by linarith
    have hONE : outcome s q ≠ T := by
      intro h
      exact hbr.1 (by rw [← hTR, ← h])
    have hOltT : outcome s q < T := lt_of_le_of_ne hOle hONE
    exact hbr.2 (Or.inl ⟨hpO, by rw [← hTR]; exact hOltT⟩)
  have hpT : outcome pp q ≤ T := by
    have habs : |T - mt| = mt - T := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs] at hd_A
    linarith
  have hpk_lt_T : outcome pp q < T := lt_of_le_of_ne hpT (Ne.symm hTp)
  have hpk_lt_mt : outcome pp q < mt := lt_of_lt_of_le hpk_lt_T hT_le_mt
  -- The unchanged truth-state winner caps every deviation from below.
  have hsu_st : Function.update st (winner pp q) u = Function.update s (winner pp q) u := by
    rw [hst, Function.update_idem]
  have hsuk : Function.update s (winner pp q) u k = T := by
    rw [Function.update_apply, if_neg hkw, hsk]
  have hT_le_U : T ≤ outcome (Function.update s (winner pp q) u) q := by
    by_contra hUT
    rw [not_le] at hUT
    rcases le_or_gt u mt with hu | hu
    · have hmed_u : socialMedian (Function.update s (winner pp q) u) q = mt := by
        have h := socialMedian_update_eq_of_proxy_lt (s := st) (q := q)
          (j := winner pp q) (r := u)
          (by rw [hstw, ← hmt]; exact hpk_lt_mt) (by rw [← hmt]; exact hu)
        rwa [hsu_st, ← hmt] at h
      have hd := abs_outcome_sub_socialMedian_le (Function.update s (winner pp q) u) q k
      rw [hmed_u, hsuk] at hd
      have h1 : |outcome (Function.update s (winner pp q) u) q - mt|
          = mt - outcome (Function.update s (winner pp q) u) q := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have h2 : |T - mt| = mt - T := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [h1, h2] at hd
      linarith
    · have hmu_ge : mt ≤ socialMedian (Function.update s (winner pp q) u) q := by
        have h := socialMedian_le_update_proxy (s := st) (q := q)
          (j := winner pp q) (r := u)
          (by rw [hstw]; exact le_of_lt (lt_trans hpk_lt_mt hu))
        rwa [hsu_st, ← hmt] at h
      have hd := abs_outcome_sub_socialMedian_le (Function.update s (winner pp q) u) q k
      rw [hsuk] at hd
      have h1 : |outcome (Function.update s (winner pp q) u) q
          - socialMedian (Function.update s (winner pp q) u) q|
          = socialMedian (Function.update s (winner pp q) u) q
            - outcome (Function.update s (winner pp q) u) q := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have h2 : |T - socialMedian (Function.update s (winner pp q) u) q|
          = socialMedian (Function.update s (winner pp q) u) q - T := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [h1, h2] at hd
      linarith
  exact Or.inl ⟨hpT, hT_le_U⟩

/-- Truthful reporting is a weakly best better response whenever the
left-configuration initial winner has a below-peak drift better response. -/
theorem truthWeaklyBestAmongBetterResponses_of_initialWinner_left_drift
    {s : P → ℝ} {r : ℝ}
    (hband : WeakPeakBand pp q s) (hanchor : InitialWinnerAnchored pp q s)
    (hleft : outcome pp q < socialMedian pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : r < outcome pp q) :
    TruthWeaklyBestAmongBetterResponses pp q s (winner pp q) := by
  refine ⟨truth_isBetterResponse_of_initialWinner_left_drift hband hleft hbr hr, ?_⟩
  intro v _
  simpa [outcome] using
    truth_outcome_spWeaklyPrefers_of_initialWinner_left_drift v
      hband hanchor hleft hbr hr

theorem truth_isBetterResponse_of_initialWinner_right_drift
    {s : P → ℝ} {r : ℝ}
    (hband : WeakPeakBand pp q s)
    (hright : socialMedian pp q < outcome pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : outcome pp q < r) :
    IsBetterResponse pp q s (winner pp q) (pp (winner pp q)) := by
  have hband' : WeakPeakBand pp q (Function.update s (winner pp q) r) :=
    hband.update_of_not_bandViolatingReport
      (not_bandViolatingReport_initialWinner_right_drift hright hr)
  have hmed_upper := socialMedian_le_upper_of_weakPeakBand hband'
  have hpmed : socialMedian (Function.update s (winner pp q) r) q ≤ outcome pp q := by
    rwa [upper_band_eq_outcome_of_initial_winner_right (le_of_lt hright)] at hmed_upper
  have hout_or :
      outcome (Function.update s (winner pp q) (pp (winner pp q))) q = outcome pp q ∨
        outcome (Function.update s (winner pp q) (pp (winner pp q))) q =
          outcome (Function.update s (winner pp q) r) q := by
    simpa [outcome] using
      outcome_update_eq_self_or_eq_of_le_of_update_gt (s := s) (q := q)
        (j := winner pp q) (u := r) (p := outcome pp q) hpmed hr
  simpa [outcome] using hbr.truth_of_outcome_eq_peak_or_eq hout_or

/-- Mirror of `truth_outcome_spWeaklyPrefers_of_initialWinner_left_drift` for a
right-configuration initial winner attempting a drift above its peak. -/
theorem truth_outcome_spWeaklyPrefers_of_initialWinner_right_drift
    {s : P → ℝ} {r : ℝ} (u : ℝ)
    (hband : WeakPeakBand pp q s) (hanchor : InitialWinnerAnchored pp q s)
    (hright : socialMedian pp q < outcome pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : outcome pp q < r) :
    SPWeaklyPrefers (outcome pp q)
      (outcome (Function.update s (winner pp q) (outcome pp q)) q)
      (outcome (Function.update s (winner pp q) u) q) := by
  have hband' : WeakPeakBand pp q (Function.update s (winner pp q) r) :=
    hband.update_of_not_bandViolatingReport
      (not_bandViolatingReport_initialWinner_right_drift hright hr)
  have hpmed : socialMedian (Function.update s (winner pp q) r) q ≤ outcome pp q := by
    have h := socialMedian_le_upper_of_weakPeakBand hband'
    rwa [upper_band_eq_outcome_of_initial_winner_right (le_of_lt hright)] at h
  set st := Function.update s (winner pp q) (outcome pp q) with hst
  set T := outcome st q with hTdef
  set mt := socialMedian st q with hmt
  have hstw : st (winner pp q) = outcome pp q := by
    rw [hst]; exact Function.update_self ..
  have hmed_tr : mt = socialMedian (Function.update s (winner pp q) r) q := by
    rw [hmt, hst]
    exact socialMedian_update_eq_of_le_of_update_gt hpmed hr
  have hp_mt : mt ≤ outcome pp q := by rw [hmed_tr]; exact hpmed
  -- The peak branch: truth attains the peak, which is weakly best outright.
  by_cases hTp : T = outcome pp q
  · rw [hTp]
    rcases le_total (outcome pp q) (outcome (Function.update s (winner pp q) u) q) with
      hle | hle
    · exact Or.inl ⟨le_rfl, hle⟩
    · exact Or.inr ⟨hle, le_rfl⟩
  -- Hard branch: truth matches the drift outcome.
  have hTR : T = outcome (Function.update s (winner pp q) r) q := by
    rw [hTdef, hst]
    exact (outcome_update_eq_self_or_eq_of_le_of_update_gt (s := s) (q := q)
      (j := winner pp q) (u := r) (p := outcome pp q) hpmed hr).resolve_left
      (by rw [← hst, ← hTdef]; exact hTp)
  have hTk : T = st (delegate st mt) := rfl
  set k := delegate st mt with hk
  have hkw : k ≠ winner pp q := by
    intro hkeq
    apply hTp
    rw [hTk, hkeq, hst]
    exact Function.update_self ..
  have hsk : s k = T := by
    rw [hTk, hst, Function.update_apply, if_neg hkw]
  have hd_A : |T - mt| ≤ outcome pp q - mt := by
    have h := delegate_dist_le st mt (winner pp q)
    have habs : |st (winner pp q) - mt| = outcome pp q - mt := by
      rw [hstw, abs_of_nonneg (by linarith)]
    rw [habs] at h
    rw [hTk]
    exact h
  -- The truthful outcome cannot land strictly beyond the truth median:
  -- otherwise the current outcome would refute the drift.
  have hmt_le_T : mt ≤ T := by
    by_contra hlt
    rw [not_le] at hlt
    have hs_eq : Function.update st (winner pp q) (s (winner pp q)) = s := by
      rw [hst, Function.update_idem, Function.update_eq_self]
    have hanchor_w : s (winner pp q) ≤ outcome pp q := hanchor.2 (le_of_lt hright)
    have hms_le : socialMedian s q ≤ mt := by
      have h := socialMedian_update_proxy_le (s := st) (q := q)
        (j := winner pp q) (r := s (winner pp q)) (by rw [hstw]; exact hanchor_w)
      rwa [hs_eq, ← hmt] at h
    have hms_ge : T ≤ socialMedian s q := by
      have h := le_socialMedian_update_of_lt (s := st) (q := q)
        (j := winner pp q) (k := k) (x := s (winner pp q)) hkw
        (by rw [← hTk, ← hmt]; exact hlt)
      rwa [hs_eq, ← hTk] at h
    have hO := abs_outcome_sub_socialMedian_le s q k
    rw [hsk] at hO
    have habsT : |T - socialMedian s q| = socialMedian s q - T := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habsT] at hO
    have hOge : T ≤ outcome s q := by
      have := neg_abs_le (outcome s q - socialMedian s q)
      linarith
    have hOle : outcome s q ≤ 2 * socialMedian s q - T := by
      have := le_abs_self (outcome s q - socialMedian s q)
      linarith
    have hT2 : 2 * mt - outcome pp q ≤ T := by
      have habs : |T - mt| = mt - T := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs] at hd_A
      linarith
    have hpO : outcome s q ≤ outcome pp q := by linarith
    have hONE : outcome s q ≠ T := by
      intro h
      exact hbr.1 (by rw [← hTR, ← h])
    have hOgtT : T < outcome s q := lt_of_le_of_ne hOge (Ne.symm hONE)
    exact hbr.2 (Or.inr ⟨by rw [← hTR]; exact hOgtT, hpO⟩)
  have hpT : T ≤ outcome pp q := by
    have habs : |T - mt| = T - mt := abs_of_nonneg (by linarith)
    rw [habs] at hd_A
    linarith
  have hpk_gt_T : T < outcome pp q := lt_of_le_of_ne hpT hTp
  have hpk_gt_mt : mt < outcome pp q := lt_of_le_of_lt hmt_le_T hpk_gt_T
  -- The unchanged truth-state winner caps every deviation from above.
  have hsu_st : Function.update st (winner pp q) u = Function.update s (winner pp q) u := by
    rw [hst, Function.update_idem]
  have hsuk : Function.update s (winner pp q) u k = T := by
    rw [Function.update_apply, if_neg hkw, hsk]
  have hU_le_T : outcome (Function.update s (winner pp q) u) q ≤ T := by
    by_contra hUT
    rw [not_le] at hUT
    rcases le_or_gt mt u with hu | hu
    · have hmed_u : socialMedian (Function.update s (winner pp q) u) q = mt := by
        have h := socialMedian_update_eq_of_proxy_gt (s := st) (q := q)
          (j := winner pp q) (r := u)
          (by rw [hstw, ← hmt]; exact hpk_gt_mt) (by rw [← hmt]; exact hu)
        rwa [hsu_st, ← hmt] at h
      have hd := abs_outcome_sub_socialMedian_le (Function.update s (winner pp q) u) q k
      rw [hmed_u, hsuk] at hd
      have h1 : |outcome (Function.update s (winner pp q) u) q - mt|
          = outcome (Function.update s (winner pp q) u) q - mt :=
        abs_of_nonneg (by linarith)
      have h2 : |T - mt| = T - mt := abs_of_nonneg (by linarith)
      rw [h1, h2] at hd
      linarith
    · have hmu_le : socialMedian (Function.update s (winner pp q) u) q ≤ mt := by
        have h := socialMedian_update_proxy_le (s := st) (q := q)
          (j := winner pp q) (r := u)
          (by rw [hstw]; exact le_of_lt (lt_trans hu hpk_gt_mt))
        rwa [hsu_st, ← hmt] at h
      have hd := abs_outcome_sub_socialMedian_le (Function.update s (winner pp q) u) q k
      rw [hsuk] at hd
      have h1 : |outcome (Function.update s (winner pp q) u) q
          - socialMedian (Function.update s (winner pp q) u) q|
          = outcome (Function.update s (winner pp q) u) q
            - socialMedian (Function.update s (winner pp q) u) q :=
        abs_of_nonneg (by linarith)
      have h2 : |T - socialMedian (Function.update s (winner pp q) u) q|
          = T - socialMedian (Function.update s (winner pp q) u) q :=
        abs_of_nonneg (by linarith)
      rw [h1, h2] at hd
      linarith
  exact Or.inr ⟨hU_le_T, hpT⟩

/-- Truthful reporting is a weakly best better response whenever the
right-configuration initial winner has an above-peak drift better response. -/
theorem truthWeaklyBestAmongBetterResponses_of_initialWinner_right_drift
    {s : P → ℝ} {r : ℝ}
    (hband : WeakPeakBand pp q s) (hanchor : InitialWinnerAnchored pp q s)
    (hright : socialMedian pp q < outcome pp q)
    (hbr : IsBetterResponse pp q s (winner pp q) r)
    (hr : outcome pp q < r) :
    TruthWeaklyBestAmongBetterResponses pp q s (winner pp q) := by
  refine ⟨truth_isBetterResponse_of_initialWinner_right_drift hband hright hbr hr, ?_⟩
  intro v _
  simpa [outcome] using
    truth_outcome_spWeaklyPrefers_of_initialWinner_right_drift v
      hband hanchor hright hbr hr

/-- **Drift forcing.**  At a `StrongBandInvariant` state, a drift better
response by the initial winner that does not already violate the report band
makes truthful reporting a weakly best better response.  A drift when the
truthful winner sits exactly at the population median is band-violating, so
the two forcing cases together cover every drift. -/
theorem truthWeaklyBestAmongBetterResponses_of_initialWinnerDriftReport
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hdrift : InitialWinnerDriftReport pp q j r)
    (hnotband : ¬ BandViolatingReport pp q j r) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  obtain ⟨hj, hcase⟩ := hdrift
  subst hj
  rcases hcase with ⟨hleft_le, hr⟩ | ⟨hright_le, hr⟩
  · rcases lt_or_eq_of_le hleft_le with hleft | heq
    · exact truthWeaklyBestAmongBetterResponses_of_initialWinner_left_drift
        hinv.1 hinv.2 hleft hbr hr
    · exfalso
      apply hnotband
      right
      have hdelta : initialDelta pp q = 0 := by
        rw [initialDelta, heq, sub_self, abs_zero]
      refine ⟨by simpa [outcome] using le_of_eq heq.symm, ?_⟩
      rw [hdelta, sub_zero, ← heq]
      exact hr
  · rcases lt_or_eq_of_le hright_le with hright | heq
    · exact truthWeaklyBestAmongBetterResponses_of_initialWinner_right_drift
        hinv.1 hinv.2 hright hbr hr
    · exfalso
      apply hnotband
      left
      have hdelta : initialDelta pp q = 0 := by
        rw [initialDelta, ← heq, sub_self, abs_zero]
      refine ⟨by simpa [outcome] using le_of_eq heq.symm, ?_⟩
      rw [hdelta, add_zero, heq]
      exact hr

/-- **The forcing hypothesis holds.**  At an invariant state, every violating
better response — band-violating or initial-winner drift — forces truthful
reporting to be a weakly best better response. -/
theorem truthWeaklyBestAmongBetterResponses_of_violating
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponse pp q s j r)
    (hviol : BandViolatingReport pp q j r ∨ InitialWinnerDriftReport pp q j r) :
    TruthWeaklyBestAmongBetterResponses pp q s j := by
  by_cases hband : BandViolatingReport pp q j r
  · exact truthWeaklyBestAmongBetterResponses_of_bandViolatingReport hinv hbr hband
  · rcases hviol with h | hdrift
    · exact absurd h hband
    · exact truthWeaklyBestAmongBetterResponses_of_initialWinnerDriftReport
        hinv hbr hdrift hband

/-- **Theorem 3** (Bielous-Meir).  Truth-oriented better-response dynamics
from the truthful state preserve the band and winner-anchor invariants: every
report stays on the allowed side of the `Delta` band around the truthful
population median, and the initial winner never crosses past its peak. -/
theorem strongBandInvariant_of_isTruthOrientedDynamics {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamics pp q σ) (t : ℕ) :
    StrongBandInvariant pp q (σ t) :=
  strongBandInvariant_of_isTruthOrientedDynamics_of_forcing hdyn
    (fun _ _ _ hinv hbr hviol =>
      truthWeaklyBestAmongBetterResponses_of_violating hinv hbr hviol) t

/-- **Corollary 1** (Bielous-Meir).  Along a truth-oriented better-response
dynamics from the truthful state, the current population median and the
current outcome stay in the closed `Delta` band around the truthful
population median. -/
theorem median_and_outcome_mem_band_of_isTruthOrientedDynamics {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamics pp q σ) (t : ℕ) :
    (socialMedian pp q - initialDelta pp q ≤ socialMedian (σ t) q ∧
        socialMedian (σ t) q ≤ socialMedian pp q + initialDelta pp q) ∧
      (socialMedian pp q - initialDelta pp q ≤ outcome (σ t) q ∧
        outcome (σ t) q ≤ socialMedian pp q + initialDelta pp q) := by
  have hinv := strongBandInvariant_of_isTruthOrientedDynamics hdyn t
  exact ⟨socialMedian_mem_initialDelta_band_of_weakPeakBand hinv.1,
    outcome_mem_band_of_strongBandInvariant hinv⟩

end Bounded

end ProxyVoting

end GameTheory
