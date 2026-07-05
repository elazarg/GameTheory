/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Bounded
import GameTheory.Mechanism.ProxyVoting.PartialInformation
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.IntervalCases

/-!
# Counterexamples for the added hypotheses

Machine-checked finite configurations showing that the hypotheses this
formalization adds to Bielous–Meir's statements are necessary.

* `metaMove_not_dist_lt_without_peak_separation` — Lemma 4's strict
  meta-move decrease fails without peak separation: a mover whose peak lies
  strictly inside the winner's interval can take the win and finish exactly
  on the old winning position, every step a better response in the
  preference-free single-peaked-existence sense.  For fixed transitive
  preferences, see `metaMoveFor_dist_lt_of_strictTrans`.
* `weakBandForcingCounterexample_truth_not_weaklyBest` — the weak report
  band alone does not force truth at a drifted state: the Lemma-2
  winner-drift clause of `StrongBandInvariant` is load-bearing.
* `strongBandInvariant_does_not_refute_bandViolatingReports` — a
  band-violating report can be a strictly beneficial better response even
  at an invariant state: the winning proxy vacates across a mirror tie.
  Theorem 3 therefore cannot proceed by refuting violations; only the
  truth-orientation forcing rules them out.
* `winnerStay_not_isMinimaxRegret` — winner-stay is not minimax-regret when a
  runner-up sits strictly between the winner's reflected peak and its report,
  since vacating hands the win to the runner-up for zero regret at every
  consistent median.
* `moveRight_socialMedian_lt` — a winner on the right of the median
  can move farther right, strong-monotonically and as a dominating
  manipulation, so intersecting the uncertainty with the half-line right
  of its new report would exclude every consistent profile.
* `paperBaseInterval_endpoints_reversed` — the displayed base interval for a
  winner between left and right neighbors has its endpoints reversed.
* `paperMinEndpoint_report_not_dominates` — the displayed non-winner
  dominating-manipulation interval is too wide after refinement: its `min`
  lower endpoint admits reports that never beat the old winner at any
  consistent median.
* `monotoneStep_not_dist_lt_with_mirror_tie` — Lemma 3's strict decrease
  fails under a mirror tie: a monotone better response can hand the win
  across the median to a report at the same distance.  The data is
  integral, so the section-4.4 discretization inherits the same caveat.
* `integral_monotoneStep_not_dist_add_one_le_without_noMirrorTie` — the
  discrete `+1` decrease conclusion itself fails on the same integral
  mirror-tie instance, so a discrete/FBRP convergence theorem needs a
  preserved no-mirror-tie or strict-decrease invariant.
* `integral_truthful_monotoneStep_hits_mirrorTie` — the mirror-tie caveat can
  occur immediately from a truthful integral state, even with distinct proxy
  peaks; integer best-response-from-truth dynamics therefore do not by
  themselves preserve the tie-free invariant.
* `minimaxTrap_minimaxRegretInfo_not_tendsto` — active minimax-regret reports
  over a nested, median-robust information-set sequence do not force
  convergence, even along weak non-crossing winner observations: a right
  endpoint proxy keeps reporting the current upper boundary while the old
  winner, and hence the outcome, never changes.
* `insidePeak_boundary_not_isMinimaxRegret` — Theorem 4's peak-outside
  hypothesis is necessary: with the peak inside the winning interval the
  boundary is not minimax-regret; reporting the peak wins everywhere for
  zero maximal regret (`isMinimaxRegret_peak_of_forall_lt`).
* `knownMedian_no_isMinimaxRegret` — Theorem 4's uncertainty-spread
  hypothesis is necessary: with a known median (degenerate uncertainty)
  no report is minimax-regret at all — the best response approaches the
  mirror of the winner, where the tie-break hands the win back.
* `midBreak_boundary_not_isMinimaxRegret` — Theorem 4's midpoint-spread
  hypothesis is necessary over and above non-degeneracy and peak-outside:
  on the interval `[0, 1]` with winner at `4`, the near boundary `0` is not
  minimax-regret because reporting `-1` has smaller maximal regret.
* `paperDisplayWeightedMedian_rejects_duplicate_median` — the paper's
  displayed weak-inequality/excluding-self weighted-median formula is not
  equivalent to the strict-left/strict-right definition used in the text:
  with three coincident unit-weight positions, the strict definition accepts
  the common position, while the displayed formula rejects every occurrence.
* `unguardedNonAnchoredReportsForceTruth_counterexample` — the forcing lemma
  used by truth-oriented boundedness needs the same-side and fixed-median
  invariants; without them, a non-anchored monotone better response need not
  make truthful reporting a better response.
* `socialCost_and_median_distance_diverge` — the Section 2 footnote is
  witnessed by a truthful profile where the elected proxy is closest to the
  population median, while another proxy has strictly smaller social cost and
  is farther from the median.
-/

namespace GameTheory

namespace ProxyVoting

open Finset
open Filter

/-! ## The paper's displayed weighted-median formula is not duplicate-safe -/

/-- The weak-inequality, excluding-self reading of the paper's displayed
weighted-median formula, for a selected occurrence `i`.  This is intentionally
not the library definition: it is used only to witness the erratum that the
displayed formula disagrees with the surrounding text on repeated positions. -/
def PaperDisplayWeightedMedianAt {α : Type*} [Fintype α] [DecidableEq α]
    (pos : α → ℝ) (w : α → ℕ) (i : α) : Prop :=
  2 * (∑ j ∈ (univ.filter fun j => j ≠ i ∧ pos j ≤ pos i), w j)
      ≤ Math.totalWeight w
    ∧ 2 * (∑ j ∈ (univ.filter fun j => j ≠ i ∧ pos i ≤ pos j), w j)
      ≤ Math.totalWeight w

/-- For three coincident unit-weight positions,
the strict-left/strict-right weighted-median predicate accepts the common
position, but the paper's displayed weak-inequality/excluding-self formula
rejects every occurrence. -/
theorem paperDisplayWeightedMedian_rejects_duplicate_median :
    Math.IsWeightedMedian (fun _ : Fin 3 => (0 : ℝ)) (fun _ => 1) 0 ∧
      ∀ i, ¬ PaperDisplayWeightedMedianAt (fun _ : Fin 3 => (0 : ℝ)) (fun _ => 1) i := by
  constructor
  · norm_num [Math.IsWeightedMedian, Math.leftWeight, Math.rightWeight, Math.totalWeight]
  · intro i h
    have hleft : 2 * (univ.filter fun j : Fin 3 => j ≠ i).card ≤ 3 := by
      simpa [PaperDisplayWeightedMedianAt, Math.totalWeight] using h.1
    have hcard : (univ.filter fun j : Fin 3 => j ≠ i).card = 2 := by
      have hfilter : (univ.filter fun j : Fin 3 => j ≠ i) = univ.erase i := by
        ext j
        simp
      rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      rfl
    rw [hcard] at hleft
    norm_num at hleft

/-! ## The peak-separation hypothesis is necessary -/

/-- Peaks for the meta-move counterexample: the mover's peak `-10` lies
strictly inside the starting winner interval of radius `15`. -/
def metaMovePeaks : Fin 2 → ℝ
  | 0 => -10
  | 1 => -15

/-- Followers pinning the population median at `0`. -/
def metaMoveFollowers : Fin 3 → ℝ
  | 0 => 0
  | _ => 10

/-- The meta-move's starting state: the mover parked at `-16`, the winner
truthful at `-15`. -/
def metaMoveState0 : Fin 2 → ℝ
  | 0 => -16
  | 1 => -15

/-- After the first move the mover has taken the win inside, at `-9`. -/
def metaMoveState1 : Fin 2 → ℝ
  | 0 => -9
  | 1 => -15

/-- After the second move the mover sits exactly on the old winner. -/
def metaMoveState2 : Fin 2 → ℝ
  | 0 => -15
  | 1 => -15

/-- The meta-move as a dynamics. -/
def metaMoveSigma : ℕ → Fin 2 → ℝ
  | 0 => metaMoveState0
  | 1 => metaMoveState1
  | _ => metaMoveState2

private abbrev mPk := metaMovePeaks
private abbrev mFl := metaMoveFollowers
private def mPkPos : Fin 2 ⊕ Fin 3 → ℝ := Sum.elim mPk mFl

private theorem mPkPos_cum_zero : Math.cumWeight mPkPos (fun _ => 1) 0 = 3 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Fin 3 => mPkPos a ≤ 0)
      = {Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2), Sum.inr (0 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [mPkPos, mPk, metaMovePeaks, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [mPkPos, mFl, metaMoveFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem mPkPos_cum_neg_ten :
    Math.cumWeight mPkPos (fun _ => 1) (-10) = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Fin 3 => mPkPos a ≤ -10)
      = {Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [mPkPos, mPk, metaMovePeaks, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [mPkPos, mFl, metaMoveFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem mPkPos_cum_neg_fifteen :
    Math.cumWeight mPkPos (fun _ => 1) (-15) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Fin 3 => mPkPos a ≤ -15)
      = {Sum.inl (1 : Fin 2)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [mPkPos, mPk, metaMovePeaks, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [mPkPos, mFl, metaMoveFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem socialMedian_mPk : socialMedian mPk mFl = 0 := by
  unfold socialMedian
  change Math.weightedMedian mPkPos (fun _ => 1) = 0
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      mPkPos_cum_zero]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    rcases a with j | i
    · fin_cases j
      · change 2 * Math.cumWeight mPkPos (fun _ => 1) (-10) < 5
        rw [mPkPos_cum_neg_ten]
        norm_num
      · change 2 * Math.cumWeight mPkPos (fun _ => 1) (-15) < 5
        rw [mPkPos_cum_neg_fifteen]
        norm_num
    · fin_cases i <;>
        norm_num [mPkPos, mFl, metaMoveFollowers] at hltx

private theorem mState0_eq : metaMoveState0 = Function.update mPk (0 : Fin 2) (-16) := by
  funext j
  fin_cases j <;>
    norm_num [metaMoveState0, mPk, metaMovePeaks, Function.update_apply, Fin.ext_iff]

private theorem mState1_eq :
    Function.update metaMoveState0 (0 : Fin 2) (-9) = metaMoveState1 := by
  funext j
  fin_cases j <;>
    norm_num [metaMoveState0, metaMoveState1, Function.update_apply, Fin.ext_iff]

private theorem mState2_eq :
    Function.update metaMoveState1 (0 : Fin 2) (-15) = metaMoveState2 := by
  funext j
  fin_cases j <;>
    norm_num [metaMoveState1, metaMoveState2, Function.update_apply, Fin.ext_iff]

private theorem socialMedian_mState0 : socialMedian metaMoveState0 mFl = 0 := by
  rw [mState0_eq]
  have h := socialMedian_update_eq_of_proxy_lt (s := mPk) (q := mFl)
    (j := (0 : Fin 2)) (r := -16)
    (by rw [socialMedian_mPk]; norm_num [mPk, metaMovePeaks])
    (by rw [socialMedian_mPk]; norm_num)
  rw [h, socialMedian_mPk]

private theorem socialMedian_mState1 : socialMedian metaMoveState1 mFl = 0 := by
  rw [← mState1_eq]
  have h := socialMedian_update_eq_of_proxy_lt (s := metaMoveState0) (q := mFl)
    (j := (0 : Fin 2)) (r := -9)
    (by rw [socialMedian_mState0]; norm_num [metaMoveState0])
    (by rw [socialMedian_mState0]; norm_num)
  rw [h, socialMedian_mState0]

private theorem socialMedian_mState2 : socialMedian metaMoveState2 mFl = 0 := by
  rw [← mState2_eq]
  have h := socialMedian_update_eq_of_proxy_lt (s := metaMoveState1) (q := mFl)
    (j := (0 : Fin 2)) (r := -15)
    (by rw [socialMedian_mState1]; norm_num [metaMoveState1])
    (by rw [socialMedian_mState1]; norm_num)
  rw [h, socialMedian_mState1]

private theorem delegate_mState0 : delegate metaMoveState0 0 = 1 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [metaMoveState0]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    fin_cases b
    · have hb1 := hb (1 : Fin 2)
      norm_num [metaMoveState0] at hb1
    · exact le_rfl

private theorem delegate_mState1 : delegate metaMoveState1 0 = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [metaMoveState1]
  · intro b _
    exact Fin.zero_le b

private theorem delegate_mState2 : delegate metaMoveState2 0 = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [metaMoveState2]
  · intro b _
    exact Fin.zero_le b

private theorem winner_mState0 : winner metaMoveState0 mFl = 1 := by
  unfold winner
  rw [socialMedian_mState0, delegate_mState0]

private theorem winner_mState1 : winner metaMoveState1 mFl = 0 := by
  unfold winner
  rw [socialMedian_mState1, delegate_mState1]

private theorem winner_mState2 : winner metaMoveState2 mFl = 0 := by
  unfold winner
  rw [socialMedian_mState2, delegate_mState2]

private theorem outcome_mState0 : outcome metaMoveState0 mFl = -15 := by
  unfold outcome
  rw [winner_mState0]
  norm_num [metaMoveState0]

private theorem outcome_mState1 : outcome metaMoveState1 mFl = -9 := by
  unfold outcome
  rw [winner_mState1]
  norm_num [metaMoveState1]

private theorem outcome_mState2 : outcome metaMoveState2 mFl = -15 := by
  unfold outcome
  rw [winner_mState2]
  norm_num [metaMoveState2]

private theorem mMetaMove : MetaMove mPk mFl 0 metaMoveSigma 2 := by
  refine ⟨two_pos, ?_, ?_, ?_⟩
  · change (0 : Fin 2) ≠ winner metaMoveState0 mFl
    rw [winner_mState0]
    decide
  · intro i hi
    interval_cases i
    · refine ⟨-9, ?_, ?_, ?_⟩
      · constructor
        · change outcome (Function.update metaMoveState0 (0 : Fin 2) (-9)) mFl
              ≠ outcome metaMoveState0 mFl
          rw [mState1_eq, outcome_mState1, outcome_mState0]
          norm_num
        · change ¬ SPPrefers (mPk 0) (outcome metaMoveState0 mFl)
              (outcome (Function.update metaMoveState0 (0 : Fin 2) (-9)) mFl)
          rw [mState1_eq, outcome_mState1, outcome_mState0]
          norm_num [SPPrefers, mPk, metaMovePeaks]
      · rw [MonotoneReport, socialMedian_mPk]
        norm_num [mPk, metaMovePeaks]
      · change metaMoveState1 = Function.update metaMoveState0 (0 : Fin 2) (-9)
        rw [mState1_eq]
    · refine ⟨-15, ?_, ?_, ?_⟩
      · constructor
        · change outcome (Function.update metaMoveState1 (0 : Fin 2) (-15)) mFl
              ≠ outcome metaMoveState1 mFl
          rw [mState2_eq, outcome_mState2, outcome_mState1]
          norm_num
        · change ¬ SPPrefers (mPk 0) (outcome metaMoveState1 mFl)
              (outcome (Function.update metaMoveState1 (0 : Fin 2) (-15)) mFl)
          rw [mState2_eq, outcome_mState2, outcome_mState1]
          norm_num [SPPrefers, mPk, metaMovePeaks]
      · rw [MonotoneReport, socialMedian_mPk]
        norm_num [mPk, metaMovePeaks]
      · change metaMoveState2 = Function.update metaMoveState1 (0 : Fin 2) (-15)
        rw [mState2_eq]
  · intro i h1 h2
    interval_cases i
    · exact winner_mState1
    · exact winner_mState2

/-- Without the peak-separation hypothesis, the strict Lemma 4 fails: a mover
whose peak lies strictly inside the winner interval takes the win inside and
finishes exactly on the old winning position, so the meta-move ends at the
starting distance.  Every final report coincides, so the no-mirror-tie
hypothesis holds vacuously. -/
theorem metaMove_not_dist_lt_without_peak_separation :
    ∃ (pp : Fin 2 → ℝ) (q : Fin 3 → ℝ) (j : Fin 2) (σ : ℕ → Fin 2 → ℝ) (ℓ : ℕ),
      MetaMove pp q j σ ℓ ∧ SameSide pp q (σ 0)
        ∧ socialMedian (σ 0) q = socialMedian pp q
        ∧ (∀ k k', |σ ℓ k - socialMedian pp q| = |σ ℓ k' - socialMedian pp q|
            → σ ℓ k = σ ℓ k')
        ∧ ¬ |outcome (σ ℓ) q - socialMedian pp q|
            < |outcome (σ 0) q - socialMedian pp q| := by
  refine ⟨mPk, mFl, 0, metaMoveSigma, 2, mMetaMove, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [socialMedian_mPk]
    fin_cases j <;>
      norm_num [metaMoveSigma, metaMoveState0, mPk, metaMovePeaks]
  · change socialMedian metaMoveState0 mFl = socialMedian mPk mFl
    rw [socialMedian_mState0, socialMedian_mPk]
  · intro k k' _
    fin_cases k <;> fin_cases k' <;>
      norm_num [metaMoveSigma, metaMoveState2]
  · change ¬ |outcome metaMoveState2 mFl - socialMedian mPk mFl|
        < |outcome metaMoveState0 mFl - socialMedian mPk mFl|
    rw [outcome_mState2, outcome_mState0, socialMedian_mPk]
    norm_num

/-! ## The report band alone is not enough -/

/-- Peaks for a finite counterexample showing that `WeakPeakBand` alone does not
force truth for every band-violating better response. -/
def weakBandForcingCounterexamplePeaks : Fin 2 → ℝ
  | 0 => -1
  | 1 => 3

/-- Follower profile for `weakBandForcingCounterexamplePeaks`. -/
def weakBandForcingCounterexampleFollowers : Unit → ℝ := fun _ => 0

/-- A banded state that violates the Lemma-2 drift clause: the initial winner
has drifted past its peak while the right proxy remains truthful. -/
def weakBandForcingCounterexampleState : Fin 2 → ℝ
  | 0 => -3
  | 1 => 3

private abbrev bPeaks := weakBandForcingCounterexamplePeaks
private abbrev bFollowers := weakBandForcingCounterexampleFollowers
private abbrev bState := weakBandForcingCounterexampleState
private def bPeakPos : Fin 2 ⊕ Unit → ℝ := Sum.elim bPeaks bFollowers
private def bStatePos : Fin 2 ⊕ Unit → ℝ := Sum.elim bState bFollowers

private theorem bPeakPos_cum_zero : Math.cumWeight bPeakPos (fun _ => 1) 0 = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bPeakPos a ≤ 0)
      = {Sum.inl (0 : Fin 2), Sum.inr Unit.unit} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          simp [bPeakPos, bPeaks, weakBandForcingCounterexamplePeaks]
    | inr u => cases u; simp [bPeakPos, bFollowers, weakBandForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem bPeakPos_cum_neg_one :
    Math.cumWeight bPeakPos (fun _ => 1) (-1) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bPeakPos a ≤ -1)
      = {Sum.inl (0 : Fin 2)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [bPeakPos, bPeaks, weakBandForcingCounterexamplePeaks, Fin.ext_iff]
    | inr u => cases u; simp [bPeakPos, bFollowers, weakBandForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem socialMedian_bPeaks : socialMedian bPeaks bFollowers = 0 := by
  unfold socialMedian
  change Math.weightedMedian bPeakPos (fun _ => 1) = 0
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr Unit.unit, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique,
      bPeakPos_cum_zero]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight bPeakPos (fun _ => 1) (-1) < 3
          rw [bPeakPos_cum_neg_one]
          norm_num
        · norm_num [bPeakPos, bPeaks, weakBandForcingCounterexamplePeaks] at hltx
    | inr u =>
        cases u
        norm_num [bPeakPos, bFollowers, weakBandForcingCounterexampleFollowers] at hltx

private theorem bStatePos_cum_zero : Math.cumWeight bStatePos (fun _ => 1) 0 = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bStatePos a ≤ 0)
      = {Sum.inl (0 : Fin 2), Sum.inr Unit.unit} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          simp [bStatePos, bState, weakBandForcingCounterexampleState]
    | inr u => cases u; simp [bStatePos, bFollowers, weakBandForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem bStatePos_cum_neg_three :
    Math.cumWeight bStatePos (fun _ => 1) (-3) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bStatePos a ≤ -3)
      = {Sum.inl (0 : Fin 2)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [bStatePos, bState, weakBandForcingCounterexampleState, Fin.ext_iff]
    | inr u => cases u; simp [bStatePos, bFollowers, weakBandForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem socialMedian_bState : socialMedian bState bFollowers = 0 := by
  unfold socialMedian
  change Math.weightedMedian bStatePos (fun _ => 1) = 0
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr Unit.unit, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique,
      bStatePos_cum_zero]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight bStatePos (fun _ => 1) (-3) < 3
          rw [bStatePos_cum_neg_three]
          norm_num
        · norm_num [bStatePos, bState, weakBandForcingCounterexampleState] at hltx
    | inr u =>
        cases u
        norm_num [bStatePos, bFollowers, weakBandForcingCounterexampleFollowers] at hltx

private def bSelectedPos : Fin 2 ⊕ Unit → ℝ
  | Sum.inl 0 => -3
  | Sum.inl 1 => -2
  | Sum.inr _ => 0

private theorem bSelectedPos_cum_neg_two :
    Math.cumWeight bSelectedPos (fun _ => 1) (-2) = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bSelectedPos a ≤ -2)
      = {Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [bSelectedPos, Fin.ext_iff]
    | inr u => cases u; simp [bSelectedPos]
  rw [hfilter]
  simp

private theorem bSelectedPos_cum_neg_three :
    Math.cumWeight bSelectedPos (fun _ => 1) (-3) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 2 ⊕ Unit => bSelectedPos a ≤ -3)
      = {Sum.inl (0 : Fin 2)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [bSelectedPos, Fin.ext_iff]
    | inr u => cases u; simp [bSelectedPos]
  rw [hfilter]
  simp

private theorem socialMedian_bSelected :
    socialMedian (Function.update bState (1 : Fin 2) (-2)) bFollowers = -2 := by
  unfold socialMedian
  change Math.weightedMedian bSelectedPos (fun _ => 1) = -2
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inl 1, Finset.mem_univ _, by simp [bSelectedPos]⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
    rw [bSelectedPos_cum_neg_two]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight bSelectedPos (fun _ => 1) (-3) < 3
          rw [bSelectedPos_cum_neg_three]
          norm_num
        · norm_num [bSelectedPos] at hltx
    | inr u =>
        cases u
        norm_num [bSelectedPos] at hltx

private theorem delegate_bPeaks_zero : delegate bPeaks 0 = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [bPeaks, weakBandForcingCounterexamplePeaks]
  · intro b _
    exact Fin.zero_le b

private theorem delegate_bState_zero : delegate bState 0 = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [bState, weakBandForcingCounterexampleState]
  · intro b _
    exact Fin.zero_le b

private theorem delegate_bSelected_neg_two :
    delegate (Function.update bState (1 : Fin 2) (-2)) (-2) = 1 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp [bState, weakBandForcingCounterexampleState, Function.update_apply, Fin.ext_iff]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    fin_cases b
    · have hb1 := hb (1 : Fin 2)
      norm_num [bState, weakBandForcingCounterexampleState, Function.update_apply,
        Fin.ext_iff] at hb1
    · exact le_rfl

private theorem outcome_bPeaks : outcome bPeaks bFollowers = -1 := by
  unfold outcome winner
  rw [socialMedian_bPeaks, delegate_bPeaks_zero]
  rfl

private theorem outcome_bState : outcome bState bFollowers = -3 := by
  unfold outcome winner
  rw [socialMedian_bState, delegate_bState_zero]
  rfl

private theorem outcome_bSelected :
    outcome (Function.update bState (1 : Fin 2) (-2)) bFollowers = -2 := by
  unfold outcome winner
  rw [socialMedian_bSelected, delegate_bSelected_neg_two]
  simp

private theorem outcome_bTruth :
    outcome (Function.update bState (1 : Fin 2) (bPeaks 1)) bFollowers = -3 := by
  have hupdate : Function.update bState (1 : Fin 2) (bPeaks 1) = bState := by
    funext j
    fin_cases j <;> simp [bState, bPeaks, weakBandForcingCounterexampleState,
      weakBandForcingCounterexamplePeaks]
  rw [hupdate, outcome_bState]

theorem weakBandForcingCounterexample_band :
    WeakPeakBand bPeaks bFollowers bState := by
  intro j
  fin_cases j <;>
    norm_num [WeakPeakBand, initialDelta, socialMedian_bPeaks, outcome_bPeaks,
      bPeaks, bState, weakBandForcingCounterexamplePeaks,
      weakBandForcingCounterexampleState]

theorem weakBandForcingCounterexample_not_initialWinnerAnchored :
    ¬ InitialWinnerAnchored bPeaks bFollowers bState := by
  intro h
  have hleft := h.1 (by rw [outcome_bPeaks, socialMedian_bPeaks]; norm_num)
  rw [outcome_bPeaks] at hleft
  unfold winner at hleft
  rw [socialMedian_bPeaks, delegate_bPeaks_zero] at hleft
  norm_num [bState, weakBandForcingCounterexampleState] at hleft

theorem weakBandForcingCounterexample_selected_isBetterResponse :
    IsBetterResponse bPeaks bFollowers bState (1 : Fin 2) (-2) := by
  constructor
  · rw [outcome_bSelected, outcome_bState]
    norm_num
  · intro hsp
    norm_num [SPPrefers, bPeaks, weakBandForcingCounterexamplePeaks, outcome_bState,
      outcome_bSelected] at hsp

theorem weakBandForcingCounterexample_selected_violates :
    BandViolatingReport bPeaks bFollowers (1 : Fin 2) (-2) := by
  right
  norm_num [BandViolatingReport, initialDelta, socialMedian_bPeaks, outcome_bPeaks,
    bPeaks, weakBandForcingCounterexamplePeaks]

theorem weakBandForcingCounterexample_truth_not_weaklyBest :
    ¬ TruthWeaklyBestAmongBetterResponses bPeaks bFollowers bState (1 : Fin 2) := by
  intro h
  exact h.1.1 (by rw [outcome_bTruth, outcome_bState])

/-- The weak report band, by itself, does not imply the local forcing lemma
needed for Theorem 3.  The missing invariant must exclude states like this one,
where a far-left current winner makes a right-peaked proxy's forbidden
leftward move a better response while truthful reporting leaves the outcome
unchanged. -/
theorem weakPeakBand_does_not_force_bandViolatingReports :
    ∃ (s : Fin 2 → ℝ) (j : Fin 2) (r : ℝ),
      WeakPeakBand bPeaks bFollowers s ∧
        IsBetterResponse bPeaks bFollowers s j r ∧
        BandViolatingReport bPeaks bFollowers j r ∧
        ¬ TruthWeaklyBestAmongBetterResponses bPeaks bFollowers s j := by
  exact ⟨bState, 1, -2, weakBandForcingCounterexample_band,
    weakBandForcingCounterexample_selected_isBetterResponse,
    weakBandForcingCounterexample_selected_violates,
    weakBandForcingCounterexample_truth_not_weaklyBest⟩

/-! ## Band violations can be better responses

Even at a `StrongBandInvariant` state, a band-violating report can be a
better response: a winning proxy that vacates the winning position can hand
the outcome across a mirror tie to a report it strictly prefers, and the
vacating report itself may land anywhere — in particular outside the band.
So band violations cannot be refuted as better responses outright; only the
truth-orientation forcing rules them out. -/

/-- Peaks for the finite example of a band-violating better response at an
invariant state. -/
def violatingBRPeaks : Fin 3 → ℝ
  | 0 => -1
  | 1 => 3
  | 2 => -2

/-- Follower profile for `violatingBRPeaks`. -/
def violatingBRFollowers : Fin 2 → ℝ := fun _ => 1

/-- An invariant state where proxy `2` wins at position `0` and prefers to
vacate: any far-away report hands the win to the mirror tie at `±2` around
the median, which breaks to proxy `0` at `-1`. -/
def violatingBRState : Fin 3 → ℝ
  | 0 => -1
  | 1 => 3
  | 2 => 0

private abbrev vPeaks := violatingBRPeaks
private abbrev vFollowers := violatingBRFollowers
private abbrev vState := violatingBRState
private def vPeakPos : Fin 3 ⊕ Fin 2 → ℝ := Sum.elim vPeaks vFollowers
private def vStatePos : Fin 3 ⊕ Fin 2 → ℝ := Sum.elim vState vFollowers
/-- The violation state written out: proxy `2` has vacated to `10`. -/
private def vViolState : Fin 3 → ℝ
  | 0 => -1
  | 1 => 3
  | 2 => 10

private theorem vViolState_eq :
    Function.update vState (2 : Fin 3) 10 = vViolState := by
  funext j
  fin_cases j <;>
    norm_num [vState, violatingBRState, vViolState, Function.update_apply, Fin.ext_iff]

private def vViolPos : Fin 3 ⊕ Fin 2 → ℝ := Sum.elim vViolState vFollowers

private theorem vPeakPos_cum_one : Math.cumWeight vPeakPos (fun _ => 1) 1 = 4 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vPeakPos a ≤ 1)
      = {Sum.inl (0 : Fin 3), Sum.inl (2 : Fin 3),
          Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vPeakPos, vPeaks, violatingBRPeaks, Fin.ext_iff]
      simp
    · fin_cases i <;>
        norm_num [vPeakPos, vFollowers, violatingBRFollowers, Fin.ext_iff]
  rw [hfilter]
  decide

private theorem vPeakPos_cum_neg_one :
    Math.cumWeight vPeakPos (fun _ => 1) (-1) = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vPeakPos a ≤ -1)
      = {Sum.inl (0 : Fin 3), Sum.inl (2 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vPeakPos, vPeaks, violatingBRPeaks, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [vPeakPos, vFollowers, violatingBRFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem vPeakPos_cum_neg_two :
    Math.cumWeight vPeakPos (fun _ => 1) (-2) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vPeakPos a ≤ -2)
      = {Sum.inl (2 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vPeakPos, vPeaks, violatingBRPeaks, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [vPeakPos, vFollowers, violatingBRFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem socialMedian_vPeaks : socialMedian vPeaks vFollowers = 1 := by
  unfold socialMedian
  change Math.weightedMedian vPeakPos (fun _ => 1) = 1
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      vPeakPos_cum_one]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    rcases a with j | i
    · fin_cases j
      · change 2 * Math.cumWeight vPeakPos (fun _ => 1) (-1) < 5
        rw [vPeakPos_cum_neg_one]
        norm_num
      · norm_num [vPeakPos, vPeaks, violatingBRPeaks] at hltx
      · change 2 * Math.cumWeight vPeakPos (fun _ => 1) (-2) < 5
        rw [vPeakPos_cum_neg_two]
        norm_num
    · fin_cases i <;>
        norm_num [vPeakPos, vFollowers, violatingBRFollowers] at hltx

private theorem vStatePos_cum_one : Math.cumWeight vStatePos (fun _ => 1) 1 = 4 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vStatePos a ≤ 1)
      = {Sum.inl (0 : Fin 3), Sum.inl (2 : Fin 3),
          Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vStatePos, vState, violatingBRState, Fin.ext_iff]
      simp
    · fin_cases i <;>
        norm_num [vStatePos, vFollowers, violatingBRFollowers, Fin.ext_iff]
  rw [hfilter]
  decide

private theorem vStatePos_cum_zero : Math.cumWeight vStatePos (fun _ => 1) 0 = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vStatePos a ≤ 0)
      = {Sum.inl (0 : Fin 3), Sum.inl (2 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vStatePos, vState, violatingBRState, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [vStatePos, vFollowers, violatingBRFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem vStatePos_cum_neg_one :
    Math.cumWeight vStatePos (fun _ => 1) (-1) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vStatePos a ≤ -1)
      = {Sum.inl (0 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vStatePos, vState, violatingBRState, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [vStatePos, vFollowers, violatingBRFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem socialMedian_vState : socialMedian vState vFollowers = 1 := by
  unfold socialMedian
  change Math.weightedMedian vStatePos (fun _ => 1) = 1
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      vStatePos_cum_one]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    rcases a with j | i
    · fin_cases j
      · change 2 * Math.cumWeight vStatePos (fun _ => 1) (-1) < 5
        rw [vStatePos_cum_neg_one]
        norm_num
      · norm_num [vStatePos, vState, violatingBRState] at hltx
      · change 2 * Math.cumWeight vStatePos (fun _ => 1) 0 < 5
        rw [vStatePos_cum_zero]
        norm_num
    · fin_cases i <;>
        norm_num [vStatePos, vFollowers, violatingBRFollowers] at hltx

private theorem vViolPos_cum_one : Math.cumWeight vViolPos (fun _ => 1) 1 = 3 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vViolPos a ≤ 1)
      = {Sum.inl (0 : Fin 3), Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vViolPos, vViolState, Fin.ext_iff] <;> simp
    · fin_cases i <;>
        norm_num [vViolPos, vFollowers, violatingBRFollowers, Fin.ext_iff]
  rw [hfilter]
  decide

private theorem vViolPos_cum_neg_one :
    Math.cumWeight vViolPos (fun _ => 1) (-1) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Fin 2 => vViolPos a ≤ -1)
      = {Sum.inl (0 : Fin 3)} := by
    ext a
    rcases a with j | i
    · fin_cases j <;>
        norm_num [vViolPos, vViolState, Fin.ext_iff]
    · fin_cases i <;>
        norm_num [vViolPos, vFollowers, violatingBRFollowers, Fin.ext_iff] <;> simp
  rw [hfilter]
  decide

private theorem socialMedian_vViol :
    socialMedian (Function.update vState (2 : Fin 3) 10) vFollowers = 1 := by
  rw [vViolState_eq]
  unfold socialMedian
  change Math.weightedMedian vViolPos (fun _ => 1) = 1
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      vViolPos_cum_one]
    norm_num
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    rcases a with j | i
    · fin_cases j
      · change 2 * Math.cumWeight vViolPos (fun _ => 1) (-1) < 5
        rw [vViolPos_cum_neg_one]
        norm_num
      · norm_num [vViolPos, vViolState] at hltx
      · norm_num [vViolPos, vViolState] at hltx
    · fin_cases i <;>
        norm_num [vViolPos, vFollowers, violatingBRFollowers] at hltx

private theorem delegate_vPeaks_one : delegate vPeaks 1 = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [vPeaks, violatingBRPeaks]
  · intro b _
    exact Fin.zero_le b

private theorem delegate_vState_one : delegate vState 1 = 2 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [vState, violatingBRState]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    fin_cases b
    · have hb2 := hb (2 : Fin 3)
      norm_num [vState, violatingBRState] at hb2
    · have hb2 := hb (2 : Fin 3)
      norm_num [vState, violatingBRState] at hb2
    · exact le_rfl

private theorem delegate_vViol_one :
    delegate (Function.update vState (2 : Fin 3) 10) 1 = 0 := by
  rw [vViolState_eq]
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [vViolState]
  · intro b _
    exact Fin.zero_le b

private theorem outcome_vPeaks : outcome vPeaks vFollowers = -1 := by
  unfold outcome winner
  rw [socialMedian_vPeaks, delegate_vPeaks_one]
  rfl

private theorem outcome_vState : outcome vState vFollowers = 0 := by
  unfold outcome winner
  rw [socialMedian_vState, delegate_vState_one]
  rfl

private theorem outcome_vViol :
    outcome (Function.update vState (2 : Fin 3) 10) vFollowers = -1 := by
  unfold outcome winner
  rw [socialMedian_vViol, delegate_vViol_one, vViolState_eq]
  norm_num [vViolState]

theorem violatingBR_strongBandInvariant :
    StrongBandInvariant vPeaks vFollowers vState := by
  constructor
  · intro j
    fin_cases j <;>
      norm_num [WeakPeakBand, initialDelta, socialMedian_vPeaks, outcome_vPeaks,
        vPeaks, vState, violatingBRPeaks, violatingBRState]
  · constructor <;> intro h
    · rw [outcome_vPeaks]
      unfold winner
      rw [socialMedian_vPeaks, delegate_vPeaks_one]
      norm_num [vState, violatingBRState]
    · rw [outcome_vPeaks, socialMedian_vPeaks] at h
      norm_num at h

theorem violatingBR_isBetterResponse :
    IsBetterResponse vPeaks vFollowers vState (2 : Fin 3) 10 := by
  constructor
  · rw [outcome_vViol, outcome_vState]
    norm_num
  · intro hsp
    norm_num [SPPrefers, vPeaks, violatingBRPeaks, outcome_vState,
      outcome_vViol] at hsp

theorem violatingBR_bandViolating :
    BandViolatingReport vPeaks vFollowers (2 : Fin 3) 10 := by
  left
  norm_num [BandViolatingReport, initialDelta, socialMedian_vPeaks, outcome_vPeaks,
    vPeaks, violatingBRPeaks]

/-- The vacating report is a *strict Euclidean* improvement for the winning
proxy, not merely a preference-free better response: the outcome moves from `0`
(distance `2` from the peak `-2`) to `-1` (distance `1`). -/
theorem violatingBR_prefers :
    Prefers vPeaks (2 : Fin 3)
      (outcome (Function.update vState (2 : Fin 3) 10) vFollowers)
      (outcome vState vFollowers) := by
  rw [outcome_vViol, outcome_vState, Prefers,
    show vPeaks (2 : Fin 3) = (-2 : ℝ) from rfl]
  norm_num

/-- Band violations cannot be refuted as better responses: at this
`StrongBandInvariant` state the winning proxy strictly gains — even in
Euclidean distance — by vacating to a report far outside the band, because
the mirror tie at the median then breaks toward its peak.  So the
band-violation half of Theorem 3 requires the truth-orientation forcing; the
paper's claim that violations are never better responses does not hold. -/
theorem strongBandInvariant_does_not_refute_bandViolatingReports :
    ∃ (pp : Fin 3 → ℝ) (q : Fin 2 → ℝ) (s : Fin 3 → ℝ) (j : Fin 3) (r : ℝ),
      StrongBandInvariant pp q s ∧
        IsBetterResponse pp q s j r ∧
        Prefers pp j (outcome (Function.update s j r) q) (outcome s q) ∧
        BandViolatingReport pp q j r :=
  ⟨vPeaks, vFollowers, vState, 2, 10, violatingBR_strongBandInvariant,
    violatingBR_isBetterResponse, violatingBR_prefers, violatingBR_bandViolating⟩

/-! ## The winner's minimax strategy need not be to stay

Theorem 4's winning-proxy case claims that a winner reporting away from its
peak has staying put as its minimax-regret strategy.  This fails when a
runner-up sits strictly between the winner's reflected peak `2p - w` and
its report `w`: every deviation outcome lands weakly right of the
runner-up, so the best ex-post outcome *is* the runner-up — and vacating
achieves it exactly, at every consistent median, for zero regret, while
staying pays the winner-to-runner-up gap. -/

/-- Peaks: the winner far left at −10, the runner-up truthful at −2 —
strictly between the winner's reflected peak −20 and its report 0. -/
def winnerStayPeaks : Fin 2 → ℝ
  | 0 => -10
  | 1 => -2

/-- The observed state: the winner reports 0, weakly left of the whole
uncertainty interval `[0, 1]`, and the runner-up sits at −2. -/
def winnerStayState : Fin 2 → ℝ
  | 0 => 0
  | 1 => -2

private theorem winnerStay_card :
    Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

/-- Every deviation outcome lands weakly right of the runner-up: the
selected report is weakly nearer the median than the runner-up's. -/
private theorem winnerStay_outcome_ge (y μ : ℝ) (hμ : 0 ≤ μ) :
    -2 ≤ outcome (Function.update winnerStayState 0 y)
      (fun _ : Fin 3 => μ) := by
  have h := delegate_dist_le (Function.update winnerStayState 0 y) μ 1
  rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
  have e1 : winnerStayState 1 = -2 := rfl
  have habs : |(-2 : ℝ) - μ| = 2 + μ := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [e1, habs] at h
  have h2 := (abs_le.mp h).1
  unfold outcome winner
  rw [socialMedian_const winnerStay_card]
  linarith

/-- Vacating hands the win to the runner-up. -/
private theorem winnerStay_vacate_outcome (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    outcome (Function.update winnerStayState 0 100)
      (fun _ : Fin 3 => μ) = -2 := by
  unfold outcome winner
  rw [socialMedian_const winnerStay_card]
  have hdel : delegate (Function.update winnerStayState 0 100) μ = 1 := by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rcases h2 i with h0 | h1
    · rw [h0, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        Function.update_self]
      have e1 : winnerStayState 1 = -2 := rfl
      rw [e1, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · exact absurd h1 hi
  rw [hdel, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rfl

/-- The winner's best ex-post distance is the runner-up's distance to the
peak, attained by vacating. -/
private theorem winnerStay_bestDist (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    bestOutcomeDist winnerStayPeaks winnerStayState 0 (fun _ : Fin 3 => μ)
      = 8 := by
  refine le_antisymm ?_ ?_
  · calc bestOutcomeDist winnerStayPeaks winnerStayState 0 (fun _ : Fin 3 => μ)
        ≤ |outcome (Function.update winnerStayState 0 100)
            (fun _ : Fin 3 => μ) - winnerStayPeaks 0| := bestOutcomeDist_le 100
      _ = 8 := by
        rw [winnerStay_vacate_outcome μ hμ1 hμ2]
        norm_num [winnerStayPeaks]
  · unfold bestOutcomeDist
    refine le_ciInf fun y => ?_
    have hge := winnerStay_outcome_ge y μ hμ1
    have e0 : winnerStayPeaks 0 = -10 := rfl
    rw [e0]
    calc (8:ℝ) ≤ outcome (Function.update winnerStayState 0 y)
          (fun _ : Fin 3 => μ) - (-10) := by linarith
      _ ≤ |outcome (Function.update winnerStayState 0 y)
          (fun _ : Fin 3 => μ) - (-10)| := le_abs_self _

/-- Staying pays the winner-to-runner-up gap at every consistent median. -/
private theorem winnerStay_stay_regret (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    regret winnerStayPeaks winnerStayState 0 (winnerStayState 0)
      (fun _ : Fin 3 => μ) = 2 := by
  unfold regret
  rw [winnerStay_bestDist μ hμ1 hμ2,
    show Function.update winnerStayState 0 (winnerStayState 0)
      = winnerStayState from Function.update_eq_self 0 winnerStayState]
  have hout : outcome winnerStayState (fun _ : Fin 3 => μ) = 0 := by
    unfold outcome winner
    rw [socialMedian_const winnerStay_card]
    have hdel : delegate winnerStayState μ = 0 := by
      have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      refine delegate_eq_of_forall_lt fun i hi => ?_
      rcases h2 i with h0 | h1
      · exact absurd h0 hi
      · rw [h1]
        have e0 : winnerStayState 0 = 0 := rfl
        have e1 : winnerStayState 1 = -2 := rfl
        rw [e0, e1, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    rw [hdel]
    rfl
  rw [hout]
  norm_num [winnerStayPeaks]

/-- Vacating has zero regret at every consistent median. -/
private theorem winnerStay_vacate_regret (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    regret winnerStayPeaks winnerStayState 0 100 (fun _ : Fin 3 => μ) = 0 := by
  unfold regret
  rw [winnerStay_bestDist μ hμ1 hμ2, winnerStay_vacate_outcome μ hμ1 hμ2]
  norm_num [winnerStayPeaks]

/-- **Vacating has strictly smaller maximal regret than staying** in this
winner-stay configuration, where a runner-up sits strictly between the
winner's reflected peak and its report. -/
theorem winnerStay_vacate_lt_stay :
    maxRegretOver winnerStayPeaks winnerStayState 0 100
        (constProfiles (Fin 3) 0 1)
      < maxRegretOver winnerStayPeaks winnerStayState 0 (winnerStayState 0)
        (constProfiles (Fin 3) 0 1) := by
  have hne : (constProfiles (Fin 3) 0 1).Nonempty :=
    ⟨fun _ => 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hvac : maxRegretOver winnerStayPeaks winnerStayState 0 100
      (constProfiles (Fin 3) 0 1) ≤ 0 := by
    refine maxRegretOver_le hne ?_
    rintro q ⟨μ, hμ, rfl⟩
    rw [winnerStay_vacate_regret μ hμ.1 hμ.2]
  have hstay : (2:ℝ) ≤ maxRegretOver winnerStayPeaks winnerStayState 0
      (winnerStayState 0) (constProfiles (Fin 3) 0 1) := by
    have hmem : (fun _ : Fin 3 => (0:ℝ)) ∈ constProfiles (Fin 3) 0 1 :=
      ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
    have h := regret_le_maxRegretOver (pp := winnerStayPeaks)
      (s := winnerStayState) (j := 0) (r := winnerStayState 0) hmem
    rw [winnerStay_stay_regret 0 le_rfl (by norm_num)] at h
    exact h
  linarith

/-- Staying is not the winner's minimax-regret strategy: the paper's
Theorem 4 winning-proxy analysis needs the runner-up geometry as an
additional hypothesis (no other report strictly between the winner's
reflected peak and its report). -/
theorem winnerStay_not_isMinimaxRegret :
    ¬ IsMinimaxRegret winnerStayPeaks winnerStayState
        (constProfiles (Fin 3) 0 1) 0 (winnerStayState 0) := fun h =>
  absurd (h 100) (not_le.mpr winnerStay_vacate_lt_stay)

/-! ## History refinement is by side preservation

History refinement is by side preservation, not by intersecting with the
half-line past the winner's new report, which can exclude every consistent
profile.  The paper's interval recursion adds, when the winner itself moved
rightward, the constraint that the median is weakly right of its new
report.  That inference is sound only for movers weakly left of every
consistent median (`StrongMonotoneOver.report_le_socialMedian`): a winner
on the right of the median may move farther right, toward its own peak —
strong-monotonically and as a dominating manipulation — and the constraint
would then exclude every consistent profile, the true one included. -/

/-- Peaks: the winner's peak far right at 100, the runner-up truthful at
−10. -/
def moveRightPeaks : Fin 2 → ℝ
  | 0 => 100
  | 1 => -10

/-- The observed state: the winner at 5, right of every consistent median
in `[0, 1]`; it moves to 6. -/
def moveRightState : Fin 2 → ℝ
  | 0 => 5
  | 1 => -10

private theorem moveRight_card :
    Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

private theorem moveRight_delegate (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    delegate moveRightState μ = 0 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_lt fun i hi => ?_
  rcases h2 i with h0 | h1
  · exact absurd h0 hi
  · rw [h1]
    have e0 : moveRightState 0 = 5 := rfl
    have e1 : moveRightState 1 = -10 := rfl
    rw [e0, e1, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

private theorem moveRight_outcome_stay (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    outcome moveRightState (fun _ : Fin 3 => μ) = 5 := by
  unfold outcome winner
  rw [socialMedian_const moveRight_card, moveRight_delegate μ hμ1 hμ2]
  rfl

private theorem moveRight_outcome_move (μ : ℝ) (hμ1 : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    outcome (Function.update moveRightState 0 6) (fun _ : Fin 3 => μ)
      = 6 := by
  unfold outcome winner
  rw [socialMedian_const moveRight_card]
  have hdel : delegate (Function.update moveRightState 0 6) μ = 0 := by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rcases h2 i with h0 | h1
    · exact absurd h0 hi
    · rw [h1, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      have e1 : moveRightState 1 = -10 := rfl
      rw [e1, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      linarith
  rw [hdel, Function.update_self]

/-- The winner is the observed winner at every consistent profile. -/
theorem moveRight_winner :
    ∀ q ∈ constProfiles (Fin 3) 0 1, winner moveRightState q = 0 := by
  rintro q ⟨μ, hμ, rfl⟩
  unfold winner
  rw [socialMedian_const moveRight_card]
  exact moveRight_delegate μ hμ.1 hμ.2

/-- The winner's rightward move to 6 is strong-monotone over the consistent
profiles: its report stays on its own side of every consistent median. -/
theorem moveRight_strongMonotoneOver :
    StrongMonotoneOver moveRightState (constProfiles (Fin 3) 0 1) 0 6 := by
  rintro q ⟨μ, hμ, rfl⟩
  have hmed : socialMedian moveRightState (fun _ : Fin 3 => μ) = μ :=
    socialMedian_const moveRight_card moveRightState μ
  have e0 : moveRightState 0 = 5 := rfl
  rw [hmed, e0]
  refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_⟩
  · exact absurd h (not_lt.mpr (by linarith [hμ.2]))
  · linarith [hμ.2]
  · exfalso
    have h2 := hμ.2
    rw [← h] at h2
    linarith

/-- The rightward move is even a dominating manipulation: it wins at every
consistent median and lands nearer the winner's peak. -/
theorem moveRight_dominatesOver :
    DominatesOver moveRightPeaks moveRightState (constProfiles (Fin 3) 0 1)
      0 6 := by
  constructor
  · rintro q ⟨μ, hμ, rfl⟩
    rw [moveRight_outcome_move μ hμ.1 hμ.2, moveRight_outcome_stay μ hμ.1 hμ.2]
    norm_num [moveRightPeaks]
  · refine ⟨fun _ : Fin 3 => (0:ℝ), ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩
    unfold Prefers
    rw [moveRight_outcome_move 0 le_rfl (by norm_num),
      moveRight_outcome_stay 0 le_rfl (by norm_num)]
    norm_num [moveRightPeaks]

/-- **The rule excludes every consistent profile**: the paper's refinement
would assert the median is weakly right of the new report 6, yet every
consistent median lies in `[0, 1]`. -/
theorem moveRight_socialMedian_lt :
    ∀ q ∈ constProfiles (Fin 3) 0 1, socialMedian moveRightState q < 6 := by
  rintro q ⟨μ, hμ, rfl⟩
  rw [socialMedian_const moveRight_card]
  linarith [hμ.2]

/-! ## The paper's displayed base interval has reversed endpoints -/

/-- A three-proxy state with a winner strictly between its left and right
neighbors. -/
def baseIntervalReversalState : Fin 3 → ℝ
  | 0 => 0
  | 1 => 10
  | 2 => 20

/-- The winner's delegate cell is bounded in the natural order by the midpoint
with the left neighbor and then the midpoint with the right neighbor.  The
paper's displayed base interval puts these two endpoints in the opposite
order; here the median `10` lies in the natural interval but not in the
displayed reversed one. -/
theorem paperBaseInterval_endpoints_reversed :
    delegate baseIntervalReversalState 10 = 1
      ∧ ((baseIntervalReversalState 0 + baseIntervalReversalState 1) / 2 < 10
        ∧ 10 < (baseIntervalReversalState 2 + baseIntervalReversalState 1) / 2)
      ∧ ¬ ((baseIntervalReversalState 2 + baseIntervalReversalState 1) / 2 < 10
        ∧ 10 < (baseIntervalReversalState 0 + baseIntervalReversalState 1) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · refine delegate_eq_of_forall_lt fun i hi => ?_
    fin_cases i
    · change |(10 : ℝ) - 10| < |(0 : ℝ) - 10|
      norm_num
    · exact absurd rfl hi
    · change |(10 : ℝ) - 10| < |(20 : ℝ) - 10|
      norm_num
  · norm_num [baseIntervalReversalState]
  · norm_num [baseIntervalReversalState]

/-! ## The paper's non-winner interval lower endpoint is too permissive -/

/-- Peaks for the endpoint witness; the obstruction is outcome-theoretic and
does not depend on a special choice of peaks. -/
def paperMinEndpointPeaks : Fin 3 → ℝ
  | 0 => 0
  | 1 => 10
  | 2 => 20

private theorem paperMinEndpoint_card :
    Fintype.card (Fin 3) < Fintype.card (Fin 5) := by
  norm_num

private theorem paperMinEndpoint_winner :
    ∀ q ∈ constProfiles (Fin 5) 8 9,
      winner baseIntervalReversalState q = 1 := by
  rintro q ⟨μ, hμ, rfl⟩
  have hμ8 : (8 : ℝ) ≤ μ := hμ.1
  have hμ9 : μ ≤ 9 := hμ.2
  unfold winner
  rw [socialMedian_const paperMinEndpoint_card]
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i
  · change |(10 : ℝ) - μ| < |(0 : ℝ) - μ|
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · exact absurd rfl hi
  · change |(10 : ℝ) - μ| < |(20 : ℝ) - μ|
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

private theorem paperMinEndpoint_hmed :
    ∀ q ∈ constProfiles (Fin 5) 8 9,
      socialMedian (Function.update baseIntervalReversalState 0 5) q
        = socialMedian baseIntervalReversalState q := by
  rintro q ⟨μ, hμ, rfl⟩
  rw [socialMedian_const paperMinEndpoint_card,
    socialMedian_const paperMinEndpoint_card]

private theorem paperMinEndpoint_farther :
    ∀ q ∈ constProfiles (Fin 5) 8 9,
      |baseIntervalReversalState 1 - socialMedian baseIntervalReversalState q|
        < |(5 : ℝ) - socialMedian baseIntervalReversalState q| := by
  rintro q ⟨μ, hμ, rfl⟩
  have hμ8 : (8 : ℝ) ≤ μ := hμ.1
  have hμ9 : μ ≤ 9 := hμ.2
  rw [socialMedian_const paperMinEndpoint_card]
  change |(10 : ℝ) - μ| < |(5 : ℝ) - μ|
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  linarith

/-- The report `5` lies in the paper's displayed lower-bounded interval
`(min{s_l, 2ℓ - w}, w)` for `s_l = 0`, `ℓ = 8`, `w = 10`, but it does not
lie in the refined interval `(2ℓ - w, w) = (6, 10)`. -/
theorem paperMinEndpoint_report_in_displayed_not_refined_interval :
    min (baseIntervalReversalState 0)
        (2 * (8 : ℝ) - baseIntervalReversalState 1) < 5
      ∧ 5 < baseIntervalReversalState 1
      ∧ ¬ 2 * (8 : ℝ) - baseIntervalReversalState 1 < 5 := by
  norm_num [baseIntervalReversalState]

/-- The report admitted by the paper's displayed `min` lower endpoint is not
a dominating manipulation: for every median in `[8,9]`, the old winner at
`10` is strictly closer than report `5`, so the outcome never changes. -/
theorem paperMinEndpoint_report_not_dominates :
    ¬ DominatesOver paperMinEndpointPeaks baseIntervalReversalState
      (constProfiles (Fin 5) 8 9) 0 5 := by
  exact not_dominatesOver_of_report_strictly_farther_than_winner
    (pp := paperMinEndpointPeaks) (s := baseIntervalReversalState)
    (Q := constProfiles (Fin 5) 8 9) (j := 0) (r := 5) (jw := 1)
    paperMinEndpoint_winner (by decide) paperMinEndpoint_hmed
    paperMinEndpoint_farther

/-! ## Lemma 3's strict decrease fails under mirror ties

A monotone better response by a non-winner can hand the win across the
median to a report at the same distance: the position changes, the distance
does not.  All data below is integral, so integer spacing does not remove
the caveat (section 4.4). -/

/-- Peaks: the mover far left at −5, the winner truthful at 2. -/
def mirrorTiePeaks : Fin 2 → ℝ
  | 0 => -5
  | 1 => 2

/-- Followers with true median 0. -/
def mirrorTieFollowers : Fin 3 → ℝ
  | 0 => 0
  | 1 => 5
  | 2 => -5

/-- The state before the move: the mover parked at −20, the winner at 2. -/
def mirrorTieState : Fin 2 → ℝ
  | 0 => -20
  | 1 => 2

/-- The state after the mover's better response to −2 — the mirror of the
winning report across the median. -/
def mirrorTieMoved : Fin 2 → ℝ
  | 0 => -2
  | 1 => 2

private theorem mt_update :
    Function.update mirrorTieState 0 (-2) = mirrorTieMoved := by
  funext i
  fin_cases i <;> simp [mirrorTieState, mirrorTieMoved]

private theorem mt_truth_cum_zero :
    Math.cumWeight (allPos mirrorTiePeaks mirrorTieFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTiePeaks, mirrorTieFollowers]

private theorem mt_truth_cum_neg5 :
    Math.cumWeight (allPos mirrorTiePeaks mirrorTieFollowers) (fun _ => 1)
      (-5) = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTiePeaks, mirrorTieFollowers]

private theorem mt_median_truth :
    socialMedian mirrorTiePeaks mirrorTieFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, mt_truth_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos mirrorTiePeaks mirrorTieFollowers)
            (fun _ => 1) (-5) < Math.totalWeight fun _ => 1
          rw [mt_truth_cum_neg5, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, mirrorTiePeaks] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos mirrorTiePeaks mirrorTieFollowers)
            (fun _ => 1) (-5) < Math.totalWeight fun _ => 1
          rw [mt_truth_cum_neg5, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem mt_state_cum_zero :
    Math.cumWeight (allPos mirrorTieState mirrorTieFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieState, mirrorTieFollowers]

private theorem mt_state_cum_neg5 :
    Math.cumWeight (allPos mirrorTieState mirrorTieFollowers) (fun _ => 1)
      (-5) = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieState, mirrorTieFollowers]

private theorem mt_state_cum_neg20 :
    Math.cumWeight (allPos mirrorTieState mirrorTieFollowers) (fun _ => 1)
      (-20) = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieState, mirrorTieFollowers]

private theorem mt_median_state :
    socialMedian mirrorTieState mirrorTieFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, mt_state_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos mirrorTieState mirrorTieFollowers)
            (fun _ => 1) (-20) < Math.totalWeight fun _ => 1
          rw [mt_state_cum_neg20, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, mirrorTieState] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos mirrorTieState mirrorTieFollowers)
            (fun _ => 1) (-5) < Math.totalWeight fun _ => 1
          rw [mt_state_cum_neg5, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem mt_moved_cum_zero :
    Math.cumWeight (allPos mirrorTieMoved mirrorTieFollowers) (fun _ => 1) 0
      = 3 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieMoved, mirrorTieFollowers]

private theorem mt_moved_cum_neg5 :
    Math.cumWeight (allPos mirrorTieMoved mirrorTieFollowers) (fun _ => 1)
      (-5) = 1 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieMoved, mirrorTieFollowers]

private theorem mt_moved_cum_neg2 :
    Math.cumWeight (allPos mirrorTieMoved mirrorTieFollowers) (fun _ => 1)
      (-2) = 2 := by
  rw [Math.cumWeight, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [allPos, mirrorTieMoved, mirrorTieFollowers]

private theorem mt_median_moved :
    socialMedian mirrorTieMoved mirrorTieFollowers = 0 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, mt_moved_cum_zero]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos mirrorTieMoved mirrorTieFollowers)
            (fun _ => 1) (-2) < Math.totalWeight fun _ => 1
          rw [mt_moved_cum_neg2, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, mirrorTieMoved] at hzlt
    | inr f =>
        fin_cases f
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · norm_num [allPos, mirrorTieFollowers] at hzlt
        · change 2 * Math.cumWeight (allPos mirrorTieMoved mirrorTieFollowers)
            (fun _ => 1) (-5) < Math.totalWeight fun _ => 1
          rw [mt_moved_cum_neg5, Math.totalWeight_one, Fintype.card_sum]
          norm_num

private theorem mt_delegate_state : delegate mirrorTieState 0 = 1 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_lt fun i hi => ?_
  rcases h2 i with h0 | h1
  · rw [h0]
    norm_num [mirrorTieState]
  · exact absurd h1 hi

private theorem mt_delegate_moved : delegate mirrorTieMoved 0 = 0 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
  · rcases h2 i with h0 | h1
    · rw [h0]
    · rw [h1]
      norm_num [mirrorTieMoved]
  · exact absurd hi (Fin.not_lt_zero i)

private theorem mt_outcome_state :
    outcome mirrorTieState mirrorTieFollowers = 2 := by
  unfold outcome winner
  rw [mt_median_state, mt_delegate_state]
  rfl

private theorem mt_outcome_moved :
    outcome mirrorTieMoved mirrorTieFollowers = -2 := by
  unfold outcome winner
  rw [mt_median_moved, mt_delegate_moved]
  rfl

/-- **Lemma 3's strict decrease fails under a mirror tie** (and integer
spacing does not restore it): all hypotheses of `monotoneStep_dist_lt`
except the no-tie condition hold, yet the distance to the true median does
not decrease — the mover's better response to −2 hands the win across the
median from 2 at unchanged distance 2. -/
theorem monotoneStep_not_dist_lt_with_mirror_tie :
    SameSide mirrorTiePeaks mirrorTieFollowers mirrorTieState
      ∧ socialMedian mirrorTieState mirrorTieFollowers
          = socialMedian mirrorTiePeaks mirrorTieFollowers
      ∧ IsBetterResponse mirrorTiePeaks mirrorTieFollowers mirrorTieState
          0 (-2)
      ∧ MonotoneReport mirrorTiePeaks mirrorTieFollowers 0 (-2)
      ∧ (0 : Fin 2) ≠ winner mirrorTieState mirrorTieFollowers
      ∧ ¬ (|outcome (Function.update mirrorTieState 0 (-2)) mirrorTieFollowers
            - socialMedian mirrorTiePeaks mirrorTieFollowers|
          < |outcome mirrorTieState mirrorTieFollowers
            - socialMedian mirrorTiePeaks mirrorTieFollowers|) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [mt_median_truth]
    fin_cases j
    · exact ⟨fun _ => by norm_num [mirrorTieState],
        fun h => absurd h (by norm_num [mirrorTiePeaks]),
        fun h => absurd h (by norm_num [mirrorTiePeaks])⟩
    · exact ⟨fun h => absurd h (by norm_num [mirrorTiePeaks]),
        fun _ => by norm_num [mirrorTieState],
        fun h => absurd h (by norm_num [mirrorTiePeaks])⟩
  · rw [mt_median_state, mt_median_truth]
  · refine isBetterResponse_of_prefers ?_
    unfold Prefers
    rw [mt_update, mt_outcome_moved, mt_outcome_state]
    norm_num [mirrorTiePeaks]
  · rw [MonotoneReport, mt_median_truth]
    exact ⟨fun _ => by norm_num,
      fun h => absurd h (by norm_num [mirrorTiePeaks]),
      fun h => absurd h (by norm_num [mirrorTiePeaks])⟩
  · have hw : winner mirrorTieState mirrorTieFollowers = 1 := by
      unfold winner
      rw [mt_median_state, mt_delegate_state]
    rw [hw]
    decide
  · rw [mt_update, mt_outcome_moved, mt_outcome_state, mt_median_truth]
    norm_num

/-- The discrete `+1` decrease conclusion also fails without the no-mirror-tie
hypothesis, even though all peaks, followers, reports, and the move are
integral.  Thus integer spacing alone cannot discharge the strict-decrease
premise used by `eventually_outcome_eq_socialMedian_of_windowed_decrease`. -/
theorem integral_monotoneStep_not_dist_add_one_le_without_noMirrorTie :
    SameSide mirrorTiePeaks mirrorTieFollowers mirrorTieState
      ∧ socialMedian mirrorTieState mirrorTieFollowers
          = socialMedian mirrorTiePeaks mirrorTieFollowers
      ∧ IsBetterResponse mirrorTiePeaks mirrorTieFollowers mirrorTieState
          0 (-2)
      ∧ MonotoneReport mirrorTiePeaks mirrorTieFollowers 0 (-2)
      ∧ (0 : Fin 2) ≠ winner mirrorTieState mirrorTieFollowers
      ∧ (∀ k, ∃ n : ℤ, mirrorTiePeaks k = n)
      ∧ (∀ i, ∃ n : ℤ, mirrorTieFollowers i = n)
      ∧ (∀ k, ∃ n : ℤ, mirrorTieState k = n)
      ∧ (∃ n : ℤ, (-2 : ℝ) = n)
      ∧ ¬ (|outcome (Function.update mirrorTieState 0 (-2)) mirrorTieFollowers
            - socialMedian mirrorTiePeaks mirrorTieFollowers| + 1
          ≤ |outcome mirrorTieState mirrorTieFollowers
            - socialMedian mirrorTiePeaks mirrorTieFollowers|) := by
  obtain ⟨hside, hmed, hbr, hmono, hj, _⟩ := monotoneStep_not_dist_lt_with_mirror_tie
  refine ⟨hside, hmed, hbr, hmono, hj, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact ⟨-5, by norm_num [mirrorTiePeaks]⟩
    · exact ⟨2, by norm_num [mirrorTiePeaks]⟩
  · intro i
    fin_cases i
    · exact ⟨0, by norm_num [mirrorTieFollowers]⟩
    · exact ⟨5, by norm_num [mirrorTieFollowers]⟩
    · exact ⟨-5, by norm_num [mirrorTieFollowers]⟩
  · intro k
    fin_cases k
    · exact ⟨-20, by norm_num [mirrorTieState]⟩
    · exact ⟨2, by norm_num [mirrorTieState]⟩
  · exact ⟨-2, by norm_num⟩
  · rw [mt_update, mt_outcome_moved, mt_outcome_state, mt_median_truth]
    norm_num

/-! ## Mirror ties can arise immediately from truthful integral play -/

/-- Distinct integral peaks for a truthful-start mirror-tie example. -/
def truthfulMirrorTiePeaks : Fin 3 → ℝ
  | 0 => -7
  | 1 => -6
  | 2 => -3

/-- Four followers fixed at the true median `-4`, so follower majority pins
the social median for every proxy report state used below. -/
def truthfulMirrorTieFollowers : Fin 4 → ℝ := fun _ => -4

/-- The state after proxy `0` moves from its truthful report `-7` to `-5`,
the mirror of the old winner `-3` around median `-4`. -/
def truthfulMirrorTieMoved : Fin 3 → ℝ
  | 0 => -5
  | 1 => -6
  | 2 => -3

private theorem tmt_card : Fintype.card (Fin 3) < Fintype.card (Fin 4) := by
  simp

private theorem tmt_median_truth :
    socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers = -4 := by
  rw [show truthfulMirrorTieFollowers = fun _ : Fin 4 => (-4 : ℝ) from rfl]
  exact socialMedian_const tmt_card truthfulMirrorTiePeaks (-4)

private theorem tmt_median_moved :
    socialMedian truthfulMirrorTieMoved truthfulMirrorTieFollowers = -4 := by
  rw [show truthfulMirrorTieFollowers = fun _ : Fin 4 => (-4 : ℝ) from rfl]
  exact socialMedian_const tmt_card truthfulMirrorTieMoved (-4)

private theorem tmt_update :
    Function.update truthfulMirrorTiePeaks 0 (-5) = truthfulMirrorTieMoved := by
  funext i
  fin_cases i <;> simp [truthfulMirrorTiePeaks, truthfulMirrorTieMoved]

private theorem tmt_delegate_truth :
    delegate truthfulMirrorTiePeaks (-4) = 2 := by
  refine delegate_eq_of_forall_lt fun i hi => ?_
  fin_cases i
  · norm_num [truthfulMirrorTiePeaks]
  · norm_num [truthfulMirrorTiePeaks]
  · exact absurd rfl hi

private theorem tmt_delegate_moved :
    delegate truthfulMirrorTieMoved (-4) = 0 := by
  refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
  · fin_cases i <;> norm_num [truthfulMirrorTieMoved]
  · exact absurd hi (Fin.not_lt_zero i)

private theorem tmt_outcome_truth :
    outcome truthfulMirrorTiePeaks truthfulMirrorTieFollowers = -3 := by
  unfold outcome winner
  rw [tmt_median_truth, tmt_delegate_truth]
  rfl

private theorem tmt_outcome_moved :
    outcome truthfulMirrorTieMoved truthfulMirrorTieFollowers = -5 := by
  unfold outcome winner
  rw [tmt_median_moved, tmt_delegate_moved]
  rfl

/-- **Truthful integral play can hit a mirror tie immediately.**  Starting
from truthful, distinct, integral proxy reports, proxy `0` has an integral
monotone better response to `-5`.  The resulting state mirror-ties reports
`-5` and `-3` around the true median `-4`, so the winner changes but the
outcome distance from the true median remains `1`.  Thus integer
best-response-from-truth dynamics do not preserve the no-mirror-tie invariant
needed by the discrete convergence theorem. -/
theorem integral_truthful_monotoneStep_hits_mirrorTie :
    SameSide truthfulMirrorTiePeaks truthfulMirrorTieFollowers truthfulMirrorTiePeaks
      ∧ IsBetterResponse truthfulMirrorTiePeaks truthfulMirrorTieFollowers
          truthfulMirrorTiePeaks 0 (-5)
      ∧ MonotoneReport truthfulMirrorTiePeaks truthfulMirrorTieFollowers 0 (-5)
      ∧ (0 : Fin 3) ≠ winner truthfulMirrorTiePeaks truthfulMirrorTieFollowers
      ∧ (∀ k, ∃ n : ℤ, truthfulMirrorTiePeaks k = n)
      ∧ (∀ i, ∃ n : ℤ, truthfulMirrorTieFollowers i = n)
      ∧ (∃ n : ℤ, (-5 : ℝ) = n)
      ∧ ¬ NoMirrorTieAt (Function.update truthfulMirrorTiePeaks 0 (-5))
          (socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers)
      ∧ ¬ (|outcome (Function.update truthfulMirrorTiePeaks 0 (-5))
              truthfulMirrorTieFollowers
            - socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers| + 1
          ≤ |outcome truthfulMirrorTiePeaks truthfulMirrorTieFollowers
            - socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers|) := by
  refine ⟨sameSide_self truthfulMirrorTiePeaks truthfulMirrorTieFollowers, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isBetterResponse_of_prefers ?_
    unfold Prefers
    rw [tmt_update, tmt_outcome_moved, tmt_outcome_truth]
    norm_num [truthfulMirrorTiePeaks]
  · rw [MonotoneReport, tmt_median_truth]
    exact ⟨fun _ => by norm_num, fun h => absurd h (by norm_num [truthfulMirrorTiePeaks]),
      fun h => absurd h (by norm_num [truthfulMirrorTiePeaks])⟩
  · have hw : winner truthfulMirrorTiePeaks truthfulMirrorTieFollowers = 2 := by
      unfold winner
      rw [tmt_median_truth, tmt_delegate_truth]
    rw [hw]
    decide
  · intro k
    fin_cases k
    · exact ⟨-7, by norm_num [truthfulMirrorTiePeaks]⟩
    · exact ⟨-6, by norm_num [truthfulMirrorTiePeaks]⟩
    · exact ⟨-3, by norm_num [truthfulMirrorTiePeaks]⟩
  · intro i
    exact ⟨-4, by norm_num [truthfulMirrorTieFollowers]⟩
  · exact ⟨-5, by norm_num⟩
  · intro htie
    have hdist : |Function.update truthfulMirrorTiePeaks 0 (-5) 0
          - socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers|
        = |Function.update truthfulMirrorTiePeaks 0 (-5) 2
          - socialMedian truthfulMirrorTiePeaks truthfulMirrorTieFollowers| := by
      rw [tmt_median_truth]
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      simp [truthfulMirrorTiePeaks, Function.update, h20]
      norm_num
    have hpos := htie 0 2 hdist
    norm_num [truthfulMirrorTiePeaks, Function.update] at hpos
    exact (by decide : (2 : Fin 3) ≠ 0) hpos
  · rw [tmt_update, tmt_outcome_moved, tmt_outcome_truth, tmt_median_truth]
    norm_num

/-! ## Theorem 4's peak-outside hypothesis is necessary

With the proxy's peak strictly inside the winning interval, the near
boundary of the uncertainty is not minimax-regret: reporting the peak wins
at every consistent median for zero maximal regret. -/

/-- Peaks: the winner truthful at 2, the deviator's peak at 1 — inside the
winning interval `(2ℓ - w, w) = (-2, 2)`. -/
def insidePeakPeaks : Fin 2 → ℝ
  | 0 => 2
  | 1 => 1

/-- The observed state: the winner at 2, the deviator parked at 100. -/
def insidePeakState : Fin 2 → ℝ
  | 0 => 2
  | 1 => 100

private theorem ip_card : Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

private theorem ip_delegate (μ : ℝ) (hμ2 : μ ≤ 1) :
    delegate insidePeakState μ = 0 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_lt fun i hi => ?_
  rcases h2 i with h0 | h1
  · exact absurd h0 hi
  · rw [h1]
    have e0 : insidePeakState 0 = 2 := rfl
    have e1 : insidePeakState 1 = 100 := rfl
    rw [e0, e1, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

private theorem ip_out_stay (μ : ℝ) (hμ2 : μ ≤ 1) :
    outcome insidePeakState (fun _ : Fin 3 => μ) = 2 := by
  unfold outcome winner
  rw [socialMedian_const ip_card, ip_delegate μ hμ2]
  rfl

private theorem ip_out_peak (μ : ℝ) (hμ2 : μ ≤ 1) :
    outcome (Function.update insidePeakState 1 1) (fun _ : Fin 3 => μ)
      = 1 := by
  unfold outcome winner
  rw [socialMedian_const ip_card]
  have hdel : delegate (Function.update insidePeakState 1 1) μ = 1 := by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rcases h2 i with h0 | h1
    · rw [h0, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      have e0 : insidePeakState 0 = 2 := rfl
      rw [e0, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · exact absurd h1 hi
  rw [hdel, Function.update_self]

private theorem ip_out_zero_at_one :
    outcome (Function.update insidePeakState 1 0) (fun _ : Fin 3 => (1:ℝ))
      = 2 := by
  unfold outcome winner
  rw [socialMedian_const ip_card]
  have hdel : delegate (Function.update insidePeakState 1 0) (1:ℝ) = 0 := by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
    · rcases h2 i with h0 | h1
      · rw [h0]
      · rw [h1, Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
        norm_num [insidePeakState]
    · exact absurd hi (Fin.not_lt_zero i)
  rw [hdel, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  rfl

/-- With the peak inside the winning interval, reporting the peak is
minimax-regret: it wins at every consistent median. -/
theorem insidePeak_peak_isMinimaxRegret :
    IsMinimaxRegret insidePeakPeaks insidePeakState
      (constProfiles (Fin 3) 0 1) 1 1 := by
  have hQw : ∀ q ∈ constProfiles (Fin 3) 0 1,
      winner insidePeakState q = 0 := by
    rintro q ⟨μ, hμ, rfl⟩
    unfold winner
    rw [socialMedian_const ip_card]
    exact ip_delegate μ hμ.2
  have hmed : ∀ q ∈ constProfiles (Fin 3) 0 1, ∀ y,
      socialMedian (Function.update insidePeakState 1 y) q
        = socialMedian insidePeakState q := by
    rintro q ⟨μ, -, rfl⟩ y
    rw [socialMedian_const ip_card, socialMedian_const ip_card]
  have hwin : ∀ q ∈ constProfiles (Fin 3) 0 1,
      |insidePeakPeaks 1 - socialMedian insidePeakState q|
        < |outcome insidePeakState q - socialMedian insidePeakState q| := by
    rintro q ⟨μ, hμ, rfl⟩
    rw [socialMedian_const ip_card, ip_out_stay μ hμ.2]
    have e1 : insidePeakPeaks 1 = 1 := rfl
    rw [e1, abs_of_nonneg (by linarith [hμ.2]),
      abs_of_nonneg (by linarith [hμ.2])]
    linarith
  exact isMinimaxRegret_peak_of_forall_lt hQw (by decide) hmed
    ⟨fun _ => 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩ hwin

/-- **Theorem 4's peak-outside hypothesis is necessary**: with the peak
inside the winning interval, the near boundary is not minimax-regret — the
peak beats it. -/
theorem insidePeak_boundary_not_isMinimaxRegret :
    ¬ IsMinimaxRegret insidePeakPeaks insidePeakState
      (constProfiles (Fin 3) 0 1) 1 0 := by
  intro h
  have h1 := h 1
  have hbd : bestOutcomeDist insidePeakPeaks insidePeakState 1
      (fun _ : Fin 3 => (1:ℝ)) = 0 := by
    refine le_antisymm ?_ (bestOutcomeDist_nonneg (pp := insidePeakPeaks)
      (s := insidePeakState) (j := 1) (q := fun _ : Fin 3 => (1:ℝ)))
    have hle1 := bestOutcomeDist_le (pp := insidePeakPeaks)
      (s := insidePeakState) (j := 1) (q := fun _ : Fin 3 => (1:ℝ)) (1 : ℝ)
    rw [ip_out_peak 1 le_rfl] at hle1
    simpa [insidePeakPeaks] using hle1
  have hge : (1:ℝ) ≤ maxRegretOver insidePeakPeaks insidePeakState 1 0
      (constProfiles (Fin 3) 0 1) := by
    have hmem : (fun _ : Fin 3 => (1:ℝ)) ∈ constProfiles (Fin 3) 0 1 :=
      ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩
    have hr := regret_le_maxRegretOver (pp := insidePeakPeaks)
      (s := insidePeakState) (j := 1) (r := 0) hmem
    have hreg : regret insidePeakPeaks insidePeakState 1 0
        (fun _ : Fin 3 => (1:ℝ)) = 1 := by
      unfold regret
      rw [ip_out_zero_at_one, hbd]
      norm_num [insidePeakPeaks]
    rw [hreg] at hr
    exact hr
  have hle : maxRegretOver insidePeakPeaks insidePeakState 1 1
      (constProfiles (Fin 3) 0 1) ≤ 0 := by
    refine maxRegretOver_le ⟨fun _ => 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩ ?_
    rintro q ⟨μ, hμ, rfl⟩
    unfold regret
    rw [ip_out_peak μ hμ.2,
      show insidePeakPeaks 1 = (1:ℝ) from rfl, sub_self, abs_zero]
    have := bestOutcomeDist_nonneg (pp := insidePeakPeaks)
      (s := insidePeakState) (j := 1) (q := fun _ : Fin 3 => μ)
    linarith
  linarith

/-! ## Theorem 4's midpoint-spread hypothesis is necessary

Non-degeneracy `ℓ < u` alone does not make the near boundary minimax-regret:
the boundary is minimax only once the far endpoint `u` reaches the midpoint
`(ℓ + w)/2` between the near endpoint `ℓ` and the winning position `w`.  Below
that midpoint the boundary loses, even with the peak strictly outside the
winning interval.  Here the winner reports `w = 4`, the deviator's peak is
`-10` (outside, `-10 ≤ 2·0 - 4`), and the median uncertainty is the
*non-degenerate* interval `[0, 1]` — so `ℓ = 0 < 1 = u` is strict — but
`(0 + 4)/2 = 2 > 1`, so only the midpoint hypothesis fails.  The near boundary
report `0` then has maximal regret `≥ 7/2`, while reporting `-1` (still winning
at every consistent median) caps the maximal regret at `3`, so `0` is not
minimax-regret. -/

/-- Peaks: the winner truthful at `4`, the deviator's peak at `-10` — strictly
outside the winning interval `(2ℓ - w, w) = (-4, 4)`. -/
def midBreakPeaks : Fin 2 → ℝ
  | 0 => 4
  | 1 => -10

/-- The observed state: the winner at `4`, the deviator parked at `100`. -/
def midBreakState : Fin 2 → ℝ
  | 0 => 4
  | 1 => 100

private theorem mb_card : Fintype.card (Fin 2) < Fintype.card (Fin 3) := by simp

/-- Any report strictly nearer the median than the winner's `4` wins for the
deviator, so the outcome is that report. -/
private theorem mb_out_win (y μ : ℝ) (hy : |y - μ| < |(4 : ℝ) - μ|) :
    outcome (Function.update midBreakState 1 y) (fun _ : Fin 3 => μ) = y := by
  unfold outcome winner
  rw [socialMedian_const mb_card]
  have hdel : delegate (Function.update midBreakState 1 y) μ = 1 := by
    have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rcases h2 i with h0 | h1
    · rw [h0, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      have e0 : midBreakState 0 = 4 := rfl
      rw [e0]
      exact hy
    · exact absurd h1 hi
  rw [hdel, Function.update_self]

/-- Whatever the deviator reports, the selected position is at least as near
the median as the winner's `4`, hence at least `2μ - 4 ≥ -4` over `μ ∈ [0,1]`,
so its distance to the deviator's peak `-10` is at least `6`. -/
private theorem mb_outcome_ge (y μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (6:ℝ) ≤ |outcome (Function.update midBreakState 1 y) (fun _ : Fin 3 => μ)
      - midBreakPeaks 1| := by
  obtain ⟨h0, h1⟩ := hμ
  have hout : outcome (Function.update midBreakState 1 y) (fun _ : Fin 3 => μ)
      = (Function.update midBreakState 1 y)
          (delegate (Function.update midBreakState 1 y) μ) := by
    unfold outcome winner
    rw [socialMedian_const mb_card]
  have hd := delegate_dist_le (Function.update midBreakState 1 y) μ 0
  rw [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    show midBreakState 0 = (4:ℝ) from rfl,
    show |(4:ℝ) - μ| = 4 - μ from abs_of_nonneg (by linarith)] at hd
  rw [hout, show midBreakPeaks 1 = (-10:ℝ) from rfl]
  have hge : -(4 - μ) ≤ (Function.update midBreakState 1 y)
      (delegate (Function.update midBreakState 1 y) μ) - μ := neg_le_of_abs_le hd
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Theorem 4's midpoint hypothesis `(ℓ + w)/2 ≤ u` is necessary**, over and
above non-degeneracy `ℓ < u` and the peak-outside hypothesis.  With median
uncertainty `[0, 1]` (so `ℓ = 0 < 1 = u` is strict) but `(0 + 4)/2 = 2 > 1`,
the near boundary `0` is *not* minimax-regret: reporting `-1` still wins at
every consistent median and has strictly smaller maximal regret. -/
theorem midBreak_boundary_not_isMinimaxRegret :
    ¬ IsMinimaxRegret midBreakPeaks midBreakState (constProfiles (Fin 3) 0 1) 1 0 := by
  intro h
  have h1 := h (-1)
  have hhi : maxRegretOver midBreakPeaks midBreakState 1 (-1)
      (constProfiles (Fin 3) 0 1) ≤ 3 := by
    refine maxRegretOver_le ⟨fun _ => 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩ ?_
    rintro q ⟨μ, hμ, rfl⟩
    obtain ⟨hμ0, hμ1⟩ := hμ
    have hbdlo : (6:ℝ) ≤ bestOutcomeDist midBreakPeaks midBreakState 1
        (fun _ : Fin 3 => μ) := le_ciInf fun y => mb_outcome_ge y μ ⟨hμ0, hμ1⟩
    unfold regret
    rw [mb_out_win (-1) μ (by
        rw [show |(-1:ℝ) - μ| = 1 + μ from by rw [abs_of_nonpos (by linarith)]; ring,
          show |(4:ℝ) - μ| = 4 - μ from abs_of_nonneg (by linarith)]
        linarith),
      show midBreakPeaks 1 = (-10:ℝ) from rfl,
      show |(-1:ℝ) - (-10)| = 9 from by norm_num]
    linarith
  have hlo : (7/2:ℝ) ≤ maxRegretOver midBreakPeaks midBreakState 1 0
      (constProfiles (Fin 3) 0 1) := by
    have hmem0 : (fun _ : Fin 3 => (0:ℝ)) ∈ constProfiles (Fin 3) 0 1 :=
      ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
    have hr := regret_le_maxRegretOver (pp := midBreakPeaks) (s := midBreakState)
      (j := 1) (r := 0) hmem0
    have hbd : bestOutcomeDist midBreakPeaks midBreakState 1 (fun _ : Fin 3 => (0:ℝ))
        ≤ 13/2 := by
      have hle := bestOutcomeDist_le (pp := midBreakPeaks) (s := midBreakState)
        (j := 1) (q := fun _ : Fin 3 => (0:ℝ)) (-7/2)
      rw [mb_out_win (-7/2) 0 (by norm_num),
        show midBreakPeaks 1 = (-10:ℝ) from rfl,
        show |(-7/2:ℝ) - (-10)| = 13/2 from by norm_num] at hle
      exact hle
    have hreg : regret midBreakPeaks midBreakState 1 0 (fun _ : Fin 3 => (0:ℝ))
        = 10 - bestOutcomeDist midBreakPeaks midBreakState 1 (fun _ : Fin 3 => (0:ℝ)) := by
      unfold regret
      rw [mb_out_win 0 0 (by norm_num),
        show midBreakPeaks 1 = (-10:ℝ) from rfl,
        show |(0:ℝ) - (-10)| = 10 from by norm_num]
    rw [hreg] at hr
    linarith
  linarith

/-! ## Theorem 4's uncertainty-spread hypothesis is necessary

With a known median — degenerate uncertainty — no report is minimax-regret
at all: the best response approaches the mirror of the winning report, where
the tie-break hands the win back, so the infimum is unattained and every
report is strictly beaten by one slightly nearer the mirror. -/

/-- Peaks: the winner truthful at 2, the deviator's peak at −2 — exactly the
reflection of the winner across the known median 0. -/
def knownMedianPeaks : Fin 2 → ℝ
  | 0 => 2
  | 1 => -2

/-- The observed state: the winner at 2, the deviator parked at 100. -/
def knownMedianState : Fin 2 → ℝ
  | 0 => 2
  | 1 => 100

private theorem km_card : Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

private theorem km_out_win (y : ℝ) (h1 : -2 < y) (h2 : y < 2) :
    outcome (Function.update knownMedianState 1 y) (fun _ : Fin 3 => (0:ℝ))
      = y := by
  unfold outcome winner
  rw [socialMedian_const km_card]
  have hdel : delegate (Function.update knownMedianState 1 y) (0:ℝ) = 1 := by
    have hf : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_lt fun i hi => ?_
    rcases hf i with h0 | hone
    · rw [h0, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      have e0 : knownMedianState 0 = 2 := rfl
      rw [e0, sub_zero, sub_zero, show |(2:ℝ)| = 2 by norm_num]
      exact abs_lt.mpr ⟨h1, h2⟩
    · exact absurd hone hi
  rw [hdel, Function.update_self]

private theorem km_out_lose (y : ℝ) (h : 2 ≤ |y|) :
    outcome (Function.update knownMedianState 1 y) (fun _ : Fin 3 => (0:ℝ))
      = 2 := by
  unfold outcome winner
  rw [socialMedian_const km_card]
  have hdel : delegate (Function.update knownMedianState 1 y) (0:ℝ) = 0 := by
    have hf : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
    · rcases hf i with h0 | hone
      · rw [h0]
      · rw [hone, Function.update_self,
          Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
        have e0 : knownMedianState 0 = 2 := rfl
        rw [e0, sub_zero, sub_zero, show |(2:ℝ)| = 2 by norm_num]
        exact h
    · exact absurd hi (Fin.not_lt_zero i)
  rw [hdel, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  rfl

private theorem km_maxRegret (x : ℝ) :
    maxRegretOver knownMedianPeaks knownMedianState 1 x
        (constProfiles (Fin 3) 0 0)
      = regret knownMedianPeaks knownMedianState 1 x
          (fun _ : Fin 3 => (0:ℝ)) := by
  refine le_antisymm (maxRegretOver_le ⟨fun _ => 0, 0, ⟨le_rfl, le_rfl⟩, rfl⟩
    ?_) (regret_le_maxRegretOver ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩)
  rintro q ⟨μ, hμ, rfl⟩
  have hμ0 : μ = 0 := le_antisymm hμ.2 hμ.1
  rw [hμ0]

/-- **Theorem 4's uncertainty-spread hypothesis is necessary**: with a known
median, no report is minimax-regret — every report is strictly beaten by
one closer to the winner's mirror. -/
theorem knownMedian_no_isMinimaxRegret (r : ℝ) :
    ¬ IsMinimaxRegret knownMedianPeaks knownMedianState
      (constProfiles (Fin 3) 0 0) 1 r := by
  intro h
  by_cases hr : -2 < r ∧ r < 2
  · have h1 := h ((r - 2) / 2)
    rw [km_maxRegret, km_maxRegret] at h1
    unfold regret at h1
    rw [km_out_win r hr.1 hr.2,
      km_out_win ((r - 2) / 2) (by linarith [hr.1]) (by linarith [hr.2]),
      show knownMedianPeaks 1 = (-2:ℝ) from rfl] at h1
    rw [abs_of_pos (by linarith [hr.1]), abs_of_pos (by linarith [hr.1])] at h1
    linarith [hr.1]
  · have h1 := h 0
    rw [km_maxRegret, km_maxRegret] at h1
    unfold regret at h1
    have habs : (2:ℝ) ≤ |r| := by
      rcases not_and_or.mp hr with h' | h'
      · rw [not_lt] at h'
        rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [not_lt] at h'
        rw [abs_of_nonneg (by linarith)]
        exact h'
    rw [km_out_lose r habs, km_out_win 0 (by norm_num) (by norm_num),
      show knownMedianPeaks 1 = (-2:ℝ) from rfl,
      show |(2:ℝ) - -2| = 4 by norm_num,
      show |(0:ℝ) - -2| = 2 by norm_num] at h1
    linarith

/-! ## Minimax-regret endpoint play need not converge

The right-side proxy repeatedly reports the current upper endpoint of the
winner's median interval.  The information sets are nested point-mass profile
sets, so every median in the interval is realized robustly and Theorem 4's
minimax theorem applies at each step.  The true median is `0`, but proxy `0`
keeps winning at report `1`. -/

/-- Peaks for the endpoint trap.  Proxy `0` is the standing winner, proxy `1`
bounds the cell on the left, and proxy `2` is the right endpoint updater. -/
def minimaxTrapPeaks : Fin 3 → ℝ
  | 0 => 1
  | 1 => -3
  | 2 => 3

/-- The true followers all sit at median `0`. -/
def minimaxTrapFollowers : Fin 4 → ℝ := fun _ => 0

/-- The right proxy's report: `3, 2, 3/2, 5/4, ...`, converging down to the
standing winner's report `1`. -/
noncomputable def minimaxTrapRight : ℕ → ℝ
  | 0 => 3
  | t + 1 => (1 + minimaxTrapRight t) / 2

/-- The endpoint-trap state at time `t`. -/
noncomputable def minimaxTrapState (t : ℕ) : Fin 3 → ℝ
  | 0 => 1
  | 1 => -3
  | 2 => minimaxTrapRight t

/-- The theorem-4 information set at time `t`: point-mass profiles whose
common median lies in the current winner cell. -/
noncomputable def minimaxTrapInfo (t : ℕ) : Set (Fin 4 → ℝ) :=
  constProfiles (Fin 4) (-1) (minimaxTrapRight (t + 1))

private theorem minimaxTrap_card :
    Fintype.card (Fin 3) < Fintype.card (Fin 4) := by
  simp

private theorem minimaxTrapRight_one_lt (t : ℕ) : (1 : ℝ) < minimaxTrapRight t := by
  induction t with
  | zero =>
      norm_num [minimaxTrapRight]
  | succ t ih =>
      simp [minimaxTrapRight]
      linarith

private theorem minimaxTrapRight_le_three (t : ℕ) : minimaxTrapRight t ≤ (3 : ℝ) := by
  induction t with
  | zero =>
      norm_num [minimaxTrapRight]
  | succ t ih =>
      simp [minimaxTrapRight]
      linarith

private theorem minimaxTrapRight_succ_le (t : ℕ) :
    minimaxTrapRight (t + 1) ≤ minimaxTrapRight t := by
  simp [minimaxTrapRight]
  linarith [minimaxTrapRight_one_lt t]

private theorem minimaxTrap_info_refines_one_step (t : ℕ) :
    minimaxTrapInfo (t + 1) ⊆ minimaxTrapInfo t := by
  rintro q ⟨μ, hμ, rfl⟩
  refine ⟨μ, ⟨hμ.1, ?_⟩, rfl⟩
  exact le_trans hμ.2 (minimaxTrapRight_succ_le (t + 1))

private theorem minimaxTrap_true_mem_info (t : ℕ) :
    minimaxTrapFollowers ∈ minimaxTrapInfo t := by
  refine ⟨0, ?_, rfl⟩
  constructor
  · norm_num
  · linarith [minimaxTrapRight_one_lt (t + 1)]

private theorem minimaxTrap_delegate_cell (t : ℕ) (μ : ℝ)
    (hμ : μ ∈ Set.Icc (-1 : ℝ) (minimaxTrapRight (t + 1))) :
    delegate (minimaxTrapState t) μ = 0 := by
  refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
  · fin_cases i
    · rfl
    · change |(1 : ℝ) - μ| ≤ |-3 - μ|
      exact (abs_right_sub_le_abs_left_sub_iff
        (a := (-3 : ℝ)) (b := 1) (m := μ) (by norm_num)).2 (by
          norm_num
          exact hμ.1)
    · change |(1 : ℝ) - μ| ≤ |minimaxTrapRight t - μ|
      exact (abs_left_sub_le_abs_right_sub_iff
        (a := (1 : ℝ)) (b := minimaxTrapRight t) (m := μ)
        (minimaxTrapRight_one_lt t)).2 (by
          simpa [minimaxTrapRight] using hμ.2)
  · exact absurd hi (Fin.not_lt_zero i)

private theorem minimaxTrap_image_socialMedian_winnerInfoSet (t : ℕ) :
    (fun q => socialMedian (minimaxTrapState t) q) ''
        winnerInfoSet (F := Fin 4) (minimaxTrapState t) (0 : Fin 3)
      = Set.Icc (-1 : ℝ) (minimaxTrapRight (t + 1)) := by
  have h := image_socialMedian_winnerInfoSet_eq_Icc_of_neighbor_bounds
    (F := Fin 4) (s := minimaxTrapState t) minimaxTrap_card
    (jw := (0 : Fin 3)) (jl := (1 : Fin 3)) (jr := (2 : Fin 3))
    (by norm_num [minimaxTrapState])
    (by exact minimaxTrapRight_one_lt t)
    (by
      intro k hk
      fin_cases k
      · norm_num [minimaxTrapState] at hk
      · rfl
      · have hrt := minimaxTrapRight_one_lt t
        norm_num [minimaxTrapState] at hk
        linarith)
    (by
      intro k hk
      fin_cases k
      · norm_num [minimaxTrapState] at hk
      · norm_num [minimaxTrapState] at hk
      · rfl)
    (by intro k hk _; exact absurd hk (Fin.not_lt_zero k))
    (by intro k hk _; exact absurd hk (Fin.not_lt_zero k))
    (by intro k hk; exact absurd hk (Fin.not_lt_zero k))
  have hleft : ((1 : ℝ) + -3) / 2 = -1 := by norm_num
  simpa [minimaxTrapState, minimaxTrapRight, hleft, add_comm] using h

private theorem minimaxTrap_state_succ (t : ℕ) :
    minimaxTrapState (t + 1)
      = Function.update (minimaxTrapState t) (2 : Fin 3) (minimaxTrapRight (t + 1)) := by
  funext i
  fin_cases i <;> simp [minimaxTrapState]

private theorem minimaxTrap_step_minimax (t : ℕ) :
    IsMinimaxRegret minimaxTrapPeaks (minimaxTrapState t) (minimaxTrapInfo t)
      (2 : Fin 3) (minimaxTrapRight (t + 1)) := by
  change IsMinimaxRegret minimaxTrapPeaks (minimaxTrapState t)
    (constProfiles (Fin 4) (-1) (minimaxTrapRight (t + 1)))
      (2 : Fin 3) (minimaxTrapRight (t + 1))
  refine (isMinimaxRegret_constProfiles_iff_eq_right_boundary
    (pp := minimaxTrapPeaks) (s := minimaxTrapState t) (F := Fin 4)
    (j := (2 : Fin 3)) (jw := (0 : Fin 3)) (ℓ := (-1 : ℝ))
    (u := minimaxTrapRight (t + 1))
    minimaxTrap_card (minimaxTrap_delegate_cell t) (by decide) ?_ ?_ ?_).2 rfl
  · change 2 * minimaxTrapRight (t + 1) - 1 ≤ (3 : ℝ)
    simp [minimaxTrapRight]
    linarith [minimaxTrapRight_le_three t]
  · change (1 : ℝ) < minimaxTrapRight (t + 1)
    exact minimaxTrapRight_one_lt (t + 1)
  · change (-1 : ℝ) ≤ (minimaxTrapRight (t + 1) + 1) / 2
    linarith [minimaxTrapRight_one_lt (t + 1)]

theorem minimaxTrap_isMinimaxRegretInfoDynamics :
    IsMinimaxRegretInfoDynamics minimaxTrapPeaks minimaxTrapState minimaxTrapInfo := by
  intro t
  exact ⟨2, minimaxTrapRight (t + 1), minimaxTrap_step_minimax t,
    minimaxTrap_state_succ t⟩

private theorem minimaxTrap_socialMedian (t : ℕ) :
    socialMedian (minimaxTrapState t) minimaxTrapFollowers = 0 := by
  rw [show minimaxTrapFollowers = fun _ : Fin 4 => (0 : ℝ) from rfl]
  exact socialMedian_const minimaxTrap_card (minimaxTrapState t) 0

private theorem minimaxTrap_delegate_true (t : ℕ) :
    delegate (minimaxTrapState t) 0 = 0 :=
  minimaxTrap_delegate_cell t 0
    ⟨by norm_num, by linarith [minimaxTrapRight_one_lt (t + 1)]⟩

private theorem minimaxTrap_winner_true (t : ℕ) :
    winner (minimaxTrapState t) minimaxTrapFollowers = 0 := by
  unfold winner
  rw [minimaxTrap_socialMedian t, minimaxTrap_delegate_true t]

private theorem minimaxTrap_outcome (t : ℕ) :
    outcome (minimaxTrapState t) minimaxTrapFollowers = 1 := by
  unfold outcome winner
  rw [minimaxTrap_socialMedian t, minimaxTrap_delegate_true t]
  rfl

private theorem minimaxTrap_step_weakStrongMonotone (t : ℕ) :
    WeakStrongMonotoneOver (minimaxTrapState t)
      (winnerInfoSet (F := Fin 4) (minimaxTrapState t)
        (winner (minimaxTrapState t) minimaxTrapFollowers))
      (2 : Fin 3) (minimaxTrapRight (t + 1)) := by
  intro q hq
  have hq0 : q ∈ winnerInfoSet (F := Fin 4) (minimaxTrapState t) (0 : Fin 3) := by
    simpa [minimaxTrap_winner_true t] using hq
  have hm_image :
      socialMedian (minimaxTrapState t) q
        ∈ (fun q => socialMedian (minimaxTrapState t) q) ''
          winnerInfoSet (F := Fin 4) (minimaxTrapState t) (0 : Fin 3) :=
    ⟨q, hq0, rfl⟩
  have hm : socialMedian (minimaxTrapState t) q
      ∈ Set.Icc (-1 : ℝ) (minimaxTrapRight (t + 1)) := by
    simpa [minimaxTrap_image_socialMedian_winnerInfoSet t] using hm_image
  constructor
  · intro hs
    change minimaxTrapRight t ≤ socialMedian (minimaxTrapState t) q at hs
    linarith [minimaxTrapRight_succ_le t]
  · intro _hs
    exact hm.2

theorem minimaxTrap_isWeakStrongMonotoneDynamics :
    IsWeakStrongMonotoneDynamics minimaxTrapFollowers minimaxTrapState := by
  intro t
  exact Or.inl ⟨2, minimaxTrapRight (t + 1),
    minimaxTrap_step_weakStrongMonotone t, minimaxTrap_state_succ t⟩

theorem minimaxTrap_not_tendsto_socialMedian :
    ¬ Tendsto (fun t => outcome (minimaxTrapState t) minimaxTrapFollowers)
        atTop (nhds (socialMedian (minimaxTrapState 0) minimaxTrapFollowers)) := by
  intro h
  have hlim_one :
      Tendsto (fun t => outcome (minimaxTrapState t) minimaxTrapFollowers)
        atTop (nhds (1 : ℝ)) := by
    simp [minimaxTrap_outcome]
  have huniq := tendsto_nhds_unique h hlim_one
  rw [minimaxTrap_socialMedian 0] at huniq
  norm_num at huniq

/-- Active minimax-regret reports over nested, true-containing theorem-4
information sets do not imply convergence to the true social median.  The
missing convergence assumption is a genuine contraction condition, not merely
the fact that every step is minimax-regret. -/
theorem minimaxTrap_minimaxRegretInfo_not_tendsto :
    (∀ t, minimaxTrapInfo (t + 1) ⊆ minimaxTrapInfo t)
      ∧ (∀ t, minimaxTrapFollowers ∈ minimaxTrapInfo t)
      ∧ IsMinimaxRegretInfoDynamics minimaxTrapPeaks minimaxTrapState minimaxTrapInfo
      ∧ IsWeakStrongMonotoneDynamics minimaxTrapFollowers minimaxTrapState
      ∧ ¬ Tendsto (fun t => outcome (minimaxTrapState t) minimaxTrapFollowers)
          atTop (nhds (socialMedian (minimaxTrapState 0) minimaxTrapFollowers)) :=
  ⟨minimaxTrap_info_refines_one_step, minimaxTrap_true_mem_info,
    minimaxTrap_isMinimaxRegretInfoDynamics, minimaxTrap_isWeakStrongMonotoneDynamics,
    minimaxTrap_not_tendsto_socialMedian⟩

/-! ## Truth-oriented forcing needs the invariant guard

The forcing lemma used by the boundedness theorem is stated for states
satisfying the monotone-dynamics invariants.  The finite instance below
shows the unguarded version is false: at an off-invariant state a
non-anchored monotone better response need not make truth weakly best. -/

/-- The unguarded non-anchored forcing claim refuted by the finite
counterexample below. -/
def UnguardedNonAnchoredReportsForceTruth
    (pp : Fin 3 → ℝ) (q : Unit → ℝ) (s : Fin 3 → ℝ) : Prop :=
  ∀ j r, IsBetterResponse pp q s j r → MonotoneReport pp q j r →
    ¬ PeakAnchoredReport pp q j r → TruthWeaklyBestAmongBetterResponses pp q s j

/-- Peaks for the finite counterexample to the unguarded forcing condition. -/
def unguardedForcingCounterexamplePeaks : Fin 3 → ℝ
  | 0 => -3
  | 1 => -3
  | 2 => -2

/-- Follower profile for the finite counterexample to the unguarded forcing
condition. -/
def unguardedForcingCounterexampleFollowers : Unit → ℝ := fun _ => -1

/-- A drifted state for the finite counterexample.  This state is intentionally
not same-side with the peaks, so it cannot occur along a monotone dynamics from
truth. -/
def unguardedForcingCounterexampleState : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => -3

private abbrev cPeaks := unguardedForcingCounterexamplePeaks
private abbrev cFollowers := unguardedForcingCounterexampleFollowers
private abbrev cState := unguardedForcingCounterexampleState
private def cPeakPos : Fin 3 ⊕ Unit → ℝ := Sum.elim cPeaks cFollowers
private def cStatePos : Fin 3 ⊕ Unit → ℝ := Sum.elim cState cFollowers

private theorem cPeakPos_cum_neg3 : Math.cumWeight cPeakPos (fun _ => 1) (-3) = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Unit => cPeakPos a ≤ -3)
      = {Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [cPeakPos, cPeaks, unguardedForcingCounterexamplePeaks, Fin.ext_iff]
    | inr u => cases u; simp [cPeakPos, cFollowers, unguardedForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem socialMedian_cPeaks : socialMedian cPeaks cFollowers = -3 := by
  unfold socialMedian
  change Math.weightedMedian cPeakPos (fun _ => 1) = -3
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inl 0, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique,
      cPeakPos_cum_neg3]
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a with
    | inl j =>
        fin_cases j <;>
          norm_num [cPeakPos, cPeaks, unguardedForcingCounterexamplePeaks] at hltx
    | inr u =>
        cases u
        norm_num [cPeakPos, cFollowers, unguardedForcingCounterexampleFollowers] at hltx

private theorem cStatePos_cum_neg1 :
    Math.cumWeight cStatePos (fun _ => 1) (-1) = 2 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Unit => cStatePos a ≤ -1)
      = {Sum.inl (2 : Fin 3), Sum.inr Unit.unit} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          simp [cStatePos, cState, unguardedForcingCounterexampleState, Fin.ext_iff]
    | inr u => cases u; simp [cStatePos, cFollowers, unguardedForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem cStatePos_cum_neg3 :
    Math.cumWeight cStatePos (fun _ => 1) (-3) = 1 := by
  rw [Math.cumWeight]
  have hfilter : (Finset.univ.filter fun a : Fin 3 ⊕ Unit => cStatePos a ≤ -3)
      = {Sum.inl (2 : Fin 3)} := by
    ext a
    cases a with
    | inl j =>
        fin_cases j <;>
          simp [cStatePos, cState, unguardedForcingCounterexampleState, Fin.ext_iff]
    | inr u => cases u; simp [cStatePos, cFollowers, unguardedForcingCounterexampleFollowers]
  rw [hfilter]
  simp

private theorem socialMedian_cState : socialMedian cState cFollowers = -1 := by
  unfold socialMedian
  change Math.weightedMedian cStatePos (fun _ => 1) = -1
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?hp ?hcand ?hlt
  · exact Finset.mem_image.mpr ⟨Sum.inr Unit.unit, Finset.mem_univ _, rfl⟩
  · rw [Math.totalWeight_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_unique,
      cStatePos_cum_neg1]
  · intro x hx hltx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a with
    | inl j =>
        fin_cases j
        · norm_num [cStatePos, cState, unguardedForcingCounterexampleState] at hltx
        · norm_num [cStatePos, cState, unguardedForcingCounterexampleState] at hltx
        · change 2 * Math.cumWeight cStatePos (fun _ => 1) (-3) < 4
          rw [cStatePos_cum_neg3]
          norm_num
    | inr u =>
        cases u
        norm_num [cStatePos, cFollowers, unguardedForcingCounterexampleFollowers] at hltx

private theorem socialMedian_cSelected :
    socialMedian (Function.update cState (2 : Fin 3) (-1)) cFollowers = -1 := by
  have h := socialMedian_update_eq_of_proxy_lt (s := cState) (q := cFollowers)
    (j := (2 : Fin 3)) (r := -1)
    (by rw [socialMedian_cState]; norm_num [cState, unguardedForcingCounterexampleState])
    (by rw [socialMedian_cState])
  simpa [socialMedian_cState] using h

private theorem socialMedian_cTruth :
    socialMedian (Function.update cState (2 : Fin 3) (cPeaks 2)) cFollowers = -1 := by
  have h := socialMedian_update_eq_of_proxy_lt (s := cState) (q := cFollowers)
    (j := (2 : Fin 3)) (r := cPeaks 2)
    (by rw [socialMedian_cState]; norm_num [cState, unguardedForcingCounterexampleState])
    (by rw [socialMedian_cState]; norm_num [cPeaks, unguardedForcingCounterexamplePeaks])
  simpa [socialMedian_cState] using h

private theorem delegate_cState_neg1 : delegate cState (-1) = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [sub_neg_eq_add, Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    fin_cases k <;> norm_num [cState, unguardedForcingCounterexampleState]
  · intro b _
    exact Fin.zero_le b

private theorem delegate_cSelected_neg1 :
    delegate (Function.update cState (2 : Fin 3) (-1)) (-1) = 2 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp [cState, unguardedForcingCounterexampleState, Function.update_apply, Fin.ext_iff]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    fin_cases b
    · have hb2 := hb (2 : Fin 3)
      norm_num [cState, unguardedForcingCounterexampleState, Function.update_apply,
        Fin.ext_iff] at hb2
    · have hb2 := hb (2 : Fin 3)
      norm_num [cState, unguardedForcingCounterexampleState, Function.update_apply,
        Fin.ext_iff] at hb2
    · exact le_rfl

private theorem delegate_cTruth_neg1 :
    delegate (Function.update cState (2 : Fin 3) (cPeaks 2)) (-1) = 0 := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  constructor
  · simp only [Fin.isValue, sub_neg_eq_add, Finset.mem_filter, Finset.mem_univ, ne_eq,
      Fin.reduceEq, not_false_eq_true, Function.update_of_ne, true_and]
    intro k
    fin_cases k <;> norm_num [cState, cPeaks, unguardedForcingCounterexampleState,
      unguardedForcingCounterexamplePeaks, Function.update_apply, Fin.ext_iff]
  · intro b _
    exact Fin.zero_le b

private theorem outcome_cState : outcome cState cFollowers = 0 := by
  unfold outcome winner
  rw [socialMedian_cState, delegate_cState_neg1]
  rfl

private theorem outcome_cSelected :
    outcome (Function.update cState (2 : Fin 3) (-1)) cFollowers = -1 := by
  unfold outcome winner
  rw [socialMedian_cSelected, delegate_cSelected_neg1]
  simp

private theorem outcome_cTruth :
    outcome (Function.update cState (2 : Fin 3) (cPeaks 2)) cFollowers = 0 := by
  unfold outcome winner
  rw [socialMedian_cTruth, delegate_cTruth_neg1]
  simp [cState, unguardedForcingCounterexampleState]

private theorem cSelected_isBetterResponse :
    IsBetterResponse cPeaks cFollowers cState (2 : Fin 3) (-1) := by
  constructor
  · rw [outcome_cSelected, outcome_cState]
    norm_num
  · intro hsp
    norm_num [SPPrefers, cPeaks, unguardedForcingCounterexamplePeaks, outcome_cState,
      outcome_cSelected] at hsp

private theorem cSelected_monotone : MonotoneReport cPeaks cFollowers (2 : Fin 3) (-1) := by
  rw [MonotoneReport, socialMedian_cPeaks]
  norm_num [cPeaks, unguardedForcingCounterexamplePeaks]

private theorem cSelected_not_peakAnchored :
    ¬ PeakAnchoredReport cPeaks cFollowers (2 : Fin 3) (-1) := by
  rw [PeakAnchoredReport, socialMedian_cPeaks]
  norm_num [cPeaks, unguardedForcingCounterexamplePeaks]

private theorem cTruth_not_betterResponse :
    ¬ IsBetterResponse cPeaks cFollowers cState (2 : Fin 3) (cPeaks 2) := by
  intro h
  exact h.1 (by rw [outcome_cTruth, outcome_cState])

private theorem cTruth_not_weaklyBest :
    ¬ TruthWeaklyBestAmongBetterResponses cPeaks cFollowers cState (2 : Fin 3) := by
  intro h
  exact cTruth_not_betterResponse h.1

/-- Without the `SameSide` and fixed-median invariants, the forcing claim is
false.  The selected report
`-1` is a non-anchored monotone better response for proxy `2`, but reporting
truthfully leaves the outcome unchanged and is not a better response. -/
theorem unguardedNonAnchoredReportsForceTruth_counterexample :
    ¬ UnguardedNonAnchoredReportsForceTruth cPeaks cFollowers cState := by
  intro h
  exact cTruth_not_weaklyBest
    (h (2 : Fin 3) (-1) cSelected_isBetterResponse cSelected_monotone
      cSelected_not_peakAnchored)

/-- The counterexample state is outside the monotone-dynamics invariant: a proxy
whose peak is the true median reports away from it. -/
theorem unguardedForcingCounterexample_not_sameSide : ¬ SameSide cPeaks cFollowers cState := by
  intro h
  have h0 := (h 0).2.2
    (by rw [socialMedian_cPeaks]; norm_num [cPeaks, unguardedForcingCounterexamplePeaks])
  rw [socialMedian_cPeaks] at h0
  norm_num [cState, unguardedForcingCounterexampleState] at h0

/-! ## Median distance and social cost diverge (Section 2 footnote)

The paper's Section~2 footnote observes that "a good approximation of the true
median may have poor social cost, and vice versa."  The following truthful
profile witnesses both directions at once: two proxies at `0` and `3/2`, one
follower at `0`, and two followers at `1`.  The population median is `1`, so the
elected proxy is the one at `3/2` (distance `1/2`, strictly closer than the
proxy at `0`, whose distance is `1`).  Yet the position `0` has strictly smaller
social cost (`7/2`) than the elected position `3/2` (`4`).  So the best median
approximation is socially worse, and the socially cheaper proxy is the worse
median approximation. -/

/-- Section-2 footnote proxies: one at the population median-adjacent `0`, one
near the median at `3/2`. -/
noncomputable def footnotePeaks : Fin 2 → ℝ
  | 0 => 0
  | 1 => 3 / 2

/-- Section-2 footnote followers: one at `0`, two at `1`. -/
def footnoteFollowers : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1

private theorem footnote_cum_one :
    Math.cumWeight (allPos footnotePeaks footnoteFollowers) (fun _ => 1) 1 = 4 := by
  rw [Math.cumWeight]
  have hfilter :
      (Finset.univ.filter fun x : Fin 2 ⊕ Fin 3 =>
        allPos footnotePeaks footnoteFollowers x ≤ 1)
        = ({Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2} : Finset (Fin 2 ⊕ Fin 3)) := by
    ext x
    cases x with
    | inl j =>
        fin_cases j <;> simp [allPos, footnotePeaks]
        norm_num
    | inr u => fin_cases u <;> simp [allPos, footnoteFollowers]
  rw [hfilter]
  decide

private theorem footnote_cum_zero :
    Math.cumWeight (allPos footnotePeaks footnoteFollowers) (fun _ => 1) 0 = 2 := by
  rw [Math.cumWeight]
  have hfilter :
      (Finset.univ.filter fun x : Fin 2 ⊕ Fin 3 =>
        allPos footnotePeaks footnoteFollowers x ≤ 0)
        = ({Sum.inl 0, Sum.inr 0} : Finset (Fin 2 ⊕ Fin 3)) := by
    ext x
    cases x with
    | inl j => fin_cases j <;> simp [allPos, footnotePeaks]
    | inr u => fin_cases u <;> simp [allPos, footnoteFollowers]
  rw [hfilter]
  decide

private theorem footnote_socialMedian :
    socialMedian footnotePeaks footnoteFollowers = 1 := by
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr ⟨Sum.inr 1, Finset.mem_univ _, rfl⟩
  · rw [footnote_cum_one, Math.totalWeight_one, Fintype.card_sum]
    norm_num
  · intro z hz hzlt
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨a, rfl⟩ := hz
    cases a with
    | inl j =>
        fin_cases j
        · change 2 * Math.cumWeight (allPos footnotePeaks footnoteFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [footnote_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, footnotePeaks] at hzlt
    | inr f =>
        fin_cases f
        · change 2 * Math.cumWeight (allPos footnotePeaks footnoteFollowers)
            (fun _ => 1) 0 < Math.totalWeight fun _ => 1
          rw [footnote_cum_zero, Math.totalWeight_one, Fintype.card_sum]
          norm_num
        · norm_num [allPos, footnoteFollowers] at hzlt
        · norm_num [allPos, footnoteFollowers] at hzlt

private theorem footnote_delegate_one : delegate footnotePeaks 1 = 1 := by
  refine delegate_eq_of_forall_lt fun j hj => ?_
  fin_cases j
  · norm_num [footnotePeaks]
  · exact absurd rfl hj

private theorem footnote_outcome : outcome footnotePeaks footnoteFollowers = 3 / 2 := by
  unfold outcome winner
  rw [footnote_socialMedian, footnote_delegate_one]
  simp [footnotePeaks]

private theorem footnote_socialCost :
    socialCost footnotePeaks footnoteFollowers (3 / 2) = 4
      ∧ socialCost footnotePeaks footnoteFollowers 0 = 7 / 2 := by
  constructor <;>
  · unfold socialCost
    rw [Fintype.sum_sum_type]
    simp only [Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [allPos, footnotePeaks, footnoteFollowers]

/-- **Section 2 footnote, mechanized.**  Distance to the true median and social
cost genuinely diverge: at this truthful profile the weighted-median winner is
the proxy position strictly closest to the population median — the best median
approximation — yet the other proxy's position has strictly smaller social cost;
and that socially cheaper proxy is in turn strictly farther from the median. -/
theorem socialCost_and_median_distance_diverge :
    (∀ k, |outcome footnotePeaks footnoteFollowers
          - socialMedian footnotePeaks footnoteFollowers|
        ≤ |footnotePeaks k - socialMedian footnotePeaks footnoteFollowers|)
      ∧ socialCost footnotePeaks footnoteFollowers (footnotePeaks 0)
          < socialCost footnotePeaks footnoteFollowers
            (outcome footnotePeaks footnoteFollowers)
      ∧ |outcome footnotePeaks footnoteFollowers
            - socialMedian footnotePeaks footnoteFollowers|
          < |footnotePeaks 0 - socialMedian footnotePeaks footnoteFollowers| := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have h := delegate_dist_le footnotePeaks
      (socialMedian footnotePeaks footnoteFollowers) k
    simpa [outcome, winner] using h
  · have h1 : socialCost footnotePeaks footnoteFollowers
        (outcome footnotePeaks footnoteFollowers) = 4 := by
      rw [footnote_outcome]; exact footnote_socialCost.1
    have h2 : socialCost footnotePeaks footnoteFollowers (footnotePeaks 0) = 7 / 2 := by
      rw [show footnotePeaks 0 = (0 : ℝ) from rfl]; exact footnote_socialCost.2
    rw [h1, h2]; norm_num
  · rw [footnote_outcome, footnote_socialMedian, show footnotePeaks 0 = (0 : ℝ) from rfl]
    norm_num

end ProxyVoting

end GameTheory
