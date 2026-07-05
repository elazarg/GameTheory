/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.WindowedContraction
import GameTheory.Mechanism.ProxyVoting

/-!
# Better-response dynamics for proxy voting

Iterative play in Bielous–Meir strategic proxy games: proxies repeatedly play
better responses while followers stay truthful.  A report is a *better
response* when it changes the outcome and single-peakedness at the proxy's
peak does not force the old outcome above the new one, so some single-peaked
preference at that peak strictly prefers the change.  A dynamics is *monotone*
when every report stays on its proxy's side of the true population median,
strictly for off-median peaks.  The strict form is the invariant the step
lemmas carry; for pinning the median alone the paper's weak two-sided form
already suffices (`socialMedian_eq_of_weakMonotoneReports`).

## Main results

* `socialMedian_eq_of_isMonotoneDynamics` — Observation 1 (Bielous–Meir): the
  population median never moves along a monotone better-response dynamics.
* `monotoneStep_dist_le` / `monotoneStep_dist_lt` — Lemma 3 (Bielous–Meir): a
  monotone better response by a proxy other than the current winner never
  increases the outcome's distance to the true median, and strictly decreases
  it when no two distinct reports are equidistant from the median (mirror
  ties can preserve the distance while changing the winner).
* `eventually_outcome_eq_socialMedian_of_integral_nonWinnerTieFree_dynamics` —
  the one-step discrete convergence theorem: integral monotone
  dynamics from truth reach the true median exactly when every non-median
  state takes a non-winner, no-mirror-tie better response.
* `abs_outcome_sub_le_of_isMonotoneDynamics` — along a monotone dynamics the
  outcome is at least as close to the true median as every current report.
* `socialMedian_eq_of_weakMonotoneReports` — the median is already pinned,
  per state, by the paper's weak two-sided monotonicity.
* `metaMove_dist_le` / `metaMove_dist_lt` — Lemma 4 (Bielous–Meir): the weak
  distance bound holds at every intermediate step of a meta-move
  unconditionally; the strict decrease needs Lemma 3's no-mirror-tie
  hypothesis and peak separation
  (see `GameTheory.Mechanism.ProxyVoting.Counterexamples`).
* `tendsto_outcome_of_windowed_contraction` — Corollary 2 (Bielous–Meir):
  windowed contraction drives the outcome to the true median.
* `eventually_outcome_eq_socialMedian_of_windowed_decrease` — the
  section 4.4 discretization: with integral distances the outcome eventually
  equals the true median exactly.

The convergence wrappers take the window structure and the recurring
strict decrease as hypotheses.  The per-window bounds are discharged by
`monotoneStep_dist_le` / `metaMove_dist_le` and their discrete forms; that
strictly decreasing steps keep arriving is the behavioral premise the paper
asserts informally (its "big step" argument) and is not derivable from strict
improvement alone; see `Math.slow_harmonic_no_cofinal_fixed_factor_contraction`.

The worked example of the paper's Appendix A lives in
`GameTheory.Mechanism.ProxyVoting.AppendixA`.
-/

namespace GameTheory

namespace ProxyVoting

open Finset

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]
variable {pp : P → ℝ} {q : F → ℝ} {s : P → ℝ}

/-! ## Better responses and equilibrium -/

/-- `r` is a better response for proxy `j` at state `s`: it changes the
outcome, and the old outcome is not forced above the new one by
single-peakedness at `j`'s peak — some single-peaked preference with peak
`pp j` strictly prefers the new outcome. -/
def IsBetterResponse (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) (r : ℝ) : Prop :=
  outcome (Function.update s j r) q ≠ outcome s q
    ∧ ¬ SPPrefers (pp j) (outcome s q) (outcome (Function.update s j r) q)

/-- A pure Nash equilibrium of the proxy game: no proxy has a better
response. -/
def IsPNE (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  ∀ j r, ¬ IsBetterResponse pp q s j r

/-- A Euclidean improvement is a better response. -/
theorem isBetterResponse_of_prefers {j : P} {r : ℝ}
    (h : Prefers pp j (outcome (Function.update s j r) q) (outcome s q)) :
    IsBetterResponse pp q s j r := by
  constructor
  · intro heq
    simp only [Prefers, heq] at h
    exact absurd h (lt_irrefl _)
  · intro hsp
    exact absurd h (not_lt.mpr (le_of_lt hsp.abs_lt))

/-- If truthful reporting either attains the proxy's peak as the outcome or
matches the outcome of an already better response, then truthful reporting is
also a better response. -/
theorem IsBetterResponse.truth_of_outcome_eq_peak_or_eq {j : P} {r : ℝ}
    (hbr : IsBetterResponse pp q s j r)
    (hout_or : outcome (Function.update s j (pp j)) q = pp j ∨
      outcome (Function.update s j (pp j)) q = outcome (Function.update s j r) q) :
    IsBetterResponse pp q s j (pp j) := by
  constructor
  · intro hsame_old
    rcases hout_or with hpeak | hsame_report
    · have hold : outcome s q = pp j := by rw [← hsame_old, hpeak]
      have hreport_ne : outcome (Function.update s j r) q ≠ pp j := by
        intro hreport
        exact hbr.1 (by rw [hold, hreport])
      have hsp : SPPrefers (pp j) (outcome s q) (outcome (Function.update s j r) q) := by
        rw [hold]
        rcases lt_or_gt_of_ne hreport_ne.symm with hlt | hgt
        · exact Or.inl ⟨le_rfl, hlt⟩
        · exact Or.inr ⟨hgt, le_rfl⟩
      exact hbr.2 hsp
    · exact hbr.1 (by rw [← hsame_report, hsame_old])
  · intro hsp
    rcases hout_or with hpeak | hsame_report
    · rw [hpeak] at hsp
      rcases hsp with ⟨hle, hlt⟩ | ⟨hlt, hle⟩
      · exact absurd hlt (not_lt.mpr hle)
      · exact absurd hlt (not_lt.mpr hle)
    · exact hbr.2 (by rwa [hsame_report] at hsp)

/-! ## Monotone reports and the median invariant -/

/-- A report on the same side of the true population median as the proxy's
peak, strictly for off-median peaks. -/
def MonotoneReport (pp : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) : Prop :=
  (pp j < socialMedian pp q → r < socialMedian pp q)
    ∧ (socialMedian pp q < pp j → socialMedian pp q < r)
    ∧ (pp j = socialMedian pp q → r = socialMedian pp q)

/-- Every report sits on the same (strict) side of the true median as the
reporting proxy's peak. -/
def SameSide (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  ∀ j, (pp j < socialMedian pp q → s j < socialMedian pp q)
    ∧ (socialMedian pp q < pp j → socialMedian pp q < s j)
    ∧ (pp j = socialMedian pp q → s j = socialMedian pp q)

omit [LinearOrder P] in
theorem sameSide_self (pp : P → ℝ) (q : F → ℝ) : SameSide pp q pp :=
  fun _ => ⟨fun h => h, fun h => h, fun h => h⟩

/-- A monotone report from a same-side state keeps the population median at
the true median. -/
theorem socialMedian_update_eq_of_sameSide
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r) :
    socialMedian (Function.update s j r) q = socialMedian pp q := by
  rcases lt_trichotomy (pp j) (socialMedian pp q) with hj | hj | hj
  · have hsj : s j < socialMedian s q := by
      rw [hmed]; exact (hside j).1 hj
    have hr : r ≤ socialMedian s q := by
      rw [hmed]; exact le_of_lt (hmono.1 hj)
    rw [socialMedian_update_eq_of_proxy_lt hsj hr, hmed]
  · have hupdate : Function.update s j r = s := by
      rw [hmono.2.2 hj, ← (hside j).2.2 hj]
      exact Function.update_eq_self j s
    rw [hupdate, hmed]
  · have hsj : socialMedian s q < s j := by
      rw [hmed]; exact (hside j).2.1 hj
    have hr : socialMedian s q ≤ r := by
      rw [hmed]; exact le_of_lt (hmono.2.1 hj)
    rw [socialMedian_update_eq_of_proxy_gt hsj hr, hmed]

/-! ## Monotone dynamics -/

/-- A monotone better-response step: some proxy plays a monotone better
response. -/
def MonotoneStep (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ MonotoneReport pp q j r
    ∧ s' = Function.update s j r

/-- A monotone better-response dynamics from the truthful state: at each step
either some proxy plays a monotone better response, or the state rests. -/
def IsMonotoneDynamics (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp ∧ ∀ t, MonotoneStep pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

theorem MonotoneStep.sameSide {s' : P → ℝ}
    (h : MonotoneStep pp q s s') (hside : SameSide pp q s) :
    SameSide pp q s' := by
  obtain ⟨j, r, -, hmono, rfl⟩ := h
  intro k
  by_cases hk : k = j
  · subst hk
    refine ⟨fun hlt => ?_, fun hgt => ?_, fun heq => ?_⟩
    · rw [Function.update_self]; exact hmono.1 hlt
    · rw [Function.update_self]; exact hmono.2.1 hgt
    · rw [Function.update_self]; exact hmono.2.2 heq
  · refine ⟨fun hlt => ?_, fun hgt => ?_, fun heq => ?_⟩
    · rw [Function.update_apply, if_neg hk]; exact (hside k).1 hlt
    · rw [Function.update_apply, if_neg hk]; exact (hside k).2.1 hgt
    · rw [Function.update_apply, if_neg hk]; exact (hside k).2.2 heq

theorem MonotoneStep.socialMedian_eq {s' : P → ℝ}
    (h : MonotoneStep pp q s s') (hside : SameSide pp q s)
    (hmed : socialMedian s q = socialMedian pp q) :
    socialMedian s' q = socialMedian pp q := by
  obtain ⟨j, r, -, hmono, rfl⟩ := h
  exact socialMedian_update_eq_of_sameSide hside hmed hmono

/-- States along a monotone dynamics keep every report on its peak's side of
the true median, and keep the population median at the true median. -/
theorem sameSide_and_socialMedian_eq_of_isMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsMonotoneDynamics pp q σ) (t : ℕ) :
    SameSide pp q (σ t) ∧ socialMedian (σ t) q = socialMedian pp q := by
  induction t with
  | zero => rw [h.1]; exact ⟨sameSide_self pp q, rfl⟩
  | succ t ih =>
    rcases h.2 t with hstep | heq
    · exact ⟨hstep.sameSide ih.1, hstep.socialMedian_eq ih.1 ih.2⟩
    · rw [heq]; exact ih

/-- **Observation 1** (Bielous–Meir).  Along a monotone better-response
dynamics the population median never moves. -/
theorem socialMedian_eq_of_isMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsMonotoneDynamics pp q σ) (t : ℕ) :
    socialMedian (σ t) q = socialMedian pp q :=
  (sameSide_and_socialMedian_eq_of_isMonotoneDynamics h t).2

omit [LinearOrder P] in
/-- **Observation 1, per state, under the paper's weak monotonicity.**  If
every proxy with peak weakly left of the truthful population median reports
weakly left of it, and mirror-wise on the right — so a peak-at-median proxy
is pinned by the two clauses together — then the state's canonical median is
the truthful one.  The state's weakly-left population at the median contains
the truthful one, and its strictly-left population at any lower point is
contained in the truthful strictly-left population, which is less than half
of the total. -/
theorem socialMedian_eq_of_weakMonotoneReports {s : P → ℝ}
    (hle : ∀ j, pp j ≤ socialMedian pp q → s j ≤ socialMedian pp q)
    (hge : ∀ j, socialMedian pp q ≤ pp j → socialMedian pp q ≤ s j) :
    socialMedian s q = socialMedian pp q := by
  classical
  haveI : Nonempty (P ⊕ F) := ⟨Sum.inl (Classical.arbitrary P)⟩
  have hattain : ∃ a, allPos s q a = socialMedian pp q := by
    obtain ⟨a, ha⟩ :=
      Math.exists_pos_eq_weightedMedian (allPos pp q) (fun _ => 1)
    cases a with
    | inl k =>
        have hk : pp k = socialMedian pp q := ha
        exact ⟨Sum.inl k,
          le_antisymm (hle k (le_of_eq hk)) (hge k (le_of_eq hk.symm))⟩
    | inr f => exact ⟨Sum.inr f, ha⟩
  obtain ⟨a₀, ha₀⟩ := hattain
  have hqual : Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ))
      ≤ 2 * Math.cumWeight (allPos s q) (fun _ => 1) (socialMedian pp q) := by
    have h1 : Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ))
        ≤ 2 * Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian pp q) :=
      Math.totalWeight_le_two_mul_cumWeight_weightedMedian
        (allPos pp q) (fun _ => 1)
    have h2 : Math.cumWeight (allPos pp q) (fun _ => 1) (socialMedian pp q)
        ≤ Math.cumWeight (allPos s q) (fun _ => 1) (socialMedian pp q) := by
      refine Math.cumWeight_le_cumWeight_of_imp (fun _ => 1) ?_
      intro a ha
      cases a with
      | inl k => exact hle k ha
      | inr f => exact ha
    omega
  change Math.weightedMedian (allPos s q) (fun _ => 1) = socialMedian pp q
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt
    (ha₀ ▸ Finset.mem_image_of_mem (allPos s q) (Finset.mem_univ a₀))
    hqual ?_
  intro z _ hzm
  have hsub : Math.cumWeight (allPos s q) (fun _ => 1) z
      ≤ Math.leftWeight (allPos pp q) (fun _ => 1) (socialMedian pp q) := by
    unfold Math.cumWeight Math.leftWeight
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨ha.1, ?_⟩
    cases a with
    | inl k =>
        have hs : s k ≤ z := ha.2
        by_contra hkm
        rw [not_lt] at hkm
        exact absurd hzm (not_lt.mpr (le_trans (hge k hkm) hs))
    | inr f => exact lt_of_le_of_lt ha.2 hzm
  have hlw : 2 * Math.leftWeight (allPos pp q) (fun _ => 1) (socialMedian pp q)
      < Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ)) :=
    Math.two_mul_leftWeight_weightedMedian_lt
      (allPos pp q) (fun _ => 1) Math.totalWeight_one_pos
  omega

/-! ## Distance to the true median -/

/-- The outcome never lies farther from the population median than any
reported position. -/
theorem abs_outcome_sub_socialMedian_le (s : P → ℝ) (q : F → ℝ) (k : P) :
    |outcome s q - socialMedian s q| ≤ |s k - socialMedian s q| := by
  change |s (delegate s (socialMedian s q)) - socialMedian s q| ≤ _
  exact delegate_dist_le s (socialMedian s q) k

/-- Along a monotone dynamics, the outcome is at least as close to the true
median as every current report. -/
theorem abs_outcome_sub_le_of_isMonotoneDynamics {σ : ℕ → P → ℝ}
    (h : IsMonotoneDynamics pp q σ) (t : ℕ) (k : P) :
    |outcome (σ t) q - socialMedian pp q| ≤ |σ t k - socialMedian pp q| := by
  have hd := abs_outcome_sub_socialMedian_le (σ t) q k
  rw [socialMedian_eq_of_isMonotoneDynamics h t] at hd
  exact hd

/-- **Lemma 3** (Bielous–Meir), weak form.  A monotone better response by a
proxy other than the current winner never increases the outcome's distance to
the true median: the old winner's report is unchanged and still bounds the new
winner's distance. -/
theorem monotoneStep_dist_le
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r) (hj : j ≠ winner s q) :
    |outcome (Function.update s j r) q - socialMedian pp q|
      ≤ |outcome s q - socialMedian pp q| := by
  have hmed' : socialMedian (Function.update s j r) q = socialMedian pp q :=
    socialMedian_update_eq_of_sameSide hside hmed hmono
  have hd := abs_outcome_sub_socialMedian_le (Function.update s j r) q (winner s q)
  rw [hmed'] at hd
  have hsw : Function.update s j r (winner s q) = outcome s q := by
    rw [Function.update_apply, if_neg (fun h => hj h.symm)]
    rfl
  rw [hsw] at hd
  rw [← hmed, hmed]
  exact hd

/-- **Lemma 3** (Bielous–Meir).  A monotone better response by a proxy other
than the current winner strictly decreases the outcome's distance to the true
median, provided no two distinct reports after the move are equidistant from
the median — equidistant mirror configurations can hand the win across the
median at unchanged distance. -/
theorem monotoneStep_dist_lt
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hbr : IsBetterResponse pp q s j r)
    (hmono : MonotoneReport pp q j r) (hj : j ≠ winner s q)
    (htie : ∀ k k', |Function.update s j r k - socialMedian pp q|
        = |Function.update s j r k' - socialMedian pp q|
      → Function.update s j r k = Function.update s j r k') :
    |outcome (Function.update s j r) q - socialMedian pp q|
      < |outcome s q - socialMedian pp q| := by
  rcases lt_or_eq_of_le (monotoneStep_dist_le hside hmed hmono hj) with hlt | heq
  · exact hlt
  · exfalso
    have hsw : Function.update s j r (winner s q) = outcome s q := by
      rw [Function.update_apply, if_neg (fun h => hj h.symm)]
      rfl
    have h1 : Function.update s j r (winner (Function.update s j r) q)
        = Function.update s j r (winner s q) := by
      apply htie
      rw [hsw]
      exact heq
    apply hbr.1
    rw [← hsw, ← h1]
    rfl

/-- **Discretization** (Bielous-Meir, section 4.4).  With integral peaks,
followers, reports, and move, a monotone better response by a proxy other
than the current winner decreases the outcome's distance to the true median
by at least one, under the mirror-tie hypothesis of `monotoneStep_dist_lt`. -/
theorem monotoneStep_dist_add_one_le
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hbr : IsBetterResponse pp q s j r)
    (hmono : MonotoneReport pp q j r) (hj : j ≠ winner s q)
    (htie : ∀ k k', |Function.update s j r k - socialMedian pp q|
        = |Function.update s j r k' - socialMedian pp q|
      → Function.update s j r k = Function.update s j r k')
    (hpp : ∀ k, ∃ n : ℤ, pp k = n) (hq : ∀ i, ∃ n : ℤ, q i = n)
    (hs : ∀ k, ∃ n : ℤ, s k = n) (hr : ∃ n : ℤ, r = n) :
    |outcome (Function.update s j r) q - socialMedian pp q| + 1
      ≤ |outcome s q - socialMedian pp q| := by
  have hs' : ∀ k, ∃ n : ℤ, Function.update s j r k = n := by
    intro k
    rw [Function.update_apply]
    split
    · exact hr
    · exact hs k
  have hmpp := exists_int_socialMedian hpp hq
  exact Math.add_one_le_of_lt_of_int
    (Math.exists_int_abs_sub (exists_int_outcome q hs') hmpp)
    (Math.exists_int_abs_sub (exists_int_outcome q hs) hmpp)
    (monotoneStep_dist_lt hside hmed hbr hmono hj htie)

/-! ## One-step discrete convergence -/

/-- A proxy report state whose reports are all integers. -/
def IsIntegralState (s : P → ℝ) : Prop := ∀ k, ∃ n : ℤ, s k = n

/-- No two distinct reports are mirror-tied around `m`. -/
def NoMirrorTieAt (s : P → ℝ) (m : ℝ) : Prop :=
  ∀ k k', |s k - m| = |s k' - m| → s k = s k'

/-- A monotone better-response step by a proxy other than the current winner
whose resulting state has no mirror tie around the true median.  This is the
one-step case where the section 4.4 integer decrease is actually available. -/
def NonWinnerTieFreeMonotoneStep
    (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ MonotoneReport pp q j r
    ∧ j ≠ winner s q ∧ NoMirrorTieAt s' (socialMedian pp q)
    ∧ s' = Function.update s j r

theorem NonWinnerTieFreeMonotoneStep.toMonotoneStep {s s' : P → ℝ}
    (h : NonWinnerTieFreeMonotoneStep pp q s s') : MonotoneStep pp q s s' := by
  obtain ⟨j, r, hbr, hmono, _hj, _htie, hs'⟩ := h
  exact ⟨j, r, hbr, hmono, hs'⟩

theorem isMonotoneDynamics_of_nonWinnerTieFree_steps {σ : ℕ → P → ℝ}
    (h0 : σ 0 = pp)
    (hstep : ∀ t,
      NonWinnerTieFreeMonotoneStep pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t) :
    IsMonotoneDynamics pp q σ := by
  constructor
  · exact h0
  · intro t
    rcases hstep t with h | hrest
    · exact Or.inl h.toMonotoneStep
    · exact Or.inr hrest

/-- One-step form of the section 4.4 discretization.  If an
integral monotone dynamics from truth makes a non-winner, no-mirror-tie
better response whenever the outcome is not yet the true median, then the
outcome eventually equals the true median exactly.

The no-mirror-tie progress condition is taken as a hypothesis rather than
derived: integer spacing alone does not preserve the no-mirror-tie condition,
and winner meta-moves need their own invariant, so both are supplied as
premises. -/
theorem eventually_outcome_eq_socialMedian_of_integral_nonWinnerTieFree_dynamics
    {σ : ℕ → P → ℝ}
    (h0 : σ 0 = pp)
    (hstep : ∀ t,
      NonWinnerTieFreeMonotoneStep pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t)
    (hprogress : ∀ t, outcome (σ t) q ≠ socialMedian pp q →
      NonWinnerTieFreeMonotoneStep pp q (σ t) (σ (t + 1)))
    (hpp : ∀ k, ∃ n : ℤ, pp k = n) (hq : ∀ i, ∃ n : ℤ, q i = n)
    (hs : ∀ t, IsIntegralState (σ t)) :
    ∀ᶠ t in Filter.atTop, outcome (σ t) q = socialMedian pp q := by
  have hdyn : IsMonotoneDynamics pp q σ :=
    isMonotoneDynamics_of_nonWinnerTieFree_steps h0 hstep
  have hint : ∀ t, ∃ n : ℤ, |outcome (σ t) q - socialMedian pp q| = n := by
    intro t
    exact Math.exists_int_abs_sub (exists_int_outcome q (hs t))
      (exists_int_socialMedian hpp hq)
  have htop : Filter.Tendsto (id : ℕ → ℕ) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => ha⟩
  have hwindow : ∀ k u, id k ≤ u → u ≤ id (k + 1) →
      |outcome (σ u) q - socialMedian pp q|
        ≤ |outcome (σ (id k)) q - socialMedian pp q| := by
    intro k u hku huk
    change k ≤ u at hku
    change u ≤ k + 1 at huk
    change |outcome (σ u) q - socialMedian pp q|
      ≤ |outcome (σ k) q - socialMedian pp q|
    rcases eq_or_lt_of_le hku with rfl | hku_lt
    · rfl
    · have hu : u = k + 1 := by omega
      subst u
      rcases hstep k with hactive | hrest
      · obtain ⟨j, r, _hbr, hmono, hj, _htie, hupd⟩ := hactive
        rw [hupd]
        have hinv := sameSide_and_socialMedian_eq_of_isMonotoneDynamics hdyn k
        exact monotoneStep_dist_le hinv.1 hinv.2 hmono hj
      · rw [hrest]
  have hdec : ∀ k, |outcome (σ (id k)) q - socialMedian pp q| ≠ 0 →
      ∃ k', k ≤ k' ∧
        |outcome (σ (id (k' + 1))) q - socialMedian pp q|
          < |outcome (σ (id k')) q - socialMedian pp q| := by
    intro k hk
    change |outcome (σ k) q - socialMedian pp q| ≠ 0 at hk
    refine ⟨k, le_rfl, ?_⟩
    have hkout : outcome (σ k) q ≠ socialMedian pp q := by
      intro hout
      exact hk (by rw [hout, sub_self, abs_zero])
    obtain ⟨j, r, hbr, hmono, hj, htie, hupd⟩ := hprogress k hkout
    have hinv := sameSide_and_socialMedian_eq_of_isMonotoneDynamics hdyn k
    have hr : ∃ n : ℤ, r = n := by
      obtain ⟨n, hn⟩ := hs (k + 1) j
      rw [hupd, Function.update_self] at hn
      exact ⟨n, hn⟩
    have htie_update : ∀ a b,
        |Function.update (σ k) j r a - socialMedian pp q|
            = |Function.update (σ k) j r b - socialMedian pp q|
          → Function.update (σ k) j r a = Function.update (σ k) j r b := by
      simpa [NoMirrorTieAt, hupd] using htie
    have hstep_dec := monotoneStep_dist_add_one_le hinv.1 hinv.2 hbr hmono hj
      htie_update hpp hq (hs k) hr
    rw [← hupd] at hstep_dec
    have hnonneg : 0 ≤ |outcome (σ (k + 1)) q - socialMedian pp q| := abs_nonneg _
    change |outcome (σ (k + 1)) q - socialMedian pp q|
      < |outcome (σ k) q - socialMedian pp q|
    linarith
  have hzero := Math.eventually_zero_of_windowed_decrease
    (d := fun t => |outcome (σ t) q - socialMedian pp q|) (b := id)
    (fun _ => abs_nonneg _) hint rfl monotone_id htop hwindow hdec
  refine hzero.mono fun t ht => ?_
  rw [abs_eq_zero, sub_eq_zero] at ht
  exact ht

/-! ## Meta-moves -/

/-- A meta-move: a proxy other than the current winner takes the win and then
keeps moving, holding the win after each of its `ℓ` monotone better
responses. -/
def MetaMove (pp : P → ℝ) (q : F → ℝ) (j : P) (σ : ℕ → P → ℝ) (ℓ : ℕ) : Prop :=
  0 < ℓ ∧ j ≠ winner (σ 0) q
    ∧ (∀ i < ℓ, ∃ r, IsBetterResponse pp q (σ i) j r ∧ MonotoneReport pp q j r
        ∧ σ (i + 1) = Function.update (σ i) j r)
    ∧ ∀ i, 0 < i → i ≤ ℓ → winner (σ i) q = j

theorem MetaMove.monotoneStep {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ) {i : ℕ} (hi : i < ℓ) :
    MonotoneStep pp q (σ i) (σ (i + 1)) := by
  obtain ⟨r, hbr, hmono, hupd⟩ := h.2.2.1 i hi
  exact ⟨j, r, hbr, hmono, hupd⟩

/-- The monotone-dynamics invariants propagate along a meta-move. -/
theorem MetaMove.sameSide_and_socialMedian_eq {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q) {i : ℕ} (hi : i ≤ ℓ) :
    SameSide pp q (σ i) ∧ socialMedian (σ i) q = socialMedian pp q := by
  induction i with
  | zero => exact ⟨hside, hmed⟩
  | succ i ih =>
    have hih := ih (le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self i) hi))
    have hstep := h.monotoneStep (lt_of_lt_of_le (Nat.lt_succ_self i) hi)
    exact ⟨hstep.sameSide hih.1, hstep.socialMedian_eq hih.1 hih.2⟩

/-- The old winner's report survives a meta-move untouched. -/
theorem MetaMove.winner_report_eq {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ) {i : ℕ} (hi : i ≤ ℓ) :
    σ i (winner (σ 0) q) = σ 0 (winner (σ 0) q) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    obtain ⟨r, -, -, hupd⟩ := h.2.2.1 i (lt_of_lt_of_le (Nat.lt_succ_self i) hi)
    rw [hupd, Function.update_apply, if_neg (fun hk => h.2.1 hk.symm)]
    exact ih (le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self i) hi))

/-- **Lemma 4** (Bielous–Meir), weak form.  Throughout a meta-move the
outcome's distance to the true median never exceeds its starting value: the
old winner's untouched report bounds every intermediate winner. -/
theorem metaMove_dist_le {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q) {i : ℕ} (hi : i ≤ ℓ) :
    |outcome (σ i) q - socialMedian pp q| ≤ |outcome (σ 0) q - socialMedian pp q| := by
  have hinv := h.sameSide_and_socialMedian_eq hside hmed hi
  have hd := abs_outcome_sub_socialMedian_le (σ i) q (winner (σ 0) q)
  rw [hinv.2, h.winner_report_eq hi] at hd
  exact hd

/-- **Lemma 4** (Bielous–Meir), strict form.  A meta-move strictly decreases
the outcome's distance to the true median, provided no two distinct final
reports are equidistant from the median, and the starting outcome is at least
as close to the median as every peak.  Both hypotheses are needed: without
the first the mover can finish exactly on the old winner's mirror image, and
without the second a mover whose peak lies strictly inside the winner's
interval can take the win inside and then return the outcome to the old
winning position — a better response even for Euclidean preferences. -/
theorem metaMove_dist_lt {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q)
    (hsep : ∀ k, |outcome (σ 0) q - socialMedian pp q|
      ≤ |pp k - socialMedian pp q|)
    (htie : ∀ k k', |σ ℓ k - socialMedian pp q| = |σ ℓ k' - socialMedian pp q|
      → σ ℓ k = σ ℓ k') :
    |outcome (σ ℓ) q - socialMedian pp q| < |outcome (σ 0) q - socialMedian pp q| := by
  rcases lt_or_eq_of_le (metaMove_dist_le h hside hmed (le_refl ℓ)) with hlt | heq
  · exact hlt
  exfalso
  -- Notation: the pinned median, the old winner, and its surviving position.
  obtain ⟨r₀, hbr₀, hmono₀, hupd₀⟩ := h.2.2.1 0 h.1
  have hwin1 : winner (σ 1) q = j := h.2.2.2 1 one_pos h.1
  have hout1 : outcome (σ 1) q = σ 1 j := by rw [outcome, hwin1]
  -- The first move changes the outcome, so the starting distance is positive.
  have hΔpos : 0 < |outcome (σ 0) q - socialMedian pp q| := by
    rcases (abs_nonneg (outcome (σ 0) q - socialMedian pp q)).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have hO0 : outcome (σ 0) q = socialMedian pp q :=
        sub_eq_zero.mp (abs_eq_zero.mp h0.symm)
      have hd1 := metaMove_dist_le h hside hmed (i := 1) h.1
      rw [← h0] at hd1
      have hO1 : outcome (σ 1) q = socialMedian pp q :=
        sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd1 (abs_nonneg _)))
      refine hbr₀.1 ?_
      rw [← hupd₀]
      exact hO1.trans hO0.symm
  -- The final winner is the mover, equidistant with the old winner's report,
  -- so by the tie hypothesis it sits exactly on the old winning position.
  have hwinℓ : winner (σ ℓ) q = j := h.2.2.2 ℓ h.1 (le_refl ℓ)
  have houtℓ : outcome (σ ℓ) q = σ ℓ j := by rw [outcome, hwinℓ]
  have hk₀ : σ ℓ (winner (σ 0) q) = σ 0 (winner (σ 0) q) :=
    h.winner_report_eq (le_refl ℓ)
  have hjℓ : σ ℓ j = outcome (σ 0) q := by
    have := htie j (winner (σ 0) q)
      (by rw [hk₀]; rw [houtℓ] at heq; exact heq)
    rw [this, hk₀]
    rfl
  -- The mover's peak therefore lies strictly on the old outcome's side.
  set m := socialMedian pp q with hm
  have hsideℓ := (h.sameSide_and_socialMedian_eq hside hmed (le_refl ℓ)).1
  have hside1 := (h.sameSide_and_socialMedian_eq hside hmed (i := 1) h.1).1
  have hd1 : |outcome (σ 1) q - m| ≤ |outcome (σ 0) q - m| :=
    metaMove_dist_le h hside hmed (i := 1) h.1
  have hne1 : outcome (σ 1) q ≠ outcome (σ 0) q := by
    intro hcontra
    exact hbr₀.1 (by rw [← hupd₀]; exact hcontra)
  rcases lt_trichotomy (outcome (σ 0) q) m with hw | hw | hw
  · -- Old outcome strictly left: the mover's peak is weakly left of it, but
    -- the takeover moved the outcome strictly toward the median — refuted.
    have hpj : pp j < m := by
      rcases lt_trichotomy (pp j) m with hp | hp | hp
      · exact hp
      · exfalso
        have := (hsideℓ j).2.2 hp
        rw [hjℓ] at this
        linarith
      · exfalso
        have := (hsideℓ j).2.1 hp
        rw [hjℓ] at this
        linarith
    have hs1j : σ 1 j < m := (hside1 j).1 hpj
    have habs0 : |outcome (σ 0) q - m| = m - outcome (σ 0) q := by
      rw [abs_of_neg (by linarith)]
      ring
    have hge : outcome (σ 0) q ≤ outcome (σ 1) q := by
      rw [hout1]
      rw [hout1, abs_of_neg (by linarith), habs0] at hd1
      linarith
    have hpk : pp j ≤ outcome (σ 0) q := by
      have hs := hsep j
      rw [habs0, abs_of_neg (by linarith)] at hs
      linarith
    refine hbr₀.2 ?_
    rw [← hupd₀]
    exact Or.inl ⟨hpk, lt_of_le_of_ne hge (Ne.symm hne1)⟩
  · rw [hw, sub_self, abs_zero] at hΔpos
    exact lt_irrefl _ hΔpos
  · -- Mirror case: old outcome strictly right.
    have hpj : m < pp j := by
      rcases lt_trichotomy (pp j) m with hp | hp | hp
      · exfalso
        have := (hsideℓ j).1 hp
        rw [hjℓ] at this
        linarith
      · exfalso
        have := (hsideℓ j).2.2 hp
        rw [hjℓ] at this
        linarith
      · exact hp
    have hs1j : m < σ 1 j := (hside1 j).2.1 hpj
    have habs0 : |outcome (σ 0) q - m| = outcome (σ 0) q - m :=
      abs_of_pos (by linarith)
    have hge : outcome (σ 1) q ≤ outcome (σ 0) q := by
      rw [hout1]
      rw [hout1, abs_of_pos (by linarith), habs0] at hd1
      linarith
    have hpk : outcome (σ 0) q ≤ pp j := by
      have hs := hsep j
      rw [habs0, abs_of_pos (by linarith)] at hs
      linarith
    refine hbr₀.2 ?_
    rw [← hupd₀]
    exact Or.inr ⟨lt_of_le_of_ne hge hne1, hpk⟩

/-- **Corollary 2** (Bielous-Meir), stated as the abstract window theorem used
by the dynamics layer.  If the outcome's distance to the true median is
dominated on each boundary window by its left-boundary value, and the boundary
values contract by a fixed factor `α < 1` cofinally often, then the outcome
converges to the true median.  Lemmas 3 and 4 prove the per-step and meta-move
distance bounds used to discharge such a window premise in concrete dynamics;
this theorem does not itself assemble a meta-move window decomposition. -/
theorem tendsto_outcome_of_windowed_contraction {σ : ℕ → P → ℝ} {b : ℕ → ℕ} {α : ℝ}
    (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hwindow : ∀ k u, b k ≤ u → u ≤ b (k + 1) →
      |outcome (σ u) q - socialMedian pp q|
        ≤ |outcome (σ (b k)) q - socialMedian pp q|)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbig : ∀ k, ∃ k', k ≤ k' ∧
      |outcome (σ (b (k' + 1))) q - socialMedian pp q|
        ≤ α * |outcome (σ (b k')) q - socialMedian pp q|) :
    Filter.Tendsto (fun t => outcome (σ t) q) Filter.atTop
      (nhds (socialMedian pp q)) := by
  have h := Math.tendsto_zero_of_windowed_contraction
    (d := fun t => |outcome (σ t) q - socialMedian pp q|) (b := b)
    (fun _ => abs_nonneg _) hb0 hbmono htop hwindow hα0 hα1 hbig
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using h

/-- **Discretization** (Bielous-Meir, section 4.4), meta-move form.  With
integral peaks, followers, and endpoint states, a meta-move decreases the
outcome's distance to the true median by at least one, under the hypotheses
of `metaMove_dist_lt`. -/
theorem metaMove_dist_add_one_le {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMove pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q)
    (hsep : ∀ k, |outcome (σ 0) q - socialMedian pp q|
      ≤ |pp k - socialMedian pp q|)
    (htie : ∀ k k', |σ ℓ k - socialMedian pp q| = |σ ℓ k' - socialMedian pp q|
      → σ ℓ k = σ ℓ k')
    (hpp : ∀ k, ∃ n : ℤ, pp k = n) (hq : ∀ i, ∃ n : ℤ, q i = n)
    (h0 : ∀ k, ∃ n : ℤ, σ 0 k = n) (hℓ : ∀ k, ∃ n : ℤ, σ ℓ k = n) :
    |outcome (σ ℓ) q - socialMedian pp q| + 1
      ≤ |outcome (σ 0) q - socialMedian pp q| := by
  have hmpp := exists_int_socialMedian hpp hq
  exact Math.add_one_le_of_lt_of_int
    (Math.exists_int_abs_sub (exists_int_outcome q hℓ) hmpp)
    (Math.exists_int_abs_sub (exists_int_outcome q h0) hmpp)
    (metaMove_dist_lt h hside hmed hsep htie)

/-- **Discretization convergence** (Bielous-Meir, section 4.4).  Along a
dynamics with integral outcome distances, window domination — supplied by
`monotoneStep_dist_le` and `metaMove_dist_le` — and a strict boundary decrease
somewhere ahead whenever the outcome misses the true median — supplied by
`monotoneStep_dist_add_one_le` and `metaMove_dist_add_one_le` while better
responses keep arriving — the outcome eventually equals the true median
exactly. -/
theorem eventually_outcome_eq_socialMedian_of_windowed_decrease
    {σ : ℕ → P → ℝ} {b : ℕ → ℕ}
    (hint : ∀ t, ∃ n : ℤ, |outcome (σ t) q - socialMedian pp q| = n)
    (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hwindow : ∀ k u, b k ≤ u → u ≤ b (k + 1) →
      |outcome (σ u) q - socialMedian pp q|
        ≤ |outcome (σ (b k)) q - socialMedian pp q|)
    (hdec : ∀ k, outcome (σ (b k)) q ≠ socialMedian pp q →
      ∃ k', k ≤ k' ∧ |outcome (σ (b (k' + 1))) q - socialMedian pp q|
        < |outcome (σ (b k')) q - socialMedian pp q|) :
    ∀ᶠ t in Filter.atTop, outcome (σ t) q = socialMedian pp q := by
  have h := Math.eventually_zero_of_windowed_decrease
    (d := fun t => |outcome (σ t) q - socialMedian pp q|) (b := b)
    (fun _ => abs_nonneg _) hint hb0 hbmono htop hwindow
    (fun k hk => hdec k (fun hc => hk (by rw [hc, sub_self, abs_zero])))
  refine h.mono fun t ht => ?_
  rw [abs_eq_zero, sub_eq_zero] at ht
  exact ht

end ProxyVoting

end GameTheory
