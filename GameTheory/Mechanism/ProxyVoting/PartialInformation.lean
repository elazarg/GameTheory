/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Dynamics

/-!
# Proxy voting under partial information

The partial-information layer of Bielous–Meir strategic proxy games, in the
poll-information framework of Reijngoud–Endriss.  Proxies observe the reported
state and the identity of the winner, but not the followers' positions; the
*information set* collects every follower profile consistent with the
observation.  A *dominating manipulation* (Conitzer et al.) is a report that
is weakly better against every consistent profile and strictly better against
at least one, under Euclidean preferences at the proxy's peak.

Dominance and strong monotonicity each come in two preference readings, as
elsewhere in this development: the forced single-peaked form (`SPPrefers` /
`SPWeaklyPrefers`), which holds for every single-peaked preference at the
proxy's peak, and the Euclidean form as its consequence.

## Main results

* `IsDominatingManipulation.true_profile_le` — a dominating manipulation never
  hurts: against the true (consistent) profile the outcome is weakly better.
* `dominatesOver_singleton_iff` / `isBetterResponse_of_dominatesOver_singleton`
  — with full information the information set collapses to a singleton and
  dominating manipulations are exactly Euclidean better responses.
* `socialMedian_update_eq_of_strongMonotoneOver` — a strong-monotone report
  keeps the population median unchanged at every consistent profile.
* `WeakStrongMonotoneOver` /
  `socialMedian_update_eq_of_weakStrongMonotoneOver` — the endpoint-tolerant
  weak non-crossing replacement used by boundary minimax-regret reports.
* `strongMonotoneOver_singleton_iff_monotoneReport` — with full information,
  at a state satisfying the monotone-dynamics invariants, strong-monotone
  reports are exactly monotone reports.
* `socialMedian_eq_of_isStrongMonotoneDynamics` — along a strong-monotone
  dynamics the population median at the true follower profile never moves,
  even though the proxies never observe it.
* `isMinimaxRegret_dominatesOver_leftBoundary` /
  `isMinimaxRegret_dominatesOver_rightBoundary` — the paper's minimax-regret
  implies dominance remark, restricted to the non-winning boundary regimes
  where it is true; stay-put minimax reports are explicitly non-dominating
  (`not_dominatesOver_stay`).
* `maxRegretOver_boundary_lt` / `isMinimaxRegret_iff_eq_left_boundary` and
  right-boundary mirrors — Theorem 4 (Bielous–Meir): for a non-winning proxy
  with peak weakly outside the winning interval, the near boundary of the
  median uncertainty is the unique minimax-regret report, via an exact
  reduction to the two-candidate regret game; realized constructively over
  point-mass information sets under follower majority
  (`isMinimaxRegret_constProfiles_iff_eq_left_boundary`).
* `not_dominatesOver_univ_of_truthful` — the section's opening claim: with
  no information at all, no report is a dominating manipulation at the
  truthful state (under follower majority and distinct peaks).
* `isMinimaxRegret_report_le_socialMedian` /
  `not_strongMonotoneOver_left_boundary` — the paper's conclusion that
  minimax-regret reports are strong-monotone holds in the weak same-side
  sense and fails in the strict sense: the unique minimax report sits
  exactly on the least consistent median.
* `rightBoundary_minimax_hypotheses_allow_no_fixed_factor_cut` and its left
  mirror — the minimax endpoint side conditions do not themselves imply any
  fixed-factor cut of the history interval; the convergence theorem
  states that premise explicitly as windowed contraction.
* `not_exists_rightBoundary_minimax_fixed_factor_cut` and its left mirror —
  packaged no-universal-factor forms of the same obstruction.
* `IsMinimaxRegretInfoDynamics` — active minimax-regret play relative to an
  explicit sequence of information sets; the counterexample file shows this
  still does not imply convergence without the contraction premise.
* `image_socialMedian_winnerInfoSet_eq_Ioo_of_neighbor_bounds` and endpoint
  variants — the single-observation median uncertainty interval, with
  midpoint ordering and endpoint closure determined by the proxy
  tie-break.
* `dominatesOver_left_side_set_eq_Ioo` /
  `dominatesOver_right_side_set_eq_Ioo` — the §5 open-interval
  domination formulas, stated as exact set equalities on the relevant side of
  the current winner.

For the winning proxy, the at-peak case is
`isMinimaxRegret_of_winner_at_peak`; away from the peak, winner-stay is not
minimax-regret when a runner-up sits strictly between the winner's reflected
peak and its report, since that runner-up makes vacating strictly better
(`winnerStay_not_isMinimaxRegret` in
`GameTheory.Mechanism.ProxyVoting.Counterexamples`).  The converse case
`isMinimaxRegret_winner_stay` holds: staying is minimax-regret provided no
other report lies strictly inside `(2p - w, 2u - w)` and some report sits
exactly at the reflected far boundary `2u - w`.  The paper's median-interval
structure `Iᵗ` is formalized semantically: for a single observation the
consistent medians are exactly the winner's delegate cell
(`image_socialMedian_winnerInfoSet`), and along a history-strong-monotone
play the uncertainty after `t` observations is exactly the intersection of
the observed winners' cells (`image_socialMedian_historyInfoSet`), an
interval, refining one observation at a time (`historyInfoSet_succ`).  History
refinement is by side preservation (`StrongMonotoneOver.report_le_socialMedian`),
not by intersecting with the half-line past the winner's new report (which can
exclude every consistent profile).

The worked example of the paper's Appendix B lives in
`GameTheory.Mechanism.ProxyVoting.AppendixB`.
-/

namespace GameTheory

namespace ProxyVoting

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]
variable {pp : P → ℝ} {s : P → ℝ} {q₀ : F → ℝ} {j : P} {r : ℝ}

/-- The winner-poll information set: follower profiles consistent with the
observed winner at the reported state. -/
def winnerInfoSet (s : P → ℝ) (jw : P) : Set (F → ℝ) := {q | winner s q = jw}

/-- The true follower profile is consistent with the observed winner. -/
theorem mem_winnerInfoSet_self (s : P → ℝ) (q : F → ℝ) :
    q ∈ winnerInfoSet (F := F) s (winner s q) := by
  simp only [winnerInfoSet, Set.mem_setOf_eq]

/-- Report `r` by proxy `j` dominates truthful play over a set of follower
profiles: weakly better against every profile in the set and strictly better
against at least one, under Euclidean preferences at `j`'s peak. -/
def DominatesOver (pp : P → ℝ) (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) :
    Prop :=
  (∀ q ∈ Q, |outcome (Function.update s j r) q - pp j| ≤ |outcome s q - pp j|)
    ∧ ∃ q ∈ Q, Prefers pp j (outcome (Function.update s j r) q) (outcome s q)

/-- A dominating manipulation for proxy `j` at the observed state `(s, jw)`,
with followers drawn from `F`: the report dominates truthful play over the
winner-poll information set. -/
def IsDominatingManipulation (F : Type*) [Fintype F]
    (pp : P → ℝ) (s : P → ℝ) (jw j : P) (r : ℝ) : Prop :=
  DominatesOver pp s (winnerInfoSet (F := F) s jw) j r

/-- A dominating manipulation never hurts: against the true follower profile —
which is always consistent with the observation — the outcome is weakly
better for the manipulator. -/
theorem IsDominatingManipulation.true_profile_le {q : F → ℝ}
    (h : IsDominatingManipulation F pp s (winner s q) j r) :
    |outcome (Function.update s j r) q - pp j| ≤ |outcome s q - pp j| :=
  h.1 q (mem_winnerInfoSet_self s q)

/-- Over a singleton information set — full information — domination is
exactly the Euclidean improvement at that profile. -/
theorem dominatesOver_singleton_iff :
    DominatesOver pp s {q₀} j r
      ↔ Prefers pp j (outcome (Function.update s j r) q₀) (outcome s q₀) := by
  constructor
  · rintro ⟨-, q, hq, hpref⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hpref
  · intro h
    refine ⟨fun q hq => ?_, q₀, Set.mem_singleton q₀, h⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact le_of_lt h

/-- With full information, a dominating manipulation is a better response. -/
theorem isBetterResponse_of_dominatesOver_singleton
    (h : DominatesOver pp s {q₀} j r) : IsBetterResponse pp q₀ s j r :=
  isBetterResponse_of_prefers (dominatesOver_singleton_iff.mp h)

/-- Report `r` by proxy `j` dominates truthful play over a set of follower
profiles under every single-peaked preference at `j`'s peak: the comparison
is forced weakly at every profile and forced strictly at some profile. -/
def SPDominatesOver (pp : P → ℝ) (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) :
    Prop :=
  (∀ q ∈ Q, SPWeaklyPrefers (pp j)
      (outcome (Function.update s j r) q) (outcome s q))
    ∧ ∃ q ∈ Q, SPPrefers (pp j)
        (outcome (Function.update s j r) q) (outcome s q)

/-- Forced dominance implies Euclidean dominance. -/
theorem SPDominatesOver.dominatesOver {Q : Set (F → ℝ)}
    (h : SPDominatesOver pp s Q j r) : DominatesOver pp s Q j r := by
  obtain ⟨hweak, q, hq, hstrict⟩ := h
  exact ⟨fun q' hq' => (hweak q' hq').abs_le, q, hq, hstrict.abs_lt⟩

/-- Over a singleton information set, forced dominance is exactly the forced
strict comparison at that profile. -/
theorem spDominatesOver_singleton_iff :
    SPDominatesOver pp s {q₀} j r
      ↔ SPPrefers (pp j) (outcome (Function.update s j r) q₀) (outcome s q₀) := by
  constructor
  · rintro ⟨-, q, hq, hpref⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hpref
  · intro h
    refine ⟨fun q hq => ?_, q₀, Set.mem_singleton q₀, h⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact h.spWeaklyPrefers

/-! ## Strong-monotone reports -/

/-- A report is strong-monotone over a set of follower profiles when it stays
on the same side of the population median as the proxy's current report, at
every profile in the set — strictly for current reports off the median,
exactly at the median for current reports at it, as in `MonotoneReport`. -/
def StrongMonotoneOver (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) : Prop :=
  ∀ q ∈ Q,
    (s j < socialMedian s q → r < socialMedian s q)
    ∧ (socialMedian s q < s j → socialMedian s q < r)
    ∧ (s j = socialMedian s q → r = socialMedian s q)

/-- A strong-monotone report keeps the population median unchanged at every
consistent profile: the unknown true median survives the move. -/
theorem socialMedian_update_eq_of_strongMonotoneOver {Q : Set (F → ℝ)}
    {q : F → ℝ} (h : StrongMonotoneOver s Q j r) (hq : q ∈ Q) :
    socialMedian (Function.update s j r) q = socialMedian s q := by
  obtain ⟨h1, h2, h3⟩ := h q hq
  rcases lt_trichotomy (s j) (socialMedian s q) with hlt | heq | hgt
  · exact socialMedian_update_eq_of_proxy_lt hlt (le_of_lt (h1 hlt))
  · rw [h3 heq, ← heq, Function.update_eq_self]
    exact heq.symm
  · exact socialMedian_update_eq_of_proxy_gt hgt (le_of_lt (h2 hgt))

/-- Weak non-crossing over an information set: a report that starts weakly on
one side of each consistent median remains weakly on that side.  When the
current report is exactly at a consistent median, both clauses apply and force
the new report to stay at that median. -/
def WeakStrongMonotoneOver (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) : Prop :=
  ∀ q ∈ Q,
    (s j ≤ socialMedian s q → r ≤ socialMedian s q)
      ∧ (socialMedian s q ≤ s j → socialMedian s q ≤ r)

omit [LinearOrder P] in
/-- Strict strong-monotonicity implies weak non-crossing. -/
theorem StrongMonotoneOver.weak {Q : Set (F → ℝ)}
    (h : StrongMonotoneOver s Q j r) :
    WeakStrongMonotoneOver s Q j r := by
  intro q hq
  obtain ⟨hleft, hright, heq⟩ := h q hq
  constructor
  · intro hs
    rcases lt_or_eq_of_le hs with hlt | heq'
    · exact le_of_lt (hleft hlt)
    · exact le_of_eq (heq heq')
  · intro hs
    rcases lt_or_eq_of_le hs with hlt | heq'
    · exact le_of_lt (hright hlt)
    · exact le_of_eq (heq heq'.symm).symm

/-- A weak non-crossing report keeps the population median unchanged at every
consistent profile.  The equality case is pinned because both weak clauses
fire, so the report cannot move away from a median it currently occupies. -/
theorem socialMedian_update_eq_of_weakStrongMonotoneOver {Q : Set (F → ℝ)}
    {q : F → ℝ} (h : WeakStrongMonotoneOver s Q j r) (hq : q ∈ Q) :
    socialMedian (Function.update s j r) q = socialMedian s q := by
  obtain ⟨hleft, hright⟩ := h q hq
  rcases lt_trichotomy (s j) (socialMedian s q) with hlt | heq | hgt
  · exact socialMedian_update_eq_of_proxy_lt hlt (hleft (le_of_lt hlt))
  · have hr : r = s j := by
      have hrle : r ≤ socialMedian s q := hleft (le_of_eq heq)
      have hle : socialMedian s q ≤ r := hright (le_of_eq heq.symm)
      exact (le_antisymm hrle hle).trans heq.symm
    rw [hr, Function.update_eq_self]
  · exact socialMedian_update_eq_of_proxy_gt hgt (hright (le_of_lt hgt))

omit [LinearOrder P] in
/-- With full information, at a state satisfying the monotone-dynamics
invariants, strong-monotone reports are exactly monotone reports: the sides
of the current report and of the peak agree. -/
theorem strongMonotoneOver_singleton_iff_monotoneReport
    (hside : SameSide pp q₀ s) (hmed : socialMedian s q₀ = socialMedian pp q₀) :
    StrongMonotoneOver s {q₀} j r ↔ MonotoneReport pp q₀ j r := by
  have hpeak_side : pp j < socialMedian pp q₀ ↔ s j < socialMedian pp q₀ := by
    constructor
    · intro hp
      exact (hside j).1 hp
    · intro hs
      rcases lt_trichotomy (pp j) (socialMedian pp q₀) with hp | hp | hp
      · exact hp
      · exact absurd ((hside j).2.2 hp) (ne_of_lt hs)
      · exact absurd ((hside j).2.1 hp) (not_lt.mpr (le_of_lt hs))
  have hpeak_side' : socialMedian pp q₀ < pp j ↔ socialMedian pp q₀ < s j := by
    constructor
    · intro hp
      exact (hside j).2.1 hp
    · intro hs
      rcases lt_trichotomy (pp j) (socialMedian pp q₀) with hp | hp | hp
      · exact absurd ((hside j).1 hp) (not_lt.mpr (le_of_lt hs))
      · exact absurd ((hside j).2.2 hp) (ne_of_gt hs)
      · exact hp
  have hpeak_eq : pp j = socialMedian pp q₀ ↔ s j = socialMedian pp q₀ := by
    constructor
    · intro hp
      exact (hside j).2.2 hp
    · intro hs
      rcases lt_trichotomy (pp j) (socialMedian pp q₀) with hp | hp | hp
      · exact absurd hs (ne_of_lt ((hside j).1 hp))
      · exact hp
      · exact absurd hs (ne_of_gt ((hside j).2.1 hp))
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h q₀ (Set.mem_singleton q₀)
    rw [hmed] at h1 h2 h3
    exact ⟨fun hp => h1 (hpeak_side.mp hp), fun hp => h2 (hpeak_side'.mp hp),
      fun hp => h3 (hpeak_eq.mp hp)⟩
  · intro h q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    rw [hmed]
    exact ⟨fun hs => h.1 (hpeak_side.mpr hs), fun hs => h.2.1 (hpeak_side'.mpr hs),
      fun hs => h.2.2 (hpeak_eq.mpr hs)⟩

/-- A strong-monotone dynamics: at each step some proxy moves by a report
that is strong-monotone over the winner-poll information set of the current
observation, or the state rests.  Only the monotonicity structure is
captured; dominance of the chosen reports is an orthogonal condition. -/
def IsStrongMonotoneDynamics (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  ∀ t, (∃ j r, StrongMonotoneOver (σ t)
        (winnerInfoSet (F := F) (σ t) (winner (σ t) q)) j r
      ∧ σ (t + 1) = Function.update (σ t) j r)
    ∨ σ (t + 1) = σ t

/-- A weak non-crossing dynamics: at each step the moving report is weakly
non-crossing over the winner-poll information set of the current observation,
or the state rests.  This is the right monotonicity notion for boundary
minimax-regret reports, which may land exactly on the least or greatest
consistent median. -/
def IsWeakStrongMonotoneDynamics (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  ∀ t, (∃ j r, WeakStrongMonotoneOver (σ t)
        (winnerInfoSet (F := F) (σ t) (winner (σ t) q)) j r
      ∧ σ (t + 1) = Function.update (σ t) j r)
    ∨ σ (t + 1) = σ t

/-- Strict strong-monotone dynamics are weak non-crossing dynamics. -/
theorem IsStrongMonotoneDynamics.weak {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsStrongMonotoneDynamics q σ) :
    IsWeakStrongMonotoneDynamics q σ := by
  intro t
  rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
  · exact Or.inl ⟨j, r, hsm.weak, hupd⟩
  · exact Or.inr hrest

/-- Along a strong-monotone dynamics the population median at the true
follower profile never moves, even though the proxies never observe it: the
true profile is always consistent with the published observation. -/
theorem socialMedian_eq_of_isStrongMonotoneDynamics {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsStrongMonotoneDynamics q σ) (t : ℕ) :
    socialMedian (σ t) q = socialMedian (σ 0) q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
    · rw [hupd, socialMedian_update_eq_of_strongMonotoneOver hsm
        (mem_winnerInfoSet_self (σ t) q), ih]
    · rw [hrest, ih]

/-- Along a weak non-crossing dynamics the population median at the true
follower profile never moves. -/
theorem socialMedian_eq_of_isWeakStrongMonotoneDynamics {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsWeakStrongMonotoneDynamics q σ) (t : ℕ) :
    socialMedian (σ t) q = socialMedian (σ 0) q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
    · rw [hupd, socialMedian_update_eq_of_weakStrongMonotoneOver hsm
        (mem_winnerInfoSet_self (σ t) q), ih]
    · rw [hrest, ih]

/-- **Lemma 3 under partial information**, weak form: a strong-monotone
report by a proxy other than the current winner never increases the
outcome's distance to the population median at any consistent profile. -/
theorem strongMonotoneStep_dist_le {Q : Set (F → ℝ)} {q : F → ℝ}
    (h : StrongMonotoneOver s Q j r) (hq : q ∈ Q) (hj : j ≠ winner s q) :
    |outcome (Function.update s j r) q - socialMedian s q|
      ≤ |outcome s q - socialMedian s q| := by
  have hmed := socialMedian_update_eq_of_strongMonotoneOver h hq
  have hd := abs_outcome_sub_socialMedian_le (Function.update s j r) q (winner s q)
  rw [hmed] at hd
  have hsw : Function.update s j r (winner s q) = outcome s q := by
    rw [Function.update_apply, if_neg (fun hh => hj hh.symm)]
    rfl
  rw [hsw] at hd
  exact hd

/-- Along a strong-monotone dynamics the outcome is at least as close to the
initial population median as every current report; combined with the
windowed-contraction machinery this yields convergence to the initial median.
This estimate is a bound used by the convergence theorem, not a
source of the theorem's fixed-factor contraction premise. -/
theorem abs_outcome_sub_le_of_isStrongMonotoneDynamics {q : F → ℝ}
    {σ : ℕ → P → ℝ} (h : IsStrongMonotoneDynamics q σ) (t : ℕ) (k : P) :
    |outcome (σ t) q - socialMedian (σ 0) q|
      ≤ |σ t k - socialMedian (σ 0) q| := by
  have hd := abs_outcome_sub_socialMedian_le (σ t) q k
  rw [socialMedian_eq_of_isStrongMonotoneDynamics h t] at hd
  exact hd

/-- Weak non-crossing version of
`abs_outcome_sub_le_of_isStrongMonotoneDynamics`. -/
theorem abs_outcome_sub_le_of_isWeakStrongMonotoneDynamics {q : F → ℝ}
    {σ : ℕ → P → ℝ} (h : IsWeakStrongMonotoneDynamics q σ) (t : ℕ) (k : P) :
    |outcome (σ t) q - socialMedian (σ 0) q|
      ≤ |σ t k - socialMedian (σ 0) q| := by
  have hd := abs_outcome_sub_socialMedian_le (σ t) q k
  rw [socialMedian_eq_of_isWeakStrongMonotoneDynamics h t] at hd
  exact hd

/-- Partial-information convergence theorem.  Weak non-crossing
alone preserves the true population median but does not force convergence;
the same windowed-contraction hypothesis used in the complete-information
theorem does.  The hypotheses are stated against the current median, and weak
median invariance rewrites them to the initial median consumed by
`tendsto_outcome_of_windowed_contraction`. -/
theorem tendsto_outcome_of_weakStrongMonotone_windowed_contraction
    {q : F → ℝ} {σ : ℕ → P → ℝ} {b : ℕ → ℕ} {α : ℝ}
    (h : IsWeakStrongMonotoneDynamics q σ)
    (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hwindow : ∀ k u, b k ≤ u → u ≤ b (k + 1) →
      |outcome (σ u) q - socialMedian (σ u) q|
        ≤ |outcome (σ (b k)) q - socialMedian (σ (b k)) q|)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbig : ∀ k, ∃ k', k ≤ k' ∧
      |outcome (σ (b (k' + 1))) q - socialMedian (σ (b (k' + 1))) q|
        ≤ α * |outcome (σ (b k')) q - socialMedian (σ (b k')) q|) :
    Filter.Tendsto (fun t => outcome (σ t) q) Filter.atTop
      (nhds (socialMedian (σ 0) q)) := by
  refine tendsto_outcome_of_windowed_contraction
    (pp := σ 0) (q := q) (σ := σ) (b := b) (α := α)
    hb0 hbmono htop ?_ hα0 hα1 ?_
  · intro k u hku huk
    simpa [socialMedian_eq_of_isWeakStrongMonotoneDynamics h u,
      socialMedian_eq_of_isWeakStrongMonotoneDynamics h (b k)]
      using hwindow k u hku huk
  · intro k
    obtain ⟨k', hkk', hstep⟩ := hbig k
    refine ⟨k', hkk', ?_⟩
    simpa [socialMedian_eq_of_isWeakStrongMonotoneDynamics h (b (k' + 1)),
      socialMedian_eq_of_isWeakStrongMonotoneDynamics h (b k')]
      using hstep

/-! ## Regret

Regret compares the achieved Euclidean distance with the best distance
achievable ex post.  The ex-post benchmark is expressed as an infimum over
reports, and maximal regret over an information set is expressed as a supremum
over consistent follower profiles. -/

/-- The best Euclidean outcome distance proxy `j` can achieve ex post at
profile `q`. -/
noncomputable def bestOutcomeDist (pp : P → ℝ) (s : P → ℝ) (j : P) (q : F → ℝ) :
    ℝ :=
  ⨅ y : ℝ, |outcome (Function.update s j y) q - pp j|

theorem bestOutcomeDist_nonneg {q : F → ℝ} : 0 ≤ bestOutcomeDist pp s j q :=
  le_ciInf fun _ => abs_nonneg _

theorem bestOutcomeDist_le {q : F → ℝ} (r : ℝ) :
    bestOutcomeDist pp s j q ≤ |outcome (Function.update s j r) q - pp j| :=
  ciInf_le ⟨0, by rintro x ⟨y, rfl⟩; exact abs_nonneg _⟩ r

/-- The regret of report `r` at profile `q`: the achieved distance in excess
of the best achievable one. -/
noncomputable def regret (pp : P → ℝ) (s : P → ℝ) (j : P) (r : ℝ) (q : F → ℝ) :
    ℝ :=
  |outcome (Function.update s j r) q - pp j| - bestOutcomeDist pp s j q

theorem regret_nonneg {q : F → ℝ} : 0 ≤ regret pp s j r q :=
  sub_nonneg.mpr (bestOutcomeDist_le r)

theorem regret_le_abs {q : F → ℝ} :
    regret pp s j r q ≤ |outcome (Function.update s j r) q - pp j| := by
  have h := bestOutcomeDist_nonneg (pp := pp) (s := s) (j := j) (q := q)
  unfold regret
  linarith

/-- The maximal regret of report `r` over a set of follower profiles. -/
noncomputable def maxRegretOver (pp : P → ℝ) (s : P → ℝ) (j : P) (r : ℝ)
    (Q : Set (F → ℝ)) : ℝ :=
  sSup ((fun q => regret pp s j r q) '' Q)

/-- Regrets over any profile set are bounded above by the largest report
distance: the outcome is always a report. -/
theorem bddAbove_regret_image (Q : Set (F → ℝ)) :
    BddAbove ((fun q => regret pp s j r q) '' Q) := by
  refine ⟨Finset.univ.sup' Finset.univ_nonempty
    (fun k => |Function.update s j r k - pp j|), ?_⟩
  rintro x ⟨q, -, rfl⟩
  calc regret pp s j r q
      ≤ |outcome (Function.update s j r) q - pp j| := regret_le_abs
    _ ≤ _ := Finset.le_sup'
        (fun k => |Function.update s j r k - pp j|)
        (Finset.mem_univ (winner (Function.update s j r) q))

theorem maxRegretOver_nonneg (Q : Set (F → ℝ)) :
    0 ≤ maxRegretOver pp s j r Q := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨q, -, rfl⟩
  exact regret_nonneg

theorem regret_le_maxRegretOver {Q : Set (F → ℝ)} {q : F → ℝ} (hq : q ∈ Q) :
    regret pp s j r q ≤ maxRegretOver pp s j r Q :=
  le_csSup (bddAbove_regret_image Q) ⟨q, hq, rfl⟩

theorem maxRegretOver_le {Q : Set (F → ℝ)} {c : ℝ} (hQ : Q.Nonempty)
    (h : ∀ q ∈ Q, regret pp s j r q ≤ c) :
    maxRegretOver pp s j r Q ≤ c := by
  refine csSup_le (hQ.image _) ?_
  rintro x ⟨q, hq, rfl⟩
  exact h q hq

/-- A minimax-regret report: no report has smaller maximal regret over the
profile set. -/
def IsMinimaxRegret (pp : P → ℝ) (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) :
    Prop :=
  ∀ r', maxRegretOver pp s j r Q ≤ maxRegretOver pp s j r' Q

/-- The observed winner reporting at its peak has zero maximal regret over
the winner-poll information set — staying wins at every consistent profile —
and is therefore minimax-regret. -/
theorem isMinimaxRegret_of_winner_at_peak {s : P → ℝ} {q : F → ℝ}
    (hw : s (winner s q) = pp (winner s q)) :
    maxRegretOver pp s (winner s q) (s (winner s q))
        (winnerInfoSet (F := F) s (winner s q)) = 0
      ∧ IsMinimaxRegret pp s (winnerInfoSet (F := F) s (winner s q))
          (winner s q) (s (winner s q)) := by
  have hzero : ∀ q' ∈ winnerInfoSet (F := F) s (winner s q),
      regret pp s (winner s q) (s (winner s q)) q' = 0 := by
    intro q' hq'
    have hupd : Function.update s (winner s q) (s (winner s q)) = s :=
      Function.update_eq_self _ _
    have hach : |outcome (Function.update s (winner s q) (s (winner s q))) q'
        - pp (winner s q)| = 0 := by
      rw [hupd]
      have hout : outcome s q' = s (winner s q) := by
        have hwq' : winner s q' = winner s q := hq'
        rw [outcome, hwq']
      rw [hout, hw, sub_self, abs_zero]
    refine le_antisymm ?_ regret_nonneg
    unfold regret
    rw [hach]
    have h := bestOutcomeDist_nonneg (pp := pp) (s := s) (j := winner s q) (q := q')
    linarith
  have hmax : maxRegretOver pp s (winner s q) (s (winner s q))
      (winnerInfoSet (F := F) s (winner s q)) = 0 := by
    refine le_antisymm ?_ (maxRegretOver_nonneg _)
    refine maxRegretOver_le ⟨q, mem_winnerInfoSet_self s q⟩ ?_
    intro q' hq'
    rw [hzero q' hq']
  exact ⟨hmax, fun r' => hmax ▸ maxRegretOver_nonneg _⟩

/-! ## The two-candidate regret game

The regret analysis of the paper's Theorem 4 takes place in a reduced game:
a proxy with peak `p` challenges the standing winner at position `w`, nature
holds the median `μ` uncertain over an interval, and the challenger's report
wins exactly when strictly nearer the median.  The theorems below are the
paper's computation with its implicit hypotheses made explicit: the peak
lies weakly outside the winning interval at the near boundary, and the
uncertainty reaches the midpoint between the near boundary and the winner.
Under these, the near boundary is the unique minimax-regret report — in
particular it stays weakly on the near side of every possible median. -/

/-- The two-candidate outcome: the challenger's report `x` beats the
standing winner `w` exactly when strictly nearer the median `μ`. -/
noncomputable def duelOutcome (w x μ : ℝ) : ℝ :=
  if |x - μ| < |w - μ| then x else w

theorem duelOutcome_of_lt {w x μ : ℝ} (h : |x - μ| < |w - μ|) :
    duelOutcome w x μ = x := by
  unfold duelOutcome
  exact if_pos h

theorem duelOutcome_of_ge {w x μ : ℝ} (h : |w - μ| ≤ |x - μ|) :
    duelOutcome w x μ = w := by
  unfold duelOutcome
  exact if_neg (not_lt.mpr h)

/-- The best ex-post distance in the two-candidate game. -/
noncomputable def duelBestDist (p w μ : ℝ) : ℝ :=
  ⨅ y : ℝ, |duelOutcome w y μ - p|

/-- Regret in the two-candidate game. -/
noncomputable def duelRegret (p w x μ : ℝ) : ℝ :=
  |duelOutcome w x μ - p| - duelBestDist p w μ

/-- Maximal regret over the median uncertainty. -/
noncomputable def duelMaxRegret (p w x : ℝ) (M : Set ℝ) : ℝ :=
  sSup (duelRegret p w x '' M)

private theorem bddBelow_duel (p w μ : ℝ) :
    BddBelow (Set.range fun y => |duelOutcome w y μ - p|) := by
  refine ⟨0, ?_⟩
  rintro v ⟨y, rfl⟩
  exact abs_nonneg _

/-- The ex-post best distance in closed form: the distance from the peak to
the closure of the winning interval around the median — whose boundary
carries the standing winner. -/
theorem duelBestDist_eq (p w μ : ℝ) :
    duelBestDist p w μ = max (|p - μ| - |w - μ|) 0 := by
  refine le_antisymm ?_ ?_
  · -- Approach the boundary of the winning interval.
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases eq_or_lt_of_le (abs_nonneg (w - μ)) with hd | hd
    · -- Degenerate winner at the median: nothing ever wins.
      refine ciInf_le_of_le (bddBelow_duel p w μ) w ?_
      have hout : duelOutcome w w μ = w := duelOutcome_of_ge le_rfl
      have hwμ : w = μ := by
        have h := abs_eq_zero.mp hd.symm
        linarith
      have hval : |w - p| = |p - μ| - |w - μ| := by
        rw [← hd, hwμ, abs_sub_comm]
        ring
      rw [hout, hval]
      have h := le_max_left (|p - μ| - |w - μ|) (0 : ℝ)
      linarith
    · rcases lt_or_ge (|p - μ|) (|w - μ|) with hin | hout
      · -- The peak itself wins: zero distance.
        refine ciInf_le_of_le (bddBelow_duel p w μ) p ?_
        rw [duelOutcome_of_lt hin, sub_self, abs_zero,
          max_eq_right (by linarith)]
        linarith
      · -- Nudge just inside the winning interval on the peak's side.
        have hδpos : 0 < min ε (|w - μ|) / 2 := by positivity
        have hδlt : min ε (|w - μ|) / 2 < |w - μ| := by
          have h := min_le_right ε (|w - μ|)
          linarith
        have hδε : min ε (|w - μ|) / 2 < ε := by
          have h := min_le_left ε (|w - μ|)
          linarith
        rcases le_or_gt μ p with hside | hside
        · have hpm : |p - μ| = p - μ := abs_of_nonneg (by linarith)
          rw [hpm] at hout
          refine ciInf_le_of_le (bddBelow_duel p w μ)
            (μ + (|w - μ| - min ε (|w - μ|) / 2)) ?_
          have hwin : duelOutcome w (μ + (|w - μ| - min ε (|w - μ|) / 2)) μ
              = μ + (|w - μ| - min ε (|w - μ|) / 2) := by
            refine duelOutcome_of_lt ?_
            rw [add_sub_cancel_left, abs_of_nonneg (by linarith)]
            linarith
          rw [hwin, hpm]
          have hmax := le_max_left (p - μ - |w - μ|) (0 : ℝ)
          rcases le_or_gt (μ + (|w - μ| - min ε (|w - μ|) / 2)) p with hle | hgt
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · rw [abs_of_pos (by linarith)]
            linarith
        · have hpm : |p - μ| = μ - p := by
            rw [abs_of_nonpos (by linarith)]
            ring
          rw [hpm] at hout
          refine ciInf_le_of_le (bddBelow_duel p w μ)
            (μ - (|w - μ| - min ε (|w - μ|) / 2)) ?_
          have hwin : duelOutcome w (μ - (|w - μ| - min ε (|w - μ|) / 2)) μ
              = μ - (|w - μ| - min ε (|w - μ|) / 2) := by
            refine duelOutcome_of_lt ?_
            have h : μ - (|w - μ| - min ε (|w - μ|) / 2) - μ
                = -(|w - μ| - min ε (|w - μ|) / 2) := by ring
            rw [h, abs_neg, abs_of_nonneg (by linarith)]
            linarith
          rw [hwin, hpm]
          have hmax := le_max_left (μ - p - |w - μ|) (0 : ℝ)
          rw [abs_of_pos (by linarith)]
          linarith
  · -- The closed form is a genuine lower bound, by the triangle inequality.
    refine le_ciInf fun y => ?_
    refine max_le ?_ (abs_nonneg _)
    unfold duelOutcome
    split
    · rename_i hwin
      have h := abs_sub_le p y μ
      rw [abs_sub_comm y p]
      linarith
    · have h := abs_sub_le p w μ
      rw [abs_sub_comm w p]
      linarith

theorem duelBestDist_nonneg (p w μ : ℝ) : 0 ≤ duelBestDist p w μ :=
  le_ciInf fun _ => abs_nonneg _

theorem duelRegret_nonneg (p w x μ : ℝ) : 0 ≤ duelRegret p w x μ :=
  sub_nonneg.mpr (ciInf_le (bddBelow_duel p w μ) x)

private theorem bddAbove_duelRegret_image (p w x : ℝ) (M : Set ℝ) :
    BddAbove (duelRegret p w x '' M) := by
  refine ⟨max |x - p| |w - p|, ?_⟩
  rintro v ⟨μ, -, rfl⟩
  have h := duelBestDist_nonneg p w μ
  unfold duelRegret duelOutcome
  split
  · have hb := le_max_left |x - p| |w - p|
    linarith
  · have hb := le_max_right |x - p| |w - p|
    linarith

theorem duelRegret_le_duelMaxRegret {p w x : ℝ} {M : Set ℝ} {μ : ℝ}
    (hμ : μ ∈ M) : duelRegret p w x μ ≤ duelMaxRegret p w x M :=
  le_csSup (bddAbove_duelRegret_image p w x M) ⟨μ, hμ, rfl⟩

theorem duelMaxRegret_le {p w x c : ℝ} {M : Set ℝ} (hM : M.Nonempty)
    (h : ∀ μ ∈ M, duelRegret p w x μ ≤ c) :
    duelMaxRegret p w x M ≤ c := by
  refine csSup_le (hM.image _) ?_
  rintro v ⟨μ, hμ, rfl⟩
  exact h μ hμ

/-- The near boundary's maximal regret is at most the boundary-winner gap:
winning at the boundary median costs at most the reflection defect, and
losing costs at most twice the distance from the median to the winner. -/
theorem duelMaxRegret_left_boundary_le {p ℓ w u : ℝ}
    (hp : p ≤ 2 * ℓ - w) (hlw : ℓ < w) (hu : (ℓ + w) / 2 ≤ u) :
    duelMaxRegret p w ℓ (Set.Icc ℓ u) ≤ w - ℓ := by
  have hlu : ℓ ≤ u := le_trans (by linarith) hu
  have hpℓ : p < ℓ := by linarith
  refine duelMaxRegret_le (Set.nonempty_Icc.mpr hlu) fun μ hμ => ?_
  obtain ⟨hℓμ, hμu⟩ := hμ
  have hpμ : |p - μ| = μ - p := by
    rw [abs_of_nonpos (by linarith)]
    ring
  unfold duelRegret
  rw [duelBestDist_eq, hpμ]
  rcases lt_or_ge μ ((ℓ + w) / 2) with hmid | hmid
  · -- The boundary report wins.
    have hwμ : |w - μ| = w - μ := abs_of_pos (by linarith)
    have hwin : duelOutcome w ℓ μ = ℓ := by
      refine duelOutcome_of_lt ?_
      rw [hwμ, abs_of_nonpos (by linarith)]
      linarith
    rw [hwin, hwμ, abs_of_pos (by linarith), max_eq_left (by linarith)]
    linarith
  · -- The winner survives.
    rcases le_or_gt w μ with hwμ | hwμ
    · have hwμ' : |w - μ| = μ - w := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have hlose : duelOutcome w ℓ μ = w := by
        refine duelOutcome_of_ge ?_
        rw [hwμ', abs_of_nonpos (by linarith)]
        linarith
      rw [hlose, hwμ', abs_of_pos (by linarith), max_eq_left (by linarith)]
      linarith
    · have hwμ' : |w - μ| = w - μ := abs_of_pos (by linarith)
      have hlose : duelOutcome w ℓ μ = w := by
        refine duelOutcome_of_ge ?_
        rw [hwμ', abs_of_nonpos (by linarith)]
        linarith
      rw [hlose, hwμ', abs_of_pos (by linarith), max_eq_left (by linarith)]
      linarith

/-- **Witness form of the minimax comparison.**  Every report other than the
near boundary admits a consistent median at which its two-candidate regret
strictly exceeds the boundary report's maximal regret — and the witness can
be chosen free of mirror ties, or with the report exactly on the winning
position, which is what the reduction to the full game requires.  The one
subtle case is the exact reflection `x = 2ℓ - w` of the winner across the
boundary, where the natural witness `μ = ℓ` is itself a mirror tie; a median
a quarter-gap inside still extracts regret `3(w - ℓ)/2`. -/
theorem exists_duelRegret_witness_gt {p ℓ w u : ℝ}
    (hp : p ≤ 2 * ℓ - w) (hlw : ℓ < w) (hu : (ℓ + w) / 2 ≤ u)
    {x : ℝ} (hx : x ≠ ℓ) :
    ∃ μ ∈ Set.Icc ℓ u, (|x - μ| ≠ |w - μ| ∨ x = w) ∧
      duelMaxRegret p w ℓ (Set.Icc ℓ u) < duelRegret p w x μ := by
  have hlu : ℓ ≤ u := le_trans (by linarith) hu
  have hpℓ : p < ℓ := by linarith
  have hbound := duelMaxRegret_left_boundary_le hp hlw hu
  have hℓmem : ℓ ∈ Set.Icc ℓ u := Set.mem_Icc.mpr ⟨le_refl ℓ, hlu⟩
  have hwℓ : |w - ℓ| = w - ℓ := abs_of_pos (by linarith)
  have hpℓ' : |p - ℓ| = ℓ - p := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rcases lt_trichotomy x ℓ with hxl | hxl | hxl
  · rcases lt_trichotomy x (2 * ℓ - w) with hfar | heq | hnear
    · -- Strictly beyond the reflection: losing at the boundary median is
      -- tie-free and costs twice the gap.
      refine ⟨ℓ, hℓmem, Or.inl ?_, lt_of_le_of_lt hbound ?_⟩
      · rw [hwℓ, abs_of_nonpos (by linarith)]
        intro h
        linarith
      · have hlose : duelOutcome w x ℓ = w := by
          refine duelOutcome_of_ge ?_
          rw [hwℓ, abs_of_nonpos (by linarith)]
          linarith
        unfold duelRegret
        rw [duelBestDist_eq, hlose, hwℓ, hpℓ', abs_of_pos (by linarith),
          max_eq_left (by linarith)]
        linarith
    · -- Exactly the reflection: the boundary median is a mirror tie, so move
      -- a quarter-gap inside.
      refine ⟨ℓ + (w - ℓ) / 4,
        Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, Or.inl ?_,
        lt_of_le_of_lt hbound ?_⟩
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        intro h
        linarith
      · have hlose : duelOutcome w x (ℓ + (w - ℓ) / 4) = w := by
          refine duelOutcome_of_ge ?_
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        unfold duelRegret
        rw [duelBestDist_eq, hlose,
          abs_of_pos (show (0:ℝ) < w - p by linarith),
          abs_of_nonpos (show p - (ℓ + (w - ℓ) / 4) ≤ 0 by linarith),
          abs_of_nonneg (show (0:ℝ) ≤ w - (ℓ + (w - ℓ) / 4) by linarith),
          max_eq_left (by linarith)]
        linarith
    · -- Just inside on the far side: a median just past the report-winner
      -- midpoint defeats the report tie-free.
      have hμ₀l : ℓ < (x + w) / 2 + (ℓ - x) / 4 := by linarith
      have hμ₀u : (x + w) / 2 + (ℓ - x) / 4 ≤ u := by linarith
      have hμ₀w : (x + w) / 2 + (ℓ - x) / 4 < w := by linarith
      refine ⟨(x + w) / 2 + (ℓ - x) / 4,
        Set.mem_Icc.mpr ⟨le_of_lt hμ₀l, hμ₀u⟩, Or.inl ?_,
        lt_of_le_of_lt hbound ?_⟩
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        intro h
        linarith
      · have hlose : duelOutcome w x ((x + w) / 2 + (ℓ - x) / 4) = w := by
          refine duelOutcome_of_ge ?_
          rw [abs_of_pos (by linarith), abs_of_nonpos (by linarith)]
          linarith
        unfold duelRegret
        rw [duelBestDist_eq, hlose, abs_of_pos (by linarith),
          abs_of_nonpos (by linarith), abs_of_pos (by linarith),
          max_eq_left (by linarith)]
        linarith
  · exact absurd hxl hx
  · rcases lt_trichotomy x w with hxw | hxw | hxw
    · -- Between the boundary and the winner: winning at the boundary median
      -- overshoots the reflection strictly, tie-free.
      refine ⟨ℓ, hℓmem, Or.inl ?_, lt_of_le_of_lt hbound ?_⟩
      · rw [hwℓ, abs_of_nonneg (by linarith)]
        intro h
        linarith
      · have hwin : duelOutcome w x ℓ = x := by
          refine duelOutcome_of_lt ?_
          rw [hwℓ, abs_of_nonneg (by linarith)]
          linarith
        unfold duelRegret
        rw [duelBestDist_eq, hwin, hwℓ, hpℓ', abs_of_pos (by linarith),
          max_eq_left (by linarith)]
        linarith
    · -- Exactly the winning position: a tie in distance but a coincidence in
      -- position, certified by the right disjunct.
      refine ⟨ℓ, hℓmem, Or.inr hxw, lt_of_le_of_lt hbound ?_⟩
      have hlose : duelOutcome w x ℓ = w := by
        rw [hxw]
        exact duelOutcome_of_ge le_rfl
      unfold duelRegret
      rw [duelBestDist_eq, hlose, hwℓ, hpℓ', abs_of_pos (by linarith),
        max_eq_left (by linarith)]
      linarith
    · -- Beyond the winner: losing at the boundary median, tie-free.
      refine ⟨ℓ, hℓmem, Or.inl ?_, lt_of_le_of_lt hbound ?_⟩
      · rw [hwℓ, abs_of_nonneg (by linarith)]
        intro h
        linarith
      · have hlose : duelOutcome w x ℓ = w := by
          refine duelOutcome_of_ge ?_
          rw [hwℓ, abs_of_nonneg (by linarith)]
          linarith
        unfold duelRegret
        rw [duelBestDist_eq, hlose, hwℓ, hpℓ', abs_of_pos (by linarith),
          max_eq_left (by linarith)]
        linarith

/-- **The two-candidate minimax core of Theorem 4** (Bielous-Meir).  With the
peak weakly outside the winning interval at the near boundary and the median
uncertainty reaching the boundary-winner midpoint, the near boundary is the
unique minimax-regret report: every other report incurs strictly more
maximal regret than the boundary-winner gap. -/
theorem duelMaxRegret_left_boundary_lt {p ℓ w u : ℝ}
    (hp : p ≤ 2 * ℓ - w) (hlw : ℓ < w) (hu : (ℓ + w) / 2 ≤ u)
    {x : ℝ} (hx : x ≠ ℓ) :
    duelMaxRegret p w ℓ (Set.Icc ℓ u) < duelMaxRegret p w x (Set.Icc ℓ u) := by
  obtain ⟨μ, hμ, -, h⟩ := exists_duelRegret_witness_gt hp hlw hu hx
  exact lt_of_lt_of_le h (duelRegret_le_duelMaxRegret hμ)

/-! ### Reflection

The two-candidate game has no tie-breaking, so it is symmetric under
negation, and the right-boundary results follow from the left ones by
reflection. -/

theorem duelOutcome_neg (w x μ : ℝ) :
    duelOutcome (-w) (-x) (-μ) = -duelOutcome w x μ := by
  unfold duelOutcome
  have h1 : |(-x) - (-μ)| = |x - μ| := by
    rw [show (-x) - (-μ) = -(x - μ) by ring, abs_neg]
  have h2 : |(-w) - (-μ)| = |w - μ| := by
    rw [show (-w) - (-μ) = -(w - μ) by ring, abs_neg]
  rw [h1, h2]
  split_ifs <;> rfl

theorem duelBestDist_neg (p w μ : ℝ) :
    duelBestDist (-p) (-w) (-μ) = duelBestDist p w μ := by
  rw [duelBestDist_eq, duelBestDist_eq]
  have h1 : |(-p) - (-μ)| = |p - μ| := by
    rw [show (-p) - (-μ) = -(p - μ) by ring, abs_neg]
  have h2 : |(-w) - (-μ)| = |w - μ| := by
    rw [show (-w) - (-μ) = -(w - μ) by ring, abs_neg]
  rw [h1, h2]

theorem duelRegret_neg (p w x μ : ℝ) :
    duelRegret (-p) (-w) (-x) (-μ) = duelRegret p w x μ := by
  unfold duelRegret
  rw [duelOutcome_neg, duelBestDist_neg]
  congr 1
  rw [show -duelOutcome w x μ - -p = -(duelOutcome w x μ - p) by ring, abs_neg]

theorem duelMaxRegret_neg (p w x : ℝ) (M : Set ℝ) :
    duelMaxRegret (-p) (-w) (-x) (-M) = duelMaxRegret p w x M := by
  unfold duelMaxRegret
  congr 1
  ext v
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨-μ, Set.mem_neg.mp hμ, ?_⟩
    rw [← duelRegret_neg p w x (-μ), neg_neg]
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨-μ, ?_, duelRegret_neg p w x μ⟩
    rw [Set.mem_neg, neg_neg]
    exact hμ

/-- Mirror of `duelMaxRegret_left_boundary_le` at the right boundary. -/
theorem duelMaxRegret_right_boundary_le {p ℓ w u : ℝ}
    (hp : 2 * u - w ≤ p) (hwu : w < u) (hl : ℓ ≤ (u + w) / 2) :
    duelMaxRegret p w u (Set.Icc ℓ u) ≤ u - w := by
  have h := duelMaxRegret_left_boundary_le (p := -p) (ℓ := -u) (w := -w)
    (u := -ℓ) (by linarith) (by linarith) (by linarith)
  have h2 : duelMaxRegret p w u (Set.Icc ℓ u) ≤ -w - -u := by
    rw [← duelMaxRegret_neg p w u (Set.Icc ℓ u),
      show -Set.Icc ℓ u = Set.Icc (-u) (-ℓ) from Set.neg_Icc ℓ u]
    exact h
  linarith

/-- Mirror of `duelMaxRegret_left_boundary_lt` at the right boundary: with
the peak weakly outside the winning interval at the right boundary and the
uncertainty reaching the boundary-winner midpoint, the right boundary is the
unique minimax-regret report. -/
theorem duelMaxRegret_right_boundary_lt {p ℓ w u : ℝ}
    (hp : 2 * u - w ≤ p) (hwu : w < u) (hl : ℓ ≤ (u + w) / 2)
    {x : ℝ} (hx : x ≠ u) :
    duelMaxRegret p w u (Set.Icc ℓ u) < duelMaxRegret p w x (Set.Icc ℓ u) := by
  have h := duelMaxRegret_left_boundary_lt (p := -p) (ℓ := -u) (w := -w)
    (u := -ℓ) (by linarith) (by linarith) (by linarith)
    (x := -x) (fun hc => hx (neg_injective hc))
  rw [← duelMaxRegret_neg p w u (Set.Icc ℓ u),
    ← duelMaxRegret_neg p w x (Set.Icc ℓ u),
    show -Set.Icc ℓ u = Set.Icc (-u) (-ℓ) from Set.neg_Icc ℓ u]
  exact h

/-- Mirror of `exists_duelRegret_witness_gt` at the right boundary: the
certified witness median transports through the reflection. -/
theorem exists_duelRegret_witness_gt_right {p ℓ w u : ℝ}
    (hp : 2 * u - w ≤ p) (hwu : w < u) (hl : ℓ ≤ (u + w) / 2)
    {x : ℝ} (hx : x ≠ u) :
    ∃ μ ∈ Set.Icc ℓ u, (|x - μ| ≠ |w - μ| ∨ x = w) ∧
      duelMaxRegret p w u (Set.Icc ℓ u) < duelRegret p w x μ := by
  obtain ⟨μ', hμ', hcert', hgt'⟩ := exists_duelRegret_witness_gt
    (p := -p) (ℓ := -u) (w := -w) (u := -ℓ) (by linarith) (by linarith)
    (by linarith) (x := -x) (fun hc => hx (neg_injective hc))
  refine ⟨-μ', ?_, ?_, ?_⟩
  · rw [Set.mem_Icc] at hμ' ⊢
    exact ⟨by linarith [hμ'.2], by linarith [hμ'.1]⟩
  · rcases hcert' with h | h
    · left
      have e1 : |(-x) - μ'| = |x - (-μ')| := by
        rw [show (-x) - μ' = -(x - (-μ')) by ring, abs_neg]
      have e2 : |(-w) - μ'| = |w - (-μ')| := by
        rw [show (-w) - μ' = -(w - (-μ')) by ring, abs_neg]
      rw [e1, e2] at h
      exact h
    · right
      exact neg_injective h
  · have hreg := duelRegret_neg p w x (-μ')
    rw [neg_neg] at hreg
    have hmax : duelMaxRegret (-p) (-w) (-u) (Set.Icc (-u) (-ℓ))
        = duelMaxRegret p w u (Set.Icc ℓ u) := by
      rw [← duelMaxRegret_neg p w u (Set.Icc ℓ u),
        show -Set.Icc ℓ u = Set.Icc (-u) (-ℓ) from Set.neg_Icc ℓ u]
    rw [← hmax, ← hreg]
    exact hgt'

/-! ## The bridge to the two-candidate game

For a proxy other than the winner whose deviations preserve the population
median, the full game reduces exactly to the two-candidate game against the
winning report, away from strict mirror ties. -/

/-- **The two-candidate reduction, outcome level.**  A median-preserving
deviation by a non-winning proxy that is not exactly mirror-tied with the
winning report produces exactly the two-candidate outcome. -/
theorem outcome_update_eq_duelOutcome {q : F → ℝ} {y : ℝ}
    (hj : winner s q ≠ j)
    (hmedy : socialMedian (Function.update s j y) q = socialMedian s q)
    (hy : |y - socialMedian s q| ≠ |outcome s q - socialMedian s q|) :
    outcome (Function.update s j y) q
      = duelOutcome (outcome s q) y (socialMedian s q) := by
  have houtcome : outcome (Function.update s j y) q
      = Function.update s j y
          (delegate (Function.update s j y) (socialMedian s q)) := by
    unfold outcome winner
    rw [hmedy]
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · -- The deviation is strictly nearer: it wins.
    rw [duelOutcome_of_lt hlt]
    have hdj : delegate (Function.update s j y) (socialMedian s q) = j := by
      by_contra hne
      have hdd := delegate_dist_le (Function.update s j y) (socialMedian s q) j
      rw [Function.update_self] at hdd
      have hupd : Function.update s j y
          (delegate (Function.update s j y) (socialMedian s q))
          = s (delegate (Function.update s j y) (socialMedian s q)) := by
        rw [Function.update_apply, if_neg hne]
      rw [hupd] at hdd
      have hmin : |outcome s q - socialMedian s q|
          ≤ |s (delegate (Function.update s j y) (socialMedian s q))
              - socialMedian s q| :=
        delegate_dist_le s (socialMedian s q) _
      have hchain := le_trans hmin hdd
      linarith
    rw [houtcome, hdj, Function.update_self]
  · -- The deviation is strictly farther: the winner survives.
    rw [duelOutcome_of_ge (le_of_lt hgt)]
    have hdich := update_delegate_eq_new_or_eq_of_delegate_ne
      (s := s) (j := j) (x := y) (m := socialMedian s q) hj
    rw [houtcome]
    rcases hdich with h | h
    · exfalso
      have hk := delegate_dist_le (Function.update s j y) (socialMedian s q)
        (winner s q)
      have hupdw : Function.update s j y (winner s q) = outcome s q := by
        rw [Function.update_apply, if_neg hj]
        rfl
      rw [hupdw, h] at hk
      linarith
    · rw [h]
      rfl

/-- Reporting exactly the winning position leaves the outcome there,
regardless of the delegation tie-break. -/
theorem outcome_update_winner_eq {q : F → ℝ}
    (hj : winner s q ≠ j)
    (hmedy : socialMedian (Function.update s j (outcome s q)) q
      = socialMedian s q) :
    outcome (Function.update s j (outcome s q)) q = outcome s q := by
  set w := outcome s q with hw
  have houtcome : outcome (Function.update s j w) q
      = Function.update s j w
          (delegate (Function.update s j w) (socialMedian s q)) := by
    unfold outcome winner
    rw [hmedy]
  rw [houtcome]
  rcases update_delegate_eq_new_or_eq_of_delegate_ne
    (s := s) (j := j) (x := w) (m := socialMedian s q) hj with h | h
  · exact h
  · rw [h, hw]
    rfl

/-- A non-winner report on the left side of the old winner is a forced
dominating manipulation if it is never to the left of the manipulator's peak
and it strictly beats the old winner for at least one consistent median.  The
statement is deliberately semantic: the displayed §5 open intervals should
discharge the strict-witness hypothesis by interval geometry. -/
theorem spDominatesOver_left_of_report_between_peak_and_winner
    {Q : Set (F → ℝ)} {jw : P}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hpr : pp j ≤ r) (hrw : r < s jw)
    (hstrict : ∃ q ∈ Q, |r - socialMedian s q| < |s jw - socialMedian s q|) :
    SPDominatesOver pp s Q j r := by
  have hpw : pp j ≤ s jw := le_trans hpr (le_of_lt hrw)
  have old_out : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have old_delegate_ne : ∀ q ∈ Q, delegate s (socialMedian s q) ≠ j := by
    intro q hq hdelj
    have hdel : delegate s (socialMedian s q) = jw := by
      simpa [winner] using hQw q hq
    have : jw = j := by rw [← hdel, hdelj]
    exact hj this
  have new_out : ∀ q ∈ Q,
      outcome (Function.update s j r) q = r ∨
        outcome (Function.update s j r) q = s jw := by
    intro q hq
    have houtcome : outcome (Function.update s j r) q
        = Function.update s j r
            (delegate (Function.update s j r) (socialMedian s q)) := by
      unfold outcome winner
      rw [hmedr q hq]
    rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := r) (m := socialMedian s q)
        (old_delegate_ne q hq) with hnew | hold
    · left
      rw [houtcome, hnew]
    · right
      rw [houtcome, hold]
      have hdel : delegate s (socialMedian s q) = jw := by
        simpa [winner] using hQw q hq
      rw [hdel]
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases new_out q hq with hnew | hold
    · rw [hnew, old_out q hq]
      exact Or.inl ⟨hpr, le_of_lt hrw⟩
    · rw [hold, old_out q hq]
      exact Or.inl ⟨hpw, le_rfl⟩
  · obtain ⟨q, hq, hnear⟩ := hstrict
    refine ⟨q, hq, ?_⟩
    have hwin : winner s q ≠ j := by
      rw [hQw q hq]
      exact hj
    have hne : |r - socialMedian s q| ≠ |outcome s q - socialMedian s q| := by
      rw [old_out q hq]
      exact ne_of_lt hnear
    have hduel : duelOutcome (outcome s q) r (socialMedian s q) = r := by
      rw [old_out q hq]
      exact duelOutcome_of_lt hnear
    rw [outcome_update_eq_duelOutcome hwin (hmedr q hq) hne, hduel,
      old_out q hq]
    exact Or.inl ⟨hpr, hrw⟩

/-- Right-side mirror of
`spDominatesOver_left_of_report_between_peak_and_winner`. -/
theorem spDominatesOver_right_of_report_between_winner_and_peak
    {Q : Set (F → ℝ)} {jw : P}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hwr : s jw < r) (hrp : r ≤ pp j)
    (hstrict : ∃ q ∈ Q, |r - socialMedian s q| < |s jw - socialMedian s q|) :
    SPDominatesOver pp s Q j r := by
  have hwp : s jw ≤ pp j := le_trans (le_of_lt hwr) hrp
  have old_out : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have old_delegate_ne : ∀ q ∈ Q, delegate s (socialMedian s q) ≠ j := by
    intro q hq hdelj
    have hdel : delegate s (socialMedian s q) = jw := by
      simpa [winner] using hQw q hq
    have : jw = j := by rw [← hdel, hdelj]
    exact hj this
  have new_out : ∀ q ∈ Q,
      outcome (Function.update s j r) q = r ∨
        outcome (Function.update s j r) q = s jw := by
    intro q hq
    have houtcome : outcome (Function.update s j r) q
        = Function.update s j r
            (delegate (Function.update s j r) (socialMedian s q)) := by
      unfold outcome winner
      rw [hmedr q hq]
    rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := r) (m := socialMedian s q)
        (old_delegate_ne q hq) with hnew | hold
    · left
      rw [houtcome, hnew]
    · right
      rw [houtcome, hold]
      have hdel : delegate s (socialMedian s q) = jw := by
        simpa [winner] using hQw q hq
      rw [hdel]
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases new_out q hq with hnew | hold
    · rw [hnew, old_out q hq]
      exact Or.inr ⟨le_of_lt hwr, hrp⟩
    · rw [hold, old_out q hq]
      exact Or.inr ⟨le_rfl, hwp⟩
  · obtain ⟨q, hq, hnear⟩ := hstrict
    refine ⟨q, hq, ?_⟩
    have hwin : winner s q ≠ j := by
      rw [hQw q hq]
      exact hj
    have hne : |r - socialMedian s q| ≠ |outcome s q - socialMedian s q| := by
      rw [old_out q hq]
      exact ne_of_lt hnear
    have hduel : duelOutcome (outcome s q) r (socialMedian s q) = r := by
      rw [old_out q hq]
      exact duelOutcome_of_lt hnear
    rw [outcome_update_eq_duelOutcome hwin (hmedr q hq) hne, hduel,
      old_out q hq]
    exact Or.inr ⟨hwr, hrp⟩

omit [LinearOrder P] in
/-- If the median uncertainty image is an open interval and a left-side
report lies above the winner-reflection of its lower endpoint, then some
consistent median strictly prefers that report to the old winner by distance.
This is the geometric witness behind the §5 left open interval. -/
theorem exists_profile_report_strictly_closer_left_Ioo {Q : Set (F → ℝ)}
    {jw : P} {ℓ u : ℝ}
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hrw : r < s jw) (hℓmid : ℓ < (r + s jw) / 2) (hℓu : ℓ < u) :
    ∃ q ∈ Q, |r - socialMedian s q| < |s jw - socialMedian s q| := by
  let mid := (r + s jw) / 2
  have hmin : ℓ < min u mid := lt_min hℓu hℓmid
  obtain ⟨μ, hℓμ, hμmin⟩ := exists_between hmin
  have hμu : μ < u := lt_of_lt_of_le hμmin (min_le_left u mid)
  have hμmid : μ < mid := lt_of_lt_of_le hμmin (min_le_right u mid)
  have hμmem : μ ∈ (fun q => socialMedian s q) '' Q := by
    rw [hM]
    exact ⟨hℓμ, hμu⟩
  obtain ⟨q, hq, hqμ⟩ := hμmem
  refine ⟨q, hq, ?_⟩
  have hmedq : socialMedian s q = μ := hqμ
  rw [hmedq]
  exact (abs_left_sub_lt_abs_right_sub_iff hrw).mpr hμmid

omit [LinearOrder P] in
/-- Right-side mirror of
`exists_profile_report_strictly_closer_left_Ioo`. -/
theorem exists_profile_report_strictly_closer_right_Ioo {Q : Set (F → ℝ)}
    {jw : P} {ℓ u : ℝ}
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hwr : s jw < r) (hmidu : (s jw + r) / 2 < u) (hℓu : ℓ < u) :
    ∃ q ∈ Q, |r - socialMedian s q| < |s jw - socialMedian s q| := by
  let mid := (s jw + r) / 2
  have hmax : max ℓ mid < u := max_lt hℓu hmidu
  obtain ⟨μ, hmaxμ, hμu⟩ := exists_between hmax
  have hℓμ : ℓ < μ := lt_of_le_of_lt (le_max_left ℓ mid) hmaxμ
  have hmidμ : mid < μ := lt_of_le_of_lt (le_max_right ℓ mid) hmaxμ
  have hμmem : μ ∈ (fun q => socialMedian s q) '' Q := by
    rw [hM]
    exact ⟨hℓμ, hμu⟩
  obtain ⟨q, hq, hqμ⟩ := hμmem
  refine ⟨q, hq, ?_⟩
  have hmedq : socialMedian s q = μ := hqμ
  rw [hmedq]
  exact (abs_right_sub_lt_abs_left_sub_iff hwr).mpr hmidμ

/-- §5 left open-interval sufficiency: over an open median
uncertainty interval `(ℓ, u)`, any report in `(2ℓ - w, w)` that is still
weakly right of the manipulator's peak is a forced dominating manipulation. -/
theorem spDominatesOver_left_of_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) (hpr : pp j ≤ r)
    (hlower : 2 * ℓ - s jw < r) (hrw : r < s jw) :
    SPDominatesOver pp s Q j r := by
  refine spDominatesOver_left_of_report_between_peak_and_winner
    hQw hj hmedr hpr hrw ?_
  refine exists_profile_report_strictly_closer_left_Ioo hM hrw ?_ hℓu
  linarith

/-- Euclidean corollary of `spDominatesOver_left_of_Ioo`. -/
theorem dominatesOver_left_of_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) (hpr : pp j ≤ r)
    (hlower : 2 * ℓ - s jw < r) (hrw : r < s jw) :
    DominatesOver pp s Q j r :=
  (spDominatesOver_left_of_Ioo hQw hj hmedr hM hℓu hpr hlower hrw).dominatesOver

/-- §5 right open-interval sufficiency, mirror of
`spDominatesOver_left_of_Ioo`. -/
theorem spDominatesOver_right_of_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) (hwr : s jw < r) (hrp : r ≤ pp j)
    (hupper : r < 2 * u - s jw) :
    SPDominatesOver pp s Q j r := by
  refine spDominatesOver_right_of_report_between_winner_and_peak
    hQw hj hmedr hwr hrp ?_
  refine exists_profile_report_strictly_closer_right_Ioo hM hwr ?_ hℓu
  linarith

/-- Euclidean corollary of `spDominatesOver_right_of_Ioo`. -/
theorem dominatesOver_right_of_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) (hwr : s jw < r) (hrp : r ≤ pp j)
    (hupper : r < 2 * u - s jw) :
    DominatesOver pp s Q j r :=
  (spDominatesOver_right_of_Ioo hQw hj hmedr hM hℓu hwr hrp hupper).dominatesOver

/-- If a non-winner report is strictly farther from every consistent median
than the old winner, then it never changes the outcome and hence cannot be a
dominating manipulation.  This is the semantic obstruction behind the
open-interval endpoints. -/
theorem not_dominatesOver_of_report_strictly_farther_than_winner
    {Q : Set (F → ℝ)} {jw : P}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hfar : ∀ q ∈ Q, |s jw - socialMedian s q| < |r - socialMedian s q|) :
    ¬ DominatesOver pp s Q j r := by
  rintro ⟨_, q, hq, hpref⟩
  have old_out : outcome s q = s jw := by
    unfold outcome
    rw [hQw q hq]
  have hwin : winner s q ≠ j := by
    rw [hQw q hq]
    exact hj
  have hne : |r - socialMedian s q| ≠ |outcome s q - socialMedian s q| := by
    rw [old_out]
    exact ne_of_gt (hfar q hq)
  have hduel : duelOutcome (outcome s q) r (socialMedian s q) = outcome s q := by
    rw [old_out]
    exact duelOutcome_of_ge (le_of_lt (hfar q hq))
  have hsame : outcome (Function.update s j r) q = outcome s q := by
    rw [outcome_update_eq_duelOutcome hwin (hmedr q hq) hne, hduel]
  rw [hsame] at hpref
  unfold Prefers at hpref
  exact (lt_irrefl _) hpref

/-- §5 left open-interval necessity at the reflected lower endpoint:
if `r ≤ 2ℓ - w < w`, then every median in `(ℓ,u)` is closer to the old winner
than to `r`, so `r` cannot dominate. -/
theorem not_dominatesOver_left_of_Ioo_at_or_below_reflection
    {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hrw : r < s jw) (hrle : r ≤ 2 * ℓ - s jw) :
    ¬ DominatesOver pp s Q j r := by
  refine not_dominatesOver_of_report_strictly_farther_than_winner
    hQw hj hmedr ?_
  intro q hq
  have hmem : socialMedian s q ∈ Set.Ioo ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  have hmid : (r + s jw) / 2 < socialMedian s q := by
    linarith [hmem.1, hrle]
  exact (abs_right_sub_lt_abs_left_sub_iff hrw).mpr hmid

/-- §5 right open-interval necessity at the reflected upper
endpoint, mirroring `not_dominatesOver_left_of_Ioo_at_or_below_reflection`. -/
theorem not_dominatesOver_right_of_Ioo_at_or_above_reflection
    {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmedr : ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hwr : s jw < r) (hru : 2 * u - s jw ≤ r) :
    ¬ DominatesOver pp s Q j r := by
  refine not_dominatesOver_of_report_strictly_farther_than_winner
    hQw hj hmedr ?_
  intro q hq
  have hmem : socialMedian s q ∈ Set.Ioo ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  have hmid : socialMedian s q < (s jw + r) / 2 := by
    linarith [hmem.2, hru]
  exact (abs_left_sub_lt_abs_right_sub_iff hwr).mpr hmid

/-- §5 left-side set formula.  Among reports on the left side of
the current winner and weakly right of the manipulator's peak, domination is
exactly the open interval above the reflected lower endpoint. -/
theorem dominatesOver_left_side_set_eq_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ r, ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) :
    {r | pp j ≤ r ∧ r < s jw ∧ DominatesOver pp s Q j r}
      = {r | pp j ≤ r ∧ r ∈ Set.Ioo (2 * ℓ - s jw) (s jw)} := by
  ext r
  constructor
  · rintro ⟨hpr, hrw, hdom⟩
    refine ⟨hpr, ?_, hrw⟩
    by_contra hnot
    have hrle : r ≤ 2 * ℓ - s jw := le_of_not_gt hnot
    exact (not_dominatesOver_left_of_Ioo_at_or_below_reflection
      hQw hj (hmed r) hM hrw hrle) hdom
  · rintro ⟨hpr, hlower, hrw⟩
    exact ⟨hpr, hrw, dominatesOver_left_of_Ioo
      hQw hj (hmed r) hM hℓu hpr hlower hrw⟩

/-- §5 right-side set formula.  Among reports on the right side of
the current winner and weakly left of the manipulator's peak, domination is
exactly the open interval below the reflected upper endpoint. -/
theorem dominatesOver_right_side_set_eq_Ioo {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ r, ∀ q ∈ Q,
      socialMedian (Function.update s j r) q = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Ioo ℓ u)
    (hℓu : ℓ < u) :
    {r | s jw < r ∧ r ≤ pp j ∧ DominatesOver pp s Q j r}
      = {r | r ∈ Set.Ioo (s jw) (2 * u - s jw) ∧ r ≤ pp j} := by
  ext r
  constructor
  · rintro ⟨hwr, hrp, hdom⟩
    refine ⟨⟨hwr, ?_⟩, hrp⟩
    by_contra hnot
    have hrle : 2 * u - s jw ≤ r := le_of_not_gt hnot
    exact (not_dominatesOver_right_of_Ioo_at_or_above_reflection
      hQw hj (hmed r) hM hwr hrle) hdom
  · rintro ⟨⟨hwr, hupper⟩, hrp⟩
    exact ⟨hwr, hrp, dominatesOver_right_of_Ioo
      hQw hj (hmed r) hM hℓu hwr hrp hupper⟩

/-- **The two-candidate reduction, ex-post level.**  For a non-winning proxy
whose deviations all preserve the median at a profile, the best ex-post
distance equals the two-candidate one.  Mirror-tied deviations contribute
nothing beyond the two-candidate game: their real value dominates the
two-candidate closed form, and their two-candidate value is the winner's,
achieved by any far losing report. -/
theorem bestOutcomeDist_eq_duelBestDist {q : F → ℝ}
    (hj : winner s q ≠ j)
    (hmed : ∀ y, socialMedian (Function.update s j y) q = socialMedian s q) :
    bestOutcomeDist pp s j q
      = duelBestDist (pp j) (outcome s q) (socialMedian s q) := by
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun y => ?_
    by_cases hy : |y - socialMedian s q| = |outcome s q - socialMedian s q|
    · have hgy : duelOutcome (outcome s q) y (socialMedian s q) = outcome s q :=
        duelOutcome_of_ge (le_of_eq hy.symm)
      have hy'far : |socialMedian s q + |outcome s q - socialMedian s q| + 1
          - socialMedian s q| = |outcome s q - socialMedian s q| + 1 := by
        rw [show socialMedian s q + |outcome s q - socialMedian s q| + 1
            - socialMedian s q = |outcome s q - socialMedian s q| + 1 by ring]
        exact abs_of_nonneg (by positivity)
      have hy'ne : |socialMedian s q + |outcome s q - socialMedian s q| + 1
          - socialMedian s q| ≠ |outcome s q - socialMedian s q| := by
        rw [hy'far]
        linarith
      have hf := outcome_update_eq_duelOutcome hj (hmed _) hy'ne
      have hgy' : duelOutcome (outcome s q)
          (socialMedian s q + |outcome s q - socialMedian s q| + 1)
          (socialMedian s q) = outcome s q := by
        refine duelOutcome_of_ge ?_
        rw [hy'far]
        linarith
      calc bestOutcomeDist pp s j q
          ≤ |outcome (Function.update s j
              (socialMedian s q + |outcome s q - socialMedian s q| + 1)) q
              - pp j| := bestOutcomeDist_le _
        _ = |duelOutcome (outcome s q) y (socialMedian s q) - pp j| := by
            rw [hf, hgy', hgy]
    · rw [← outcome_update_eq_duelOutcome hj (hmed y) hy]
      exact bestOutcomeDist_le y
  · refine le_ciInf fun y => ?_
    by_cases hy : |y - socialMedian s q| = |outcome s q - socialMedian s q|
    · have houtcome : outcome (Function.update s j y) q
          = Function.update s j y
              (delegate (Function.update s j y) (socialMedian s q)) := by
        unfold outcome winner
        rw [hmed y]
      rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := y) (m := socialMedian s q) hj with h | h
      · rw [houtcome, h, duelBestDist_eq]
        refine max_le ?_ (abs_nonneg _)
        have ht := abs_sub_le (pp j) y (socialMedian s q)
        rw [hy] at ht
        rw [abs_sub_comm y (pp j)]
        linarith
      · rw [houtcome, h, duelBestDist_eq]
        have hpos : s (delegate s (socialMedian s q)) = outcome s q := rfl
        rw [hpos]
        refine max_le ?_ (abs_nonneg _)
        have ht := abs_sub_le (pp j) (outcome s q) (socialMedian s q)
        rw [abs_sub_comm (outcome s q) (pp j)]
        linarith
    · rw [outcome_update_eq_duelOutcome hj (hmed y) hy]
      exact ciInf_le (bddBelow_duel _ _ _) y

/-- **The two-candidate reduction, regret level**, for deviations that are
either tie-free or exactly the winning position. -/
theorem regret_eq_duelRegret {q : F → ℝ} {y : ℝ}
    (hj : winner s q ≠ j)
    (hmed : ∀ y', socialMedian (Function.update s j y') q = socialMedian s q)
    (hy : |y - socialMedian s q| ≠ |outcome s q - socialMedian s q|
      ∨ y = outcome s q) :
    regret pp s j y q
      = duelRegret (pp j) (outcome s q) y (socialMedian s q) := by
  rcases hy with hy | rfl
  · unfold regret duelRegret
    rw [bestOutcomeDist_eq_duelBestDist hj hmed,
      outcome_update_eq_duelOutcome hj (hmed y) hy]
  · unfold regret duelRegret
    rw [bestOutcomeDist_eq_duelBestDist hj hmed,
      outcome_update_winner_eq hj (hmed _), duelOutcome_of_ge le_rfl]

/-- **Theorem 4** (Bielous-Meir), in the full proxy game.  Fix a proxy `j`
that never wins on the information set `Q`, always faces the same winning
report `s jw`, and cannot move the population median anywhere on `Q`, and
suppose the consistent medians form exactly the interval `[ℓ, u]`.  If `j`'s
peak lies weakly outside the winning interval at the near boundary
(`pp j ≤ 2ℓ - s jw`) and the uncertainty reaches the boundary-winner
midpoint (`(ℓ + s jw)/2 ≤ u`), then reporting the near boundary incurs
strictly less maximal regret than any other report.

The two-candidate reduction is exact off mirror ties; at a mirror tie the
boundary report's real outcome is the boundary or the winner by the delegate
dichotomy, and the boundary is the nearer of the two to the peak, so the
two-candidate value still dominates.  The witness median against any other
report carries a tie-freeness certificate, so its regret transfers exactly. -/
theorem maxRegretOver_boundary_lt {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {x : ℝ} (hx : x ≠ ℓ) :
    maxRegretOver pp s j ℓ Q < maxRegretOver pp s j x Q := by
  have hlu : ℓ ≤ u := le_trans (by linarith) hu
  have hQne : Q.Nonempty := by
    have hmem : ℓ ∈ (fun q => socialMedian s q) '' Q := by
      rw [hM]
      exact Set.mem_Icc.mpr ⟨le_refl ℓ, hlu⟩
    obtain ⟨q, hq, -⟩ := hmem
    exact ⟨q, hq⟩
  have hout : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have hwin : ∀ q ∈ Q, winner s q ≠ j := fun q hq => by
    rw [hQw q hq]
    exact hj
  have hμmem : ∀ q ∈ Q, socialMedian s q ∈ Set.Icc ℓ u := fun q hq => by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  -- The boundary report's real maximal regret is at most the two-candidate
  -- one.
  have hupper : maxRegretOver pp s j ℓ Q
      ≤ duelMaxRegret (pp j) (s jw) ℓ (Set.Icc ℓ u) := by
    refine maxRegretOver_le hQne fun q hq => ?_
    refine le_trans ?_ (duelRegret_le_duelMaxRegret (hμmem q hq))
    by_cases hy : |ℓ - socialMedian s q| = |s jw - socialMedian s q|
    · -- Mirror tie: the real outcome is the boundary or the winner, and the
      -- boundary is nearer the peak.
      have houtcome : outcome (Function.update s j ℓ) q
          = Function.update s j ℓ
              (delegate (Function.update s j ℓ) (socialMedian s q)) := by
        unfold outcome winner
        rw [hmed q hq ℓ]
      have hduel : duelOutcome (s jw) ℓ (socialMedian s q) = s jw :=
        duelOutcome_of_ge (le_of_eq hy.symm)
      unfold regret duelRegret
      rw [bestOutcomeDist_eq_duelBestDist (hwin q hq) (hmed q hq),
        hout q hq, hduel]
      refine sub_le_sub_right ?_ _
      rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := ℓ) (m := socialMedian s q)
        (hwin q hq) with h | h
      · rw [houtcome, h,
          abs_of_nonneg (show (0:ℝ) ≤ ℓ - pp j by linarith),
          abs_of_nonneg (show (0:ℝ) ≤ s jw - pp j by linarith)]
        linarith
      · rw [houtcome, h,
          show s (delegate s (socialMedian s q)) = s jw from hout q hq]
    · -- Off ties the reduction is exact.
      have hcert : |ℓ - socialMedian s q|
          ≠ |outcome s q - socialMedian s q| := by
        rw [hout q hq]
        exact hy
      rw [regret_eq_duelRegret (hwin q hq) (hmed q hq) (Or.inl hcert),
        hout q hq]
  -- The witness median realizes strictly more regret for any other report.
  obtain ⟨μ₀, hμ₀, hcert, hgt⟩ := exists_duelRegret_witness_gt hp hlw hu hx
  have hμ₀img : μ₀ ∈ (fun q => socialMedian s q) '' Q := by
    rw [hM]
    exact hμ₀
  obtain ⟨q₁, hq₁, hμeq'⟩ := hμ₀img
  have hμeq : socialMedian s q₁ = μ₀ := hμeq'
  have hcert' : |x - socialMedian s q₁| ≠ |outcome s q₁ - socialMedian s q₁|
      ∨ x = outcome s q₁ := by
    rw [hout q₁ hq₁, hμeq]
    exact hcert
  have hreg : regret pp s j x q₁ = duelRegret (pp j) (s jw) x μ₀ := by
    rw [regret_eq_duelRegret (hwin q₁ hq₁) (hmed q₁ hq₁) hcert',
      hout q₁ hq₁, hμeq]
  calc maxRegretOver pp s j ℓ Q
      ≤ duelMaxRegret (pp j) (s jw) ℓ (Set.Icc ℓ u) := hupper
    _ < duelRegret (pp j) (s jw) x μ₀ := hgt
    _ = regret pp s j x q₁ := hreg.symm
    _ ≤ maxRegretOver pp s j x Q := regret_le_maxRegretOver hq₁

/-- Under the hypotheses of `maxRegretOver_boundary_lt`, a report is
minimax-regret exactly when it is the near boundary of the median
uncertainty.  In particular the unique minimax-regret report lies weakly on
the peak's side of every consistent median: the proxy compromises toward the
median but never past the nearest position it might hold. -/
theorem isMinimaxRegret_iff_eq_left_boundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {r : ℝ} :
    IsMinimaxRegret pp s Q j r ↔ r = ℓ := by
  constructor
  · intro h
    by_contra hne
    exact absurd (h ℓ)
      (not_le.mpr (maxRegretOver_boundary_lt hQw hj hmed hM hp hlw hu hne))
  · intro hr r'
    rcases eq_or_ne r' ℓ with hr' | hr'
    · rw [hr, hr']
    · rw [hr]
      exact le_of_lt (maxRegretOver_boundary_lt hQw hj hmed hM hp hlw hu hr')

/-- Mirror of `maxRegretOver_boundary_lt` at the right boundary: for a
non-winning proxy with peak weakly outside the winning interval at the far
boundary, reporting `u` incurs strictly less maximal regret than any other
report. -/
theorem maxRegretOver_right_boundary_lt {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {x : ℝ} (hx : x ≠ u) :
    maxRegretOver pp s j u Q < maxRegretOver pp s j x Q := by
  have hlu : ℓ ≤ u := le_trans hl (by linarith)
  have hQne : Q.Nonempty := by
    have hmem : u ∈ (fun q => socialMedian s q) '' Q := by
      rw [hM]
      exact Set.mem_Icc.mpr ⟨hlu, le_refl u⟩
    obtain ⟨q, hq, -⟩ := hmem
    exact ⟨q, hq⟩
  have hout : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have hwin : ∀ q ∈ Q, winner s q ≠ j := fun q hq => by
    rw [hQw q hq]
    exact hj
  have hμmem : ∀ q ∈ Q, socialMedian s q ∈ Set.Icc ℓ u := fun q hq => by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  have hupper : maxRegretOver pp s j u Q
      ≤ duelMaxRegret (pp j) (s jw) u (Set.Icc ℓ u) := by
    refine maxRegretOver_le hQne fun q hq => ?_
    refine le_trans ?_ (duelRegret_le_duelMaxRegret (hμmem q hq))
    by_cases hy : |u - socialMedian s q| = |s jw - socialMedian s q|
    · have houtcome : outcome (Function.update s j u) q
          = Function.update s j u
              (delegate (Function.update s j u) (socialMedian s q)) := by
        unfold outcome winner
        rw [hmed q hq u]
      have hduel : duelOutcome (s jw) u (socialMedian s q) = s jw :=
        duelOutcome_of_ge (le_of_eq hy.symm)
      unfold regret duelRegret
      rw [bestOutcomeDist_eq_duelBestDist (hwin q hq) (hmed q hq),
        hout q hq, hduel]
      refine sub_le_sub_right ?_ _
      rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := u) (m := socialMedian s q)
        (hwin q hq) with h | h
      · rw [houtcome, h,
          abs_of_nonpos (show u - pp j ≤ 0 by linarith),
          abs_of_nonpos (show s jw - pp j ≤ 0 by linarith)]
        linarith
      · rw [houtcome, h,
          show s (delegate s (socialMedian s q)) = s jw from hout q hq]
    · have hcert : |u - socialMedian s q|
          ≠ |outcome s q - socialMedian s q| := by
        rw [hout q hq]
        exact hy
      rw [regret_eq_duelRegret (hwin q hq) (hmed q hq) (Or.inl hcert),
        hout q hq]
  obtain ⟨μ₀, hμ₀, hcert, hgt⟩ :=
    exists_duelRegret_witness_gt_right hp hwu hl hx
  have hμ₀img : μ₀ ∈ (fun q => socialMedian s q) '' Q := by
    rw [hM]
    exact hμ₀
  obtain ⟨q₁, hq₁, hμeq'⟩ := hμ₀img
  have hμeq : socialMedian s q₁ = μ₀ := hμeq'
  have hcert' : |x - socialMedian s q₁| ≠ |outcome s q₁ - socialMedian s q₁|
      ∨ x = outcome s q₁ := by
    rw [hout q₁ hq₁, hμeq]
    exact hcert
  have hreg : regret pp s j x q₁ = duelRegret (pp j) (s jw) x μ₀ := by
    rw [regret_eq_duelRegret (hwin q₁ hq₁) (hmed q₁ hq₁) hcert',
      hout q₁ hq₁, hμeq]
  calc maxRegretOver pp s j u Q
      ≤ duelMaxRegret (pp j) (s jw) u (Set.Icc ℓ u) := hupper
    _ < duelRegret (pp j) (s jw) x μ₀ := hgt
    _ = regret pp s j x q₁ := hreg.symm
    _ ≤ maxRegretOver pp s j x Q := regret_le_maxRegretOver hq₁

/-- Mirror of `isMinimaxRegret_iff_eq_left_boundary` at the right boundary. -/
theorem isMinimaxRegret_iff_eq_right_boundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {r : ℝ} :
    IsMinimaxRegret pp s Q j r ↔ r = u := by
  constructor
  · intro h
    by_contra hne
    exact absurd (h u) (not_le.mpr
      (maxRegretOver_right_boundary_lt hQw hj hmed hM hp hwu hl hne))
  · intro hr r'
    rcases eq_or_ne r' u with hr' | hr'
    · rw [hr, hr']
    · rw [hr]
      exact le_of_lt
        (maxRegretOver_right_boundary_lt hQw hj hmed hM hp hwu hl hr')

/-- **Theorem 4's conclusion, weak form** (Bielous–Meir): the minimax-regret
report of a left outside proxy stays weakly left of every consistent
median — it never crosses the median it is uncertain about.  This is the
same-side property in the weak sense; the strict `StrongMonotoneOver` form
fails at the boundary (`not_strongMonotoneOver_left_boundary`). -/
theorem isMinimaxRegret_report_le_socialMedian {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    ∀ q ∈ Q, r ≤ socialMedian s q := by
  rw [isMinimaxRegret_iff_eq_left_boundary hQw hj hmed hM hp hlw hu] at hr
  intro q hq
  have hmem : socialMedian s q ∈ Set.Icc ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  rw [hr]
  exact hmem.1

/-- Mirror of `isMinimaxRegret_report_le_socialMedian` for a right outside
proxy. -/
theorem isMinimaxRegret_socialMedian_le_report {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    ∀ q ∈ Q, socialMedian s q ≤ r := by
  rw [isMinimaxRegret_iff_eq_right_boundary hQw hj hmed hM hp hwu hl] at hr
  intro q hq
  have hmem : socialMedian s q ∈ Set.Icc ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  rw [hr]
  exact hmem.2

/-- A left-boundary minimax-regret report is weak non-crossing when the
current report is weakly left of the whole uncertainty interval.  This is the
weak replacement for the false strict-strong-monotone reading. -/
theorem isMinimaxRegret_weakStrongMonotoneOver_leftBoundary
    {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    (hsj : s j ≤ ℓ) {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    WeakStrongMonotoneOver s Q j r := by
  have hrℓ : r = ℓ := (isMinimaxRegret_iff_eq_left_boundary
    hQw hj hmed hM hp hlw hu).mp hr
  intro q hq
  have hmem : socialMedian s q ∈ Set.Icc ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  rw [hrℓ]
  constructor
  · intro _
    exact hmem.1
  · intro hle
    exact le_trans hle hsj

/-- Right-boundary mirror of
`isMinimaxRegret_weakStrongMonotoneOver_leftBoundary`. -/
theorem isMinimaxRegret_weakStrongMonotoneOver_rightBoundary
    {Q : Set (F → ℝ)} {jw : P} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    (hsj : u ≤ s j) {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    WeakStrongMonotoneOver s Q j r := by
  have hru : r = u := (isMinimaxRegret_iff_eq_right_boundary
    hQw hj hmed hM hp hwu hl).mp hr
  intro q hq
  have hmem : socialMedian s q ∈ Set.Icc ℓ u := by
    rw [← hM]
    exact ⟨q, hq, rfl⟩
  rw [hru]
  constructor
  · intro hle
    exact le_trans hsj hle
  · intro _
    exact hmem.2

omit [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F] in
/-- Endpoint minimax-regret hypotheses alone do not imply any fixed-factor
history-interval contraction.  For every proposed factor `α < 1`, the
right-boundary minimax side conditions can hold while the new lower cut
`(u + w) / 2` leaves more than an `α` fraction of the old interval width.

Thus the minimax-regret endpoint theorem supplies weak non-crossing, but not
the fixed-factor premise used by the windowed-contraction theorem. -/
theorem rightBoundary_minimax_hypotheses_allow_no_fixed_factor_cut
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p ℓ u w : ℝ,
      ℓ < u ∧
      2 * u - w ≤ p ∧
      w < u ∧
      ℓ ≤ (u + w) / 2 ∧
      α * (u - ℓ) < u - (u + w) / 2 := by
  refine ⟨2 + α, 0, 1, -α, ?_⟩
  constructor
  · norm_num
  constructor
  · ring_nf
    exact le_refl (2 + α : ℝ)
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

omit [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F] in
/-- There is no universal fixed contraction factor forced by the
right-boundary minimax endpoint side conditions. -/
theorem not_exists_rightBoundary_minimax_fixed_factor_cut :
    ¬ ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ p ℓ u w : ℝ,
        ℓ < u →
        2 * u - w ≤ p →
        w < u →
        ℓ ≤ (u + w) / 2 →
        u - (u + w) / 2 ≤ α * (u - ℓ) := by
  rintro ⟨α, hα0, hα1, hcut⟩
  obtain ⟨p, ℓ, u, w, hℓu, hp, hwu, hmid, hbad⟩ :=
    rightBoundary_minimax_hypotheses_allow_no_fixed_factor_cut α hα0 hα1
  have hle := hcut p ℓ u w hℓu hp hwu hmid
  linarith

omit [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F] in
/-- Left-boundary mirror of
`rightBoundary_minimax_hypotheses_allow_no_fixed_factor_cut`. -/
theorem leftBoundary_minimax_hypotheses_allow_no_fixed_factor_cut
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p ℓ u w : ℝ,
      ℓ < u ∧
      p ≤ 2 * ℓ - w ∧
      ℓ < w ∧
      (ℓ + w) / 2 ≤ u ∧
      α * (u - ℓ) < (ℓ + w) / 2 - ℓ := by
  refine ⟨-(2 + α), -1, 0, α, ?_⟩
  constructor
  · norm_num
  constructor
  · ring_nf
    exact le_refl (-2 - α : ℝ)
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

omit [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F] in
/-- Left-boundary mirror of
`not_exists_rightBoundary_minimax_fixed_factor_cut`. -/
theorem not_exists_leftBoundary_minimax_fixed_factor_cut :
    ¬ ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ p ℓ u w : ℝ,
        ℓ < u →
        p ≤ 2 * ℓ - w →
        ℓ < w →
        (ℓ + w) / 2 ≤ u →
        (ℓ + w) / 2 - ℓ ≤ α * (u - ℓ) := by
  rintro ⟨α, hα0, hα1, hcut⟩
  obtain ⟨p, ℓ, u, w, hℓu, hp, hℓw, hmid, hbad⟩ :=
    leftBoundary_minimax_hypotheses_allow_no_fixed_factor_cut α hα0 hα1
  have hle := hcut p ℓ u w hℓu hp hℓw hmid
  linarith

/-- A report equal to the current report is never a dominating manipulation:
it leaves every outcome unchanged, so the required strict improvement witness
cannot exist.  This covers both the winner-at-peak minimax case and the
winner-stay minimax case. -/
theorem not_dominatesOver_stay (pp : P → ℝ) (s : P → ℝ) (Q : Set (F → ℝ))
    (j : P) :
    ¬ DominatesOver pp s Q j (s j) := by
  rintro ⟨_, q, _, hpref⟩
  rw [Function.update_eq_self] at hpref
  unfold Prefers at hpref
  exact (lt_irrefl _) hpref

/-- The winner-at-peak minimax report is a stay-put report, hence not a
dominating manipulation.  This is the formal correction to the blanket reading
of the paper's minimax-regret/dominance remark. -/
theorem winner_at_peak_minimax_not_dominatesOver {q : F → ℝ}
    (hw : s (winner s q) = pp (winner s q)) :
    IsMinimaxRegret pp s (winnerInfoSet (F := F) s (winner s q))
        (winner s q) (s (winner s q))
      ∧ ¬ DominatesOver pp s (winnerInfoSet (F := F) s (winner s q))
        (winner s q) (s (winner s q)) := by
  exact ⟨(isMinimaxRegret_of_winner_at_peak (pp := pp) (s := s) (q := q) hw).2,
    not_dominatesOver_stay pp s _ _⟩

/-- In the left-boundary non-winner regime, a minimax-regret report is a
forced single-peaked dominating manipulation.  The report is the near
boundary `ℓ`: at every consistent median it either leaves the old winner in
place or wins at `ℓ`, both weakly better for a peak left of the winner
interval; at a profile realizing median `ℓ`, it wins strictly. -/
theorem isMinimaxRegret_spDominatesOver_leftBoundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    SPDominatesOver pp s Q j r := by
  have hrℓ : r = ℓ := (isMinimaxRegret_iff_eq_left_boundary
    hQw hj hmed hM hp hlw hu).mp hr
  subst r
  have hpℓ : pp j ≤ ℓ := by linarith
  have hpw : pp j ≤ s jw := le_trans hpℓ (le_of_lt hlw)
  have hout : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have hwin : ∀ q ∈ Q, winner s q ≠ j := fun q hq => by
    rw [hQw q hq]
    exact hj
  refine ⟨?_, ?_⟩
  · intro q hq
    have houtcome : outcome (Function.update s j ℓ) q
        = Function.update s j ℓ
            (delegate (Function.update s j ℓ) (socialMedian s q)) := by
      unfold outcome winner
      rw [hmed q hq ℓ]
    rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := ℓ) (m := socialMedian s q) (hwin q hq) with hnew | hold
    · rw [houtcome, hnew, hout q hq]
      exact Or.inl ⟨hpℓ, le_of_lt hlw⟩
    · rw [houtcome, hold,
        show s (delegate s (socialMedian s q)) = s jw from hout q hq,
        hout q hq]
      exact Or.inl ⟨hpw, le_rfl⟩
  · have hlu : ℓ ≤ u := le_trans (by linarith) hu
    have hℓmem : ℓ ∈ (fun q => socialMedian s q) '' Q := by
      rw [hM]
      exact Set.mem_Icc.mpr ⟨le_rfl, hlu⟩
    obtain ⟨qℓ, hqℓ, hmedℓ'⟩ := hℓmem
    have hmedℓ : socialMedian s qℓ = ℓ := hmedℓ'
    refine ⟨qℓ, hqℓ, ?_⟩
    have hcert : |ℓ - socialMedian s qℓ| ≠ |outcome s qℓ - socialMedian s qℓ| := by
      rw [hmedℓ, hout qℓ hqℓ, sub_self, abs_zero]
      exact ne_of_lt (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hlw)))
    have hduel : duelOutcome (outcome s qℓ) ℓ (socialMedian s qℓ) = ℓ := by
      rw [hmedℓ, hout qℓ hqℓ]
      refine duelOutcome_of_lt ?_
      rw [sub_self, abs_zero, abs_of_pos (by linarith)]
      linarith
    rw [outcome_update_eq_duelOutcome (hwin qℓ hqℓ) (hmed qℓ hqℓ ℓ) hcert,
      hduel, hout qℓ hqℓ]
    exact Or.inl ⟨hpℓ, hlw⟩

/-- Euclidean corollary of
`isMinimaxRegret_spDominatesOver_leftBoundary`. -/
theorem isMinimaxRegret_dominatesOver_leftBoundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    DominatesOver pp s Q j r :=
  (isMinimaxRegret_spDominatesOver_leftBoundary hQw hj hmed hM hp hlw hu hr).dominatesOver

/-- Right-boundary mirror of
`isMinimaxRegret_spDominatesOver_leftBoundary`. -/
theorem isMinimaxRegret_spDominatesOver_rightBoundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    SPDominatesOver pp s Q j r := by
  have hru : r = u := (isMinimaxRegret_iff_eq_right_boundary
    hQw hj hmed hM hp hwu hl).mp hr
  subst r
  have hup : u ≤ pp j := by linarith
  have hwp : s jw ≤ pp j := le_trans (le_of_lt hwu) hup
  have hout : ∀ q ∈ Q, outcome s q = s jw := fun q hq => by
    unfold outcome
    rw [hQw q hq]
  have hwin : ∀ q ∈ Q, winner s q ≠ j := fun q hq => by
    rw [hQw q hq]
    exact hj
  refine ⟨?_, ?_⟩
  · intro q hq
    have houtcome : outcome (Function.update s j u) q
        = Function.update s j u
            (delegate (Function.update s j u) (socialMedian s q)) := by
      unfold outcome winner
      rw [hmed q hq u]
    rcases update_delegate_eq_new_or_eq_of_delegate_ne
        (s := s) (j := j) (x := u) (m := socialMedian s q) (hwin q hq) with hnew | hold
    · rw [houtcome, hnew, hout q hq]
      exact Or.inr ⟨le_of_lt hwu, hup⟩
    · rw [houtcome, hold,
        show s (delegate s (socialMedian s q)) = s jw from hout q hq,
        hout q hq]
      exact Or.inr ⟨le_rfl, hwp⟩
  · have hlu : ℓ ≤ u := le_trans hl (by linarith)
    have humem : u ∈ (fun q => socialMedian s q) '' Q := by
      rw [hM]
      exact Set.mem_Icc.mpr ⟨hlu, le_rfl⟩
    obtain ⟨qu, hqu, hmedu'⟩ := humem
    have hmedu : socialMedian s qu = u := hmedu'
    refine ⟨qu, hqu, ?_⟩
    have hcert : |u - socialMedian s qu| ≠ |outcome s qu - socialMedian s qu| := by
      rw [hmedu, hout qu hqu, sub_self, abs_zero]
      exact ne_of_lt (abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hwu)))
    have hduel : duelOutcome (outcome s qu) u (socialMedian s qu) = u := by
      rw [hmedu, hout qu hqu]
      refine duelOutcome_of_lt ?_
      rw [sub_self, abs_zero, abs_of_neg (by linarith)]
      linarith
    rw [outcome_update_eq_duelOutcome (hwin qu hqu) (hmed qu hqu u) hcert,
      hduel, hout qu hqu]
    exact Or.inr ⟨hwu, hup⟩

/-- Euclidean corollary of
`isMinimaxRegret_spDominatesOver_rightBoundary`. -/
theorem isMinimaxRegret_dominatesOver_rightBoundary {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    DominatesOver pp s Q j r :=
  (isMinimaxRegret_spDominatesOver_rightBoundary hQw hj hmed hM hp hwu hl hr).dominatesOver

omit [LinearOrder P] in
/-- **The strict reading of Theorem 4's conclusion fails.**  The near
boundary of the median uncertainty is itself the least consistent median:
at a profile realizing it, a proxy currently reporting strictly left of the
boundary lands exactly ON the median rather than strictly on its side.
Only the weak same-side form holds; the median is still preserved by such a
report, since moving onto the median from its own side never moves the
canonical median (`socialMedian_update_eq_of_proxy_lt`), but that half-step
is outside the strict `StrongMonotoneOver` classification. -/
theorem not_strongMonotoneOver_left_boundary {Q : Set (F → ℝ)} {ℓ u : ℝ}
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u) (hlu : ℓ ≤ u)
    (hsj : s j < ℓ) : ¬ StrongMonotoneOver s Q j ℓ := by
  intro hmono
  have hℓ : ℓ ∈ (fun q => socialMedian s q) '' Q := by
    rw [hM]
    exact Set.mem_Icc.mpr ⟨le_refl ℓ, hlu⟩
  obtain ⟨q₀, hq₀, hmed₀⟩ := hℓ
  have hmed₀' : socialMedian s q₀ = ℓ := hmed₀
  have h := (hmono q₀ hq₀).1
  rw [hmed₀'] at h
  exact absurd (h hsj) (lt_irrefl ℓ)

/-- The minimax-regret report of a left outside proxy is not strong-monotone
in the strict sense whenever its current report is strictly left of the
uncertainty interval. -/
theorem not_strongMonotoneOver_of_isMinimaxRegret {Q : Set (F → ℝ)} {jw : P}
    {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    (hsj : s j < ℓ) {r : ℝ} (hr : IsMinimaxRegret pp s Q j r) :
    ¬ StrongMonotoneOver s Q j r := by
  rw [isMinimaxRegret_iff_eq_left_boundary hQw hj hmed hM hp hlw hu] at hr
  subst hr
  exact not_strongMonotoneOver_left_boundary hM (le_trans (by linarith) hu) hsj

/-! ## The winning proxy

The winner case of Theorem 4.  For a winner reporting `w := s j`
off its peak `p := pp j < w`, weakly left of the whole uncertainty interval,
staying put is minimax-regret under two geometric hypotheses the paper
leaves implicit: no other report lies strictly inside `(2p - w, 2u - w)` —
`winnerStay_not_isMinimaxRegret` in
`GameTheory.Mechanism.ProxyVoting.Counterexamples` shows the left half is
necessary — and some report sits exactly at the reflected far boundary
`2u - w`, so the uncertainty reaches the winner's cell edge.  Without the
edge report the winner could win with uniform slack at every consistent
median and creep toward its peak, again beating staying.

The proof needs no runner-up machinery.  Deviations right of `w` are
dominated pointwise: their outcome is the deviation itself, farther from
the peak, or another's report, which the gap keeps at least `w - p` from
the peak.  For deviations left of `w`, the edge report traps every
deviation outcome within `2u - w - m` of the median `m`, so the best
ex-post distance is at least `(w - p) - 2(u - m)` and staying's maximal
regret is at most `2(u - w)`; at the median-`u` profile a left deviation
loses to the edge report at `2u - w`, paying exactly that. -/

/-- Against the edge report, every deviation outcome of the winner stays
within `2u - w - m` of the median. -/
private theorem winner_deviation_bound {u : ℝ} {q : F → ℝ}
    (hmedq : ∀ y, socialMedian (Function.update s j y) q = socialMedian s q)
    (hedge : ∃ k, k ≠ j ∧ s k = 2 * u - s j)
    (hmu : socialMedian s q ≤ u) (hwu : s j ≤ u) (y : ℝ) :
    |outcome (Function.update s j y) q - socialMedian s q|
      ≤ 2 * u - s j - socialMedian s q := by
  obtain ⟨k, hkj, hk⟩ := hedge
  have h := delegate_dist_le (Function.update s j y) (socialMedian s q) k
  rw [Function.update_of_ne hkj, hk] at h
  have habs : |2 * u - s j - socialMedian s q|
      = 2 * u - s j - socialMedian s q := abs_of_nonneg (by linarith)
  rw [habs] at h
  unfold outcome winner
  rw [hmedq y]
  exact h

/-- The winner's regret from staying is at most twice the distance from the
median to the far boundary. -/
private theorem winner_stay_regret_le {u : ℝ} {q : F → ℝ}
    (hw : winner s q = j)
    (hmedq : ∀ y, socialMedian (Function.update s j y) q = socialMedian s q)
    (hedge : ∃ k, k ≠ j ∧ s k = 2 * u - s j)
    (hpw : pp j < s j) (hmu : socialMedian s q ≤ u) (hwu : s j ≤ u) :
    regret pp s j (s j) q ≤ 2 * (u - socialMedian s q) := by
  have hstay : outcome (Function.update s j (s j)) q = s j := by
    rw [Function.update_eq_self]
    unfold outcome
    rw [hw]
  unfold regret
  rw [hstay, abs_of_pos (show (0:ℝ) < s j - pp j by linarith)]
  rcases le_or_gt (s j - pp j) (2 * (u - socialMedian s q)) with hA | hA
  · have := bestOutcomeDist_nonneg (pp := pp) (s := s) (j := j) (q := q)
    linarith
  · have hbd : s j - pp j - 2 * (u - socialMedian s q)
        ≤ bestOutcomeDist pp s j q := by
      unfold bestOutcomeDist
      refine le_ciInf fun y => ?_
      have h1 := winner_deviation_bound hmedq hedge hmu hwu y
      have h2 := (abs_le.mp h1).1
      calc s j - pp j - 2 * (u - socialMedian s q)
          ≤ outcome (Function.update s j y) q - pp j := by linarith
        _ ≤ |outcome (Function.update s j y) q - pp j| := le_abs_self _
    linarith

/-- At the far-boundary median, a deviation left of the winner's report
loses to the edge report. -/
private theorem winner_dev_outcome_edge {u : ℝ} {q : F → ℝ}
    (hmedq : ∀ y, socialMedian (Function.update s j y) q = socialMedian s q)
    (hu : socialMedian s q = u)
    (hgap : ∀ k, k ≠ j → s k ≤ 2 * pp j - s j ∨ 2 * u - s j ≤ s k)
    (hedge : ∃ k, k ≠ j ∧ s k = 2 * u - s j)
    (hpw : pp j < s j) (hwu : s j ≤ u) {x : ℝ} (hx : x < s j) :
    outcome (Function.update s j x) q = 2 * u - s j := by
  obtain ⟨k, hkj, hk⟩ := hedge
  have h := delegate_dist_le (Function.update s j x) u k
  rw [Function.update_of_ne hkj, hk] at h
  have habs : |2 * u - s j - u| = u - s j := by
    rw [show 2 * u - s j - u = u - s j by ring]
    exact abs_of_nonneg (by linarith)
  rw [habs] at h
  unfold outcome winner
  rw [hmedq x, hu]
  set d := delegate (Function.update s j x) u with hd
  by_cases hdj : d = j
  · exfalso
    rw [hdj, Function.update_self] at h
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  · rw [Function.update_of_ne hdj] at h ⊢
    have hband := abs_le.mp h
    rcases hgap d hdj with hL | hR
    · exfalso
      have h1 := hband.1
      linarith
    · exact le_antisymm (by linarith [hband.2]) hR

/-- **Theorem 4, the winning proxy.**  A winner reporting off
its peak, weakly left of the whole uncertainty interval, has staying put as
a minimax-regret strategy, provided no other report lies strictly inside
`(2p - w, 2u - w)` and some report sits exactly at the reflected far
boundary `2u - w`.  The gap hypothesis is necessary
(`winnerStay_not_isMinimaxRegret`). -/
theorem isMinimaxRegret_winner_stay {Q : Set (F → ℝ)} {ℓ u : ℝ}
    (hQw : ∀ q ∈ Q, winner s q = j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hM : (fun q => socialMedian s q) '' Q = Set.Icc ℓ u)
    (hpw : pp j < s j) (hwl : s j ≤ ℓ) (hlu : ℓ ≤ u)
    (hgap : ∀ k, k ≠ j → s k ≤ 2 * pp j - s j ∨ 2 * u - s j ≤ s k)
    (hedge : ∃ k, k ≠ j ∧ s k = 2 * u - s j) :
    IsMinimaxRegret pp s Q j (s j) := by
  have hwu : s j ≤ u := le_trans hwl hlu
  have hQne : Q.Nonempty := by
    have hmem : ℓ ∈ (fun q => socialMedian s q) '' Q := by
      rw [hM]
      exact Set.mem_Icc.mpr ⟨le_rfl, hlu⟩
    obtain ⟨q, hq, -⟩ := hmem
    exact ⟨q, hq⟩
  have hstay_out : ∀ q ∈ Q, outcome (Function.update s j (s j)) q = s j := by
    intro q hq
    rw [Function.update_eq_self]
    unfold outcome
    rw [hQw q hq]
  intro x
  rcases lt_trichotomy x (s j) with hx | hx | hx
  · -- A left deviation loses to the edge report at the far-boundary median.
    obtain ⟨qu, hqu, hqmed'⟩ : ∃ q ∈ Q, (fun q => socialMedian s q) q = u := by
      have hmem : u ∈ (fun q => socialMedian s q) '' Q := by
        rw [hM]
        exact Set.mem_Icc.mpr ⟨hlu, le_rfl⟩
      obtain ⟨q, hq, hq'⟩ := hmem
      exact ⟨q, hq, hq'⟩
    have hqmed : socialMedian s qu = u := hqmed'
    have h1 : maxRegretOver pp s j (s j) Q ≤ 2 * (u - s j) := by
      refine maxRegretOver_le hQne fun q hq => ?_
      have hmm : socialMedian s q ∈ Set.Icc ℓ u := by
        rw [← hM]
        exact ⟨q, hq, rfl⟩
      calc regret pp s j (s j) q
          ≤ 2 * (u - socialMedian s q) :=
            winner_stay_regret_le (hQw q hq) (hmed q hq) hedge hpw hmm.2 hwu
        _ ≤ 2 * (u - s j) := by
            have := hmm.1
            linarith
    have h2 : 2 * (u - s j) ≤ regret pp s j x qu := by
      unfold regret
      rw [winner_dev_outcome_edge (hmed qu hqu) hqmed hgap hedge hpw hwu hx]
      have hbd : bestOutcomeDist pp s j qu ≤ s j - pp j := by
        have h := bestOutcomeDist_le (pp := pp) (s := s) (j := j) (q := qu)
          (s j)
        rw [hstay_out qu hqu, abs_of_pos (by linarith)] at h
        exact h
      rw [abs_of_pos (show (0:ℝ) < 2 * u - s j - pp j by linarith)]
      linarith
    calc maxRegretOver pp s j (s j) Q ≤ 2 * (u - s j) := h1
      _ ≤ regret pp s j x qu := h2
      _ ≤ maxRegretOver pp s j x Q := regret_le_maxRegretOver hqu
  · rw [hx]
  · -- A right deviation is dominated pointwise: its outcome is the deviation
    -- itself or another's report, both weakly farther from the peak.
    refine maxRegretOver_le hQne fun q hq => ?_
    have hbo : s j - pp j ≤ |outcome (Function.update s j x) q - pp j| := by
      unfold outcome winner
      set d := delegate (Function.update s j x)
        (socialMedian (Function.update s j x) q) with hd
      by_cases hdj : d = j
      · rw [hdj, Function.update_self]
        calc s j - pp j ≤ x - pp j := by linarith
          _ ≤ |x - pp j| := le_abs_self _
      · rw [Function.update_of_ne hdj]
        rcases hgap d hdj with hL | hR
        · calc s j - pp j ≤ -(s d - pp j) := by linarith
            _ ≤ |s d - pp j| := neg_le_abs _
        · calc s j - pp j ≤ s d - pp j := by linarith
            _ ≤ |s d - pp j| := le_abs_self _
    have hpt : regret pp s j (s j) q ≤ regret pp s j x q := by
      unfold regret
      rw [hstay_out q hq, abs_of_pos (show (0:ℝ) < s j - pp j by linarith)]
      linarith
    exact hpt.trans (regret_le_maxRegretOver hq)

/-- **The inside-peak alternative to Theorem 4's boundary case.**  When the
proxy's peak strictly beats the winner at every consistent median, reporting
the peak wins everywhere and is minimax-regret with zero maximal regret —
the boundary is then not minimax (see the `insidePeak*` configuration in
`GameTheory.Mechanism.ProxyVoting.Counterexamples`), which is why
`maxRegretOver_boundary_lt` needs the peak weakly outside the winning
interval. -/
theorem isMinimaxRegret_peak_of_forall_lt {Q : Set (F → ℝ)} {jw : P}
    (hQw : ∀ q ∈ Q, winner s q = jw) (hj : jw ≠ j)
    (hmed : ∀ q ∈ Q, ∀ y, socialMedian (Function.update s j y) q
      = socialMedian s q)
    (hQne : Q.Nonempty)
    (hwin : ∀ q ∈ Q, |pp j - socialMedian s q|
      < |outcome s q - socialMedian s q|) :
    IsMinimaxRegret pp s Q j (pp j) := by
  intro r'
  have hzero : maxRegretOver pp s j (pp j) Q ≤ 0 := by
    refine maxRegretOver_le hQne fun q hq => ?_
    have hwq : winner s q ≠ j := by
      rw [hQw q hq]
      exact hj
    have hout : outcome (Function.update s j (pp j)) q = pp j := by
      rw [outcome_update_eq_duelOutcome hwq (hmed q hq (pp j))
        (ne_of_lt (hwin q hq))]
      exact duelOutcome_of_lt (hwin q hq)
    unfold regret
    rw [hout, sub_self, abs_zero]
    have := bestOutcomeDist_nonneg (pp := pp) (s := s) (j := j) (q := q)
    linarith
  exact le_trans hzero (maxRegretOver_nonneg Q)

/-! ## Realizing the median uncertainty

The assembly theorems take the median-achievability hypothesis `hM` as given.
With strictly more followers than proxies it can be discharged
constructively: point-mass follower profiles realize every median in the
target interval, cannot have their median moved by any single proxy, and
keep the winner fixed as long as the delegate is constant on the interval —
the last being forced anyway by consistency with the observed winner, since
the winner at a profile depends only on its median. -/

/-- The point-mass follower profiles with common position in `[ℓ, u]` — the
canonical median-robust realization of the median uncertainty interval. -/
def constProfiles (F : Type*) (ℓ u : ℝ) : Set (F → ℝ) :=
  {q | ∃ μ ∈ Set.Icc ℓ u, q = fun _ => μ}

private theorem winner_constProfiles (hcard : Fintype.card P < Fintype.card F)
    {jw : P} {ℓ u : ℝ} (hdel : ∀ μ ∈ Set.Icc ℓ u, delegate s μ = jw) :
    ∀ q ∈ constProfiles F ℓ u, winner s q = jw := by
  rintro q ⟨μ, hμ, rfl⟩
  show winner s (fun _ => μ) = jw
  unfold winner
  rw [socialMedian_const hcard s μ]
  exact hdel μ hμ

private theorem socialMedian_update_constProfiles
    (hcard : Fintype.card P < Fintype.card F) {ℓ u : ℝ} :
    ∀ q ∈ constProfiles F ℓ u, ∀ y,
      socialMedian (Function.update s j y) q = socialMedian s q := by
  rintro q ⟨μ, -, rfl⟩ y
  show socialMedian (Function.update s j y) (fun _ => μ)
    = socialMedian s (fun _ => μ)
  rw [socialMedian_const hcard s μ, socialMedian_const hcard _ μ]

private theorem image_socialMedian_constProfiles
    (hcard : Fintype.card P < Fintype.card F) {ℓ u : ℝ} :
    (fun q => socialMedian s q) '' constProfiles F ℓ u = Set.Icc ℓ u := by
  ext ν
  constructor
  · rintro ⟨q, ⟨μ, hμ, rfl⟩, rfl⟩
    change socialMedian s (fun _ => μ) ∈ Set.Icc ℓ u
    rw [socialMedian_const hcard s μ]
    exact hμ
  · intro hν
    exact ⟨fun _ => ν, ⟨ν, hν, rfl⟩, socialMedian_const hcard s ν⟩

/-- **Theorem 4, constructively realized.**  With strictly more followers
than proxies, over the point-mass information set the near boundary of the
median uncertainty is the unique minimax-regret report. -/
theorem isMinimaxRegret_constProfiles_iff_eq_left_boundary
    (hcard : Fintype.card P < Fintype.card F) {jw : P} {ℓ u : ℝ}
    (hdel : ∀ μ ∈ Set.Icc ℓ u, delegate s μ = jw) (hj : jw ≠ j)
    (hp : pp j ≤ 2 * ℓ - s jw) (hlw : ℓ < s jw) (hu : (ℓ + s jw) / 2 ≤ u)
    {r : ℝ} :
    IsMinimaxRegret pp s (constProfiles F ℓ u) j r ↔ r = ℓ :=
  isMinimaxRegret_iff_eq_left_boundary (winner_constProfiles hcard hdel) hj
    (socialMedian_update_constProfiles hcard)
    (image_socialMedian_constProfiles hcard) hp hlw hu

/-- Mirror of `isMinimaxRegret_constProfiles_iff_eq_left_boundary` at the
right boundary. -/
theorem isMinimaxRegret_constProfiles_iff_eq_right_boundary
    (hcard : Fintype.card P < Fintype.card F) {jw : P} {ℓ u : ℝ}
    (hdel : ∀ μ ∈ Set.Icc ℓ u, delegate s μ = jw) (hj : jw ≠ j)
    (hp : 2 * u - s jw ≤ pp j) (hwu : s jw < u) (hl : ℓ ≤ (u + s jw) / 2)
    {r : ℝ} :
    IsMinimaxRegret pp s (constProfiles F ℓ u) j r ↔ r = u :=
  isMinimaxRegret_iff_eq_right_boundary (winner_constProfiles hcard hdel) hj
    (socialMedian_update_constProfiles hcard)
    (image_socialMedian_constProfiles hcard) hp hwu hl

/-- **The winning proxy's winner-stay case, constructively realized**: over
the point-mass information set, staying put is minimax-regret for a winner
off its peak under the gap and edge hypotheses. -/
theorem isMinimaxRegret_winner_stay_constProfiles
    (hcard : Fintype.card P < Fintype.card F) {ℓ u : ℝ}
    (hdel : ∀ μ ∈ Set.Icc ℓ u, delegate s μ = j)
    (hpw : pp j < s j) (hwl : s j ≤ ℓ) (hlu : ℓ ≤ u)
    (hgap : ∀ k, k ≠ j → s k ≤ 2 * pp j - s j ∨ 2 * u - s j ≤ s k)
    (hedge : ∃ k, k ≠ j ∧ s k = 2 * u - s j) :
    IsMinimaxRegret pp s (constProfiles F ℓ u) j (s j) :=
  isMinimaxRegret_winner_stay (winner_constProfiles hcard hdel)
    (socialMedian_update_constProfiles hcard)
    (image_socialMedian_constProfiles hcard) hpw hwl hlu hgap hedge

/-! ### Concrete minimax-regret witnesses -/

/-- A small instance satisfying the left-boundary minimax hypotheses:
the winner reports `2`, the non-winner reports far left, and the possible
medians are `[0,1]`. -/
def boundaryMinimaxPeaks : Fin 2 → ℝ
  | 0 => 2
  | 1 => -3

/-- State for `boundaryMinimaxPeaks`: proxy `0` wins throughout `[0,1]`. -/
def boundaryMinimaxState : Fin 2 → ℝ
  | 0 => 2
  | 1 => -100

private theorem boundaryMinimax_card :
    Fintype.card (Fin 2) < Fintype.card (Fin 3) := by
  simp

private theorem boundaryMinimax_delegate (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    delegate boundaryMinimaxState μ = 0 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_lt fun i hi => ?_
  rcases h2 i with h0 | h1
  · exact absurd h0 hi
  · rw [h1]
    have hμ0 : 0 ≤ μ := hμ.1
    have hμ1 : μ ≤ 1 := hμ.2
    rw [show boundaryMinimaxState 0 = 2 by rfl,
      show boundaryMinimaxState 1 = -100 by rfl,
      abs_of_nonneg (by linarith : 2 - μ ≥ 0),
      abs_of_nonpos (by linarith : -100 - μ ≤ 0)]
    linarith

/-- Concrete non-vacuity witness for the non-winning-proxy
minimax-regret theorem: the unique minimax-regret report is the boundary
`0`. -/
theorem boundaryMinimax_example :
    IsMinimaxRegret boundaryMinimaxPeaks boundaryMinimaxState
      (constProfiles (Fin 3) 0 1) 1 0 := by
  rw [isMinimaxRegret_constProfiles_iff_eq_left_boundary
    (pp := boundaryMinimaxPeaks) (s := boundaryMinimaxState)
    boundaryMinimax_card boundaryMinimax_delegate (by decide)
    (by norm_num [boundaryMinimaxPeaks, boundaryMinimaxState])
    (by norm_num [boundaryMinimaxState])
    (by norm_num [boundaryMinimaxState])]

/-- A small winner-stay instance: proxy `0` wins at report `0`, has peak
`-1`, the other report realizes the reflected far boundary `2`, and the
possible medians are `[0,1]`. -/
def winnerStayMinimaxPeaks : Fin 2 → ℝ
  | 0 => -1
  | 1 => 2

/-- State for `winnerStayMinimaxPeaks`. -/
def winnerStayMinimaxState : Fin 2 → ℝ
  | 0 => 0
  | 1 => 2

private theorem winnerStayMinimax_delegate (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    delegate winnerStayMinimaxState μ = 0 := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  refine delegate_eq_of_forall_le_of_forall_lt (fun i => ?_) (fun i hi => ?_)
  · rcases h2 i with h0 | h1
    · rw [h0]
    · rw [h1]
      have hμ0 : 0 ≤ μ := hμ.1
      have hμ1 : μ ≤ 1 := hμ.2
      rw [show winnerStayMinimaxState 0 = 0 by rfl,
        show winnerStayMinimaxState 1 = 2 by rfl,
        abs_of_nonpos (by linarith : 0 - μ ≤ 0),
        abs_of_nonneg (by linarith : 2 - μ ≥ 0)]
      linarith
  · exact absurd hi (Fin.not_lt_zero i)

/-- Concrete non-vacuity witness for the winner-stay
minimax-regret theorem: staying at `0` is minimax-regret. -/
theorem winnerStayMinimax_example :
    IsMinimaxRegret winnerStayMinimaxPeaks winnerStayMinimaxState
      (constProfiles (Fin 3) 0 1) 0 0 := by
  refine isMinimaxRegret_winner_stay_constProfiles
    (pp := winnerStayMinimaxPeaks) (s := winnerStayMinimaxState)
    boundaryMinimax_card winnerStayMinimax_delegate
    (by norm_num [winnerStayMinimaxPeaks, winnerStayMinimaxState])
    (by norm_num [winnerStayMinimaxState])
    (by norm_num)
    ?_ ?_
  · intro k hk
    fin_cases k
    · exact absurd rfl hk
    · right
      norm_num [winnerStayMinimaxPeaks, winnerStayMinimaxState]
  · exact ⟨1, by decide, by norm_num [winnerStayMinimaxState]⟩

/-! ## The median interval of a winner observation

The paper's uncertainty interval `I^t` is, at a single observation, the set
of medians consistent with the observed winner.  Under follower majority
this set is exactly the winner's delegate cell — every point of the cell is
realized by a point-mass profile, and the winner at a profile depends only
on its median — and the cell is order-convex, so the uncertainty is indeed
an interval, with boundary membership determined by the tie-break.  The
history-level refinement of `I^t` is formalized in the next section. -/

/-- Under follower majority, the consistent medians of a winner observation
are exactly the winner's delegate cell. -/
theorem image_socialMedian_winnerInfoSet
    (hcard : Fintype.card P < Fintype.card F) (s : P → ℝ) (jw : P) :
    (fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw
      = {m | delegate s m = jw} := by
  ext m
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hm
    refine ⟨fun _ => m, ?_, socialMedian_const hcard s m⟩
    change winner s (fun _ => m) = jw
    unfold winner
    rw [socialMedian_const hcard s m]
    exact hm

/-- The observed winner's median uncertainty interval, in the open-endpoint
case where both nearest-neighbor midpoint ties break away from the winner. -/
theorem image_socialMedian_winnerInfoSet_eq_Ioo_of_neighbor_bounds
    (hcard : Fintype.card P < Fintype.card F) {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hlprio : jl < jw) (hrprio : jr < jw)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    (fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw
      = Set.Ioo ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  rw [image_socialMedian_winnerInfoSet (F := F) hcard s jw]
  exact setOf_delegate_eq_eq_Ioo_of_neighbor_bounds hlpos hrpos hleft hright
    hlprio hrprio hneq

/-- The observed winner's median uncertainty interval, in the closed-endpoint
case where both nearest-neighbor midpoint ties break toward the winner. -/
theorem image_socialMedian_winnerInfoSet_eq_Icc_of_neighbor_bounds
    (hcard : Fintype.card P < Fintype.card F) {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hleftLowerStrict : ∀ k, k < jw → s k < s jw → s k < s jl)
    (hrightLowerStrict : ∀ k, k < jw → s jw < s k → s jr < s k)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    (fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw
      = Set.Icc ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  rw [image_socialMedian_winnerInfoSet (F := F) hcard s jw]
  exact setOf_delegate_eq_eq_Icc_of_neighbor_bounds hlpos hrpos hleft hright
    hleftLowerStrict hrightLowerStrict hneq

/-- The observed winner's median uncertainty interval, with the left endpoint
closed and the right endpoint open. -/
theorem image_socialMedian_winnerInfoSet_eq_Ico_of_neighbor_bounds
    (hcard : Fintype.card P < Fintype.card F) {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hleftLowerStrict : ∀ k, k < jw → s k < s jw → s k < s jl)
    (hrprio : jr < jw)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    (fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw
      = Set.Ico ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  rw [image_socialMedian_winnerInfoSet (F := F) hcard s jw]
  exact setOf_delegate_eq_eq_Ico_of_neighbor_bounds hlpos hrpos hleft hright
    hleftLowerStrict hrprio hneq

/-- The observed winner's median uncertainty interval, with the left endpoint
open and the right endpoint closed. -/
theorem image_socialMedian_winnerInfoSet_eq_Ioc_of_neighbor_bounds
    (hcard : Fintype.card P < Fintype.card F) {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hlprio : jl < jw)
    (hrightLowerStrict : ∀ k, k < jw → s jw < s k → s jr < s k)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    (fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw
      = Set.Ioc ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  rw [image_socialMedian_winnerInfoSet (F := F) hcard s jw]
  exact setOf_delegate_eq_eq_Ioc_of_neighbor_bounds hlpos hrpos hleft hright
    hlprio hrightLowerStrict hneq

/-- The median uncertainty of a winner observation is an interval. -/
theorem ordConnected_image_socialMedian_winnerInfoSet
    (hcard : Fintype.card P < Fintype.card F) (s : P → ℝ) (jw : P) :
    Set.OrdConnected
      ((fun q => socialMedian s q) '' winnerInfoSet (F := F) s jw) := by
  rw [image_socialMedian_winnerInfoSet hcard]
  exact ordConnected_setOf_delegate_eq jw

/-! ## The median interval along an observation history

The paper's interval `Iᵗ` refines recursively along the play: each new
winner observation intersects the current uncertainty with the new winner's
information set (`historyInfoSet_succ`), and strong-monotone steps keep
every consistent profile's median fixed
(`socialMedian_eq_of_isStrongMonotoneHistoryDynamics`), so the refinement
tracks a well-defined quantity.  Under follower majority the uncertainty
after `t` observations is exactly the intersection of the observed winners'
delegate cells (`image_socialMedian_historyInfoSet`), an interval.

The paper's second refinement rule — a winner that moved rightward reveals
the median to be weakly right of its new report — is sound only for movers
weakly left of every consistent median
(`StrongMonotoneOver.report_le_socialMedian`); a mover on the right of the
median may move farther right, strong-monotonically and as a dominating
manipulation, and the rule would then exclude every consistent profile —
see the `moveRight*` configuration in
`GameTheory.Mechanism.ProxyVoting.Counterexamples`. -/

/-- **Section 5's opening claim, verified**: with no information — the
information set is every follower profile — no report is a dominating
manipulation at the truthful state, under follower majority and distinct
peaks.  The refuting witness is the point-mass profile at the proxy's own
peak, where truthful play already wins exactly and any deviation lands the
outcome on the deviation itself or on another proxy's peak. -/
theorem not_dominatesOver_univ_of_truthful
    (hcard : Fintype.card P < Fintype.card F)
    (hpk : ∀ k, k ≠ j → pp k ≠ pp j) (r : ℝ) :
    ¬ DominatesOver pp pp (Set.univ : Set (F → ℝ)) j r := by
  rintro ⟨hweak, q₁, -, hstrict⟩
  by_cases hr : r = pp j
  · rw [hr, Function.update_eq_self] at hstrict
    exact absurd hstrict (lt_irrefl _)
  · have hdel : delegate pp (pp j) = j := by
      refine delegate_eq_of_forall_lt fun k hk => ?_
      rw [sub_self, abs_zero]
      exact abs_pos.mpr (sub_ne_zero.mpr (hpk k hk))
    have hout : outcome pp (fun _ : F => pp j) = pp j := by
      unfold outcome winner
      rw [socialMedian_const hcard pp (pp j), hdel]
    have hw := hweak (fun _ : F => pp j) (Set.mem_univ _)
    rw [hout, sub_self, abs_zero] at hw
    have heq : outcome (Function.update pp j r) (fun _ : F => pp j)
        = pp j := by
      have h0 := abs_nonneg
        (outcome (Function.update pp j r) (fun _ : F => pp j) - pp j)
      have h1 : |outcome (Function.update pp j r) (fun _ : F => pp j) - pp j|
          = 0 := le_antisymm hw h0
      exact sub_eq_zero.mp (abs_eq_zero.mp h1)
    unfold outcome winner at heq
    by_cases hdj : delegate (Function.update pp j r)
        (socialMedian (Function.update pp j r) (fun _ : F => pp j)) = j
    · rw [hdj, Function.update_self] at heq
      exact hr heq
    · rw [Function.update_of_ne hdj] at heq
      exact hpk _ hdj heq

omit [LinearOrder P] in
/-- A strong-monotone report over a superset of profiles is strong-monotone
over the subset. -/
theorem StrongMonotoneOver.mono {Q Q' : Set (F → ℝ)}
    (h : StrongMonotoneOver s Q j r) (hQ : Q' ⊆ Q) :
    StrongMonotoneOver s Q' j r :=
  fun q hq => h q (hQ hq)

omit [LinearOrder P] in
/-- Weak non-crossing over a superset of profiles is weak non-crossing over
the subset. -/
theorem WeakStrongMonotoneOver.mono {Q Q' : Set (F → ℝ)}
    (h : WeakStrongMonotoneOver s Q j r) (hQ : Q' ⊆ Q) :
    WeakStrongMonotoneOver s Q' j r :=
  fun q hq => h q (hQ hq)

omit [LinearOrder P] in
/-- **The sound half of the paper's winner-moved refinement**: a
strong-monotone report stays weakly on its old report's side of every
consistent median — whichever direction it moved. -/
theorem StrongMonotoneOver.report_le_socialMedian {Q : Set (F → ℝ)}
    (h : StrongMonotoneOver s Q j r)
    (hold : ∀ q ∈ Q, s j ≤ socialMedian s q) :
    ∀ q ∈ Q, r ≤ socialMedian s q := by
  intro q hq
  obtain ⟨h1, -, h3⟩ := h q hq
  rcases lt_or_eq_of_le (hold q hq) with hlt | heq
  · exact le_of_lt (h1 hlt)
  · exact le_of_eq (h3 heq)

omit [LinearOrder P] in
/-- Mirror of `StrongMonotoneOver.report_le_socialMedian`. -/
theorem StrongMonotoneOver.socialMedian_le_report {Q : Set (F → ℝ)}
    (h : StrongMonotoneOver s Q j r)
    (hold : ∀ q ∈ Q, socialMedian s q ≤ s j) :
    ∀ q ∈ Q, socialMedian s q ≤ r := by
  intro q hq
  obtain ⟨-, h2, h3⟩ := h q hq
  rcases lt_or_eq_of_le (hold q hq) with hlt | heq
  · exact le_of_lt (h2 hlt)
  · exact le_of_eq (h3 heq.symm).symm

/-- The follower profiles consistent with every winner observation along
the realized play up to time `t`. -/
def historyInfoSet (q : F → ℝ) (σ : ℕ → P → ℝ) (t : ℕ) : Set (F → ℝ) :=
  {q' | ∀ t' ≤ t, winner (σ t') q' = winner (σ t') q}

/-- The true profile is consistent with its own observation history. -/
theorem mem_historyInfoSet_self (q : F → ℝ) (σ : ℕ → P → ℝ) (t : ℕ) :
    q ∈ historyInfoSet q σ t :=
  fun _ _ => rfl

/-- Observation histories only refine. -/
theorem historyInfoSet_antitone (q : F → ℝ) (σ : ℕ → P → ℝ) :
    Antitone (historyInfoSet q σ) :=
  fun _ _ h _ hq' t' ht' => hq' t' (le_trans ht' h)

/-- **The recursion's observation step**: each new observation intersects
the history with the new winner's information set. -/
theorem historyInfoSet_succ (q : F → ℝ) (σ : ℕ → P → ℝ) (t : ℕ) :
    historyInfoSet q σ (t + 1)
      = historyInfoSet q σ t
          ∩ winnerInfoSet (σ (t + 1)) (winner (σ (t + 1)) q) := by
  ext q'
  constructor
  · intro hq'
    exact ⟨fun t' ht' => hq' t' (le_trans ht' (Nat.le_succ t)),
      hq' (t + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ t' ht'
    rcases eq_or_lt_of_le ht' with h | h
    · rw [h]
      exact h2
    · exact h1 t' (Nat.lt_succ_iff.mp h)

/-- Strong-monotone dynamics with respect to the accumulated history: each
step is strong-monotone over the profiles consistent with every observation
so far.  Weaker than `IsStrongMonotoneDynamics`, which constrains each step
against the current observation alone — the refinement relaxes the
constraint over time. -/
def IsStrongMonotoneHistoryDynamics (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  ∀ t, (∃ j r, StrongMonotoneOver (σ t) (historyInfoSet q σ t) j r
      ∧ σ (t + 1) = Function.update (σ t) j r)
    ∨ σ (t + 1) = σ t

/-- Weak non-crossing dynamics with respect to the accumulated history. -/
def IsWeakStrongMonotoneHistoryDynamics (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  ∀ t, (∃ j r, WeakStrongMonotoneOver (σ t) (historyInfoSet q σ t) j r
      ∧ σ (t + 1) = Function.update (σ t) j r)
    ∨ σ (t + 1) = σ t

/-- Active minimax-regret dynamics relative to an explicit sequence of
information sets.  This is the theorem-4 abstraction: each step chooses an
actual minimax-regret report for the currently assigned information set.
Separate hypotheses may say that the information sets are nested, contain the
true profile, or come from an observation history. -/
def IsMinimaxRegretInfoDynamics
    (pp : P → ℝ) (σ : ℕ → P → ℝ) (Q : ℕ → Set (F → ℝ)) : Prop :=
  ∀ t, ∃ j r, IsMinimaxRegret pp (σ t) (Q t) j r
    ∧ σ (t + 1) = Function.update (σ t) j r

/-- Current-observation strong-monotonicity implies the history version. -/
theorem IsStrongMonotoneDynamics.isStrongMonotoneHistoryDynamics
    {q : F → ℝ} {σ : ℕ → P → ℝ} (h : IsStrongMonotoneDynamics q σ) :
    IsStrongMonotoneHistoryDynamics q σ := by
  intro t
  rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
  · exact Or.inl ⟨j, r, hsm.mono fun q' hq' => hq' t le_rfl, hupd⟩
  · exact Or.inr hrest

/-- Current-observation weak non-crossing implies the history version. -/
theorem IsWeakStrongMonotoneDynamics.isWeakStrongMonotoneHistoryDynamics
    {q : F → ℝ} {σ : ℕ → P → ℝ} (h : IsWeakStrongMonotoneDynamics q σ) :
    IsWeakStrongMonotoneHistoryDynamics q σ := by
  intro t
  rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
  · exact Or.inl ⟨j, r, hsm.mono fun q' hq' => hq' t le_rfl, hupd⟩
  · exact Or.inr hrest

/-- Strict history-strong-monotone dynamics are weak history dynamics. -/
theorem IsStrongMonotoneHistoryDynamics.weak
    {q : F → ℝ} {σ : ℕ → P → ℝ} (h : IsStrongMonotoneHistoryDynamics q σ) :
    IsWeakStrongMonotoneHistoryDynamics q σ := by
  intro t
  rcases h t with ⟨j, r, hsm, hupd⟩ | hrest
  · exact Or.inl ⟨j, r, hsm.weak, hupd⟩
  · exact Or.inr hrest

/-- **Median invariance across the history**: along a history-strong-monotone
play, every profile consistent with the history keeps its population median
at every state it has been consistent with — the quantity the paper's
interval `Iᵗ` tracks is well defined. -/
theorem socialMedian_eq_of_isStrongMonotoneHistoryDynamics
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsStrongMonotoneHistoryDynamics q σ) {t : ℕ} {q' : F → ℝ}
    (hq' : q' ∈ historyInfoSet q σ t) :
    ∀ t' ≤ t, socialMedian (σ t') q' = socialMedian (σ 0) q' := by
  intro t'
  induction t' with
  | zero => intro _; rfl
  | succ n ih =>
      intro hst
      have hn : n ≤ t := le_trans (Nat.le_succ n) hst
      rcases h n with ⟨j, r, hsm, hupd⟩ | hrest
      · rw [hupd, socialMedian_update_eq_of_strongMonotoneOver hsm
          (historyInfoSet_antitone q σ hn hq')]
        exact ih hn
      · rw [hrest]
        exact ih hn

/-- Weak history median invariance: along a history-weak-non-crossing play,
every profile consistent with the history keeps its population median at every
state it has been consistent with. -/
theorem socialMedian_eq_of_isWeakStrongMonotoneHistoryDynamics
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsWeakStrongMonotoneHistoryDynamics q σ) {t : ℕ} {q' : F → ℝ}
    (hq' : q' ∈ historyInfoSet q σ t) :
    ∀ t' ≤ t, socialMedian (σ t') q' = socialMedian (σ 0) q' := by
  intro t'
  induction t' with
  | zero => intro _; rfl
  | succ n ih =>
      intro hst
      have hn : n ≤ t := le_trans (Nat.le_succ n) hst
      rcases h n with ⟨j, r, hsm, hupd⟩ | hrest
      · rw [hupd, socialMedian_update_eq_of_weakStrongMonotoneOver hsm
          (historyInfoSet_antitone q σ hn hq')]
        exact ih hn
      · rw [hrest]
        exact ih hn

/-- History-weak-non-crossing dynamics preserve the true profile's own
population median at every time. -/
theorem socialMedian_true_eq_of_isWeakStrongMonotoneHistoryDynamics
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsWeakStrongMonotoneHistoryDynamics q σ) (t : ℕ) :
    socialMedian (σ t) q = socialMedian (σ 0) q :=
  socialMedian_eq_of_isWeakStrongMonotoneHistoryDynamics h
    (mem_historyInfoSet_self q σ t) t le_rfl

/-- History-level partial-information convergence theorem.  If a
history-weak-non-crossing play has windowed fixed-factor contraction of the
outcome distance to its current median, then the outcome converges to the
initial true median. -/
theorem tendsto_outcome_of_weakStrongMonotoneHistory_windowed_contraction
    {q : F → ℝ} {σ : ℕ → P → ℝ} {b : ℕ → ℕ} {α : ℝ}
    (h : IsWeakStrongMonotoneHistoryDynamics q σ)
    (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hwindow : ∀ k u, b k ≤ u → u ≤ b (k + 1) →
      |outcome (σ u) q - socialMedian (σ u) q|
        ≤ |outcome (σ (b k)) q - socialMedian (σ (b k)) q|)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbig : ∀ k, ∃ k', k ≤ k' ∧
      |outcome (σ (b (k' + 1))) q - socialMedian (σ (b (k' + 1))) q|
        ≤ α * |outcome (σ (b k')) q - socialMedian (σ (b k')) q|) :
    Filter.Tendsto (fun t => outcome (σ t) q) Filter.atTop
      (nhds (socialMedian (σ 0) q)) := by
  refine tendsto_outcome_of_windowed_contraction
    (pp := σ 0) (q := q) (σ := σ) (b := b) (α := α)
    hb0 hbmono htop ?_ hα0 hα1 ?_
  · intro k u hku huk
    simpa [socialMedian_true_eq_of_isWeakStrongMonotoneHistoryDynamics h u,
      socialMedian_true_eq_of_isWeakStrongMonotoneHistoryDynamics h (b k)]
      using hwindow k u hku huk
  · intro k
    obtain ⟨k', hkk', hstep⟩ := hbig k
    refine ⟨k', hkk', ?_⟩
    simpa [socialMedian_true_eq_of_isWeakStrongMonotoneHistoryDynamics h (b (k' + 1)),
      socialMedian_true_eq_of_isWeakStrongMonotoneHistoryDynamics h (b k')]
      using hstep

/-- **The paper's interval `Iᵗ`, semantically.**  Under follower majority,
the median uncertainty after `t` observations of a history-strong-monotone
play is exactly the intersection of the observed winners' delegate cells. -/
theorem image_socialMedian_historyInfoSet
    (hcard : Fintype.card P < Fintype.card F)
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsStrongMonotoneHistoryDynamics q σ) (t : ℕ) :
    (fun q' => socialMedian (σ 0) q') '' historyInfoSet q σ t
      = {m | ∀ t' ≤ t, delegate (σ t') m = winner (σ t') q} := by
  ext m
  constructor
  · rintro ⟨q', hq', rfl⟩
    intro t' ht'
    have hmed := socialMedian_eq_of_isStrongMonotoneHistoryDynamics h hq' t' ht'
    change delegate (σ t') (socialMedian (σ 0) q') = winner (σ t') q
    rw [← hmed]
    exact hq' t' ht'
  · intro hm
    refine ⟨fun _ => m, ?_, socialMedian_const hcard (σ 0) m⟩
    intro t' ht'
    change winner (σ t') (fun _ => m) = winner (σ t') q
    unfold winner
    rw [socialMedian_const hcard (σ t') m]
    exact hm t' ht'

/-- Weak non-crossing version of `image_socialMedian_historyInfoSet`.  This is
the semantic interval theorem needed for boundary minimax-regret dynamics,
where reports can land exactly on an endpoint of the consistent-median
interval. -/
theorem image_socialMedian_historyInfoSet_of_weak
    (hcard : Fintype.card P < Fintype.card F)
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsWeakStrongMonotoneHistoryDynamics q σ) (t : ℕ) :
    (fun q' => socialMedian (σ 0) q') '' historyInfoSet q σ t
      = {m | ∀ t' ≤ t, delegate (σ t') m = winner (σ t') q} := by
  ext m
  constructor
  · rintro ⟨q', hq', rfl⟩
    intro t' ht'
    have hmed := socialMedian_eq_of_isWeakStrongMonotoneHistoryDynamics h hq' t' ht'
    change delegate (σ t') (socialMedian (σ 0) q') = winner (σ t') q
    rw [← hmed]
    exact hq' t' ht'
  · intro hm
    refine ⟨fun _ => m, ?_, socialMedian_const hcard (σ 0) m⟩
    intro t' ht'
    change winner (σ t') (fun _ => m) = winner (σ t') q
    unfold winner
    rw [socialMedian_const hcard (σ t') m]
    exact hm t' ht'

/-- An intersection of delegate cells is an interval. -/
theorem ordConnected_setOf_forall_delegate_eq {σ : ℕ → P → ℝ} {jw : ℕ → P}
    (t : ℕ) :
    Set.OrdConnected {m | ∀ t' ≤ t, delegate (σ t') m = jw t'} := by
  constructor
  intro m₁ hm₁ m₂ hm₂ m hm t' ht'
  exact delegate_eq_of_delegate_eq_of_between (hm₁ t' ht') (hm₂ t' ht')
    hm.1 hm.2

/-- The median uncertainty along an observation history is an interval. -/
theorem ordConnected_image_socialMedian_historyInfoSet
    (hcard : Fintype.card P < Fintype.card F)
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsStrongMonotoneHistoryDynamics q σ) (t : ℕ) :
    Set.OrdConnected
      ((fun q' => socialMedian (σ 0) q') '' historyInfoSet q σ t) := by
  rw [image_socialMedian_historyInfoSet hcard h t]
  exact ordConnected_setOf_forall_delegate_eq t

/-- Weak non-crossing version of the history interval theorem. -/
theorem ordConnected_image_socialMedian_historyInfoSet_of_weak
    (hcard : Fintype.card P < Fintype.card F)
    {q : F → ℝ} {σ : ℕ → P → ℝ}
    (h : IsWeakStrongMonotoneHistoryDynamics q σ) (t : ℕ) :
    Set.OrdConnected
      ((fun q' => socialMedian (σ 0) q') '' historyInfoSet q σ t) := by
  rw [image_socialMedian_historyInfoSet_of_weak hcard h t]
  exact ordConnected_setOf_forall_delegate_eq t

end ProxyVoting

end GameTheory
