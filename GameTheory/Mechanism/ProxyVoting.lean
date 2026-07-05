/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.WeightedMedian
import GameTheory.Mechanism.EuclideanPreference
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-!
# Strategic proxy voting on the line

Bielous–Meir strategic proxy games: a finite set of proxies reports positions
on the real line, and each follower delegates their vote to the nearest proxy
(the Tullock delegation model), with ties broken by a fixed order on proxies.
The *weighted median* rule elects the proxy whose reported position is a
weighted median of the reported positions under delegation weights.

The formalization takes the population-median characterization as the rule's
canonical tie-breaking: `winner` elects the proxy nearest the canonical
median of the full population of proxy reports and follower positions, and
`winner_isWMWinner` certifies that this selection satisfies the weighted-median
defining predicate.  Weighted medians are not unique (they form an interval),
so this is one legitimate deterministic selection among them; every theorem
below is about this selection.

## Main results

* `winner_isWMWinner` — Lemma 1 (Cohensius et al. 2017): the proxy nearest the
  population median is a weighted median of the proxy reports under delegation
  weights.
* `follower_strategyproof` — Theorem 1 (Bielous–Meir): the weighted median rule
  is strategyproof with respect to follower positions.
* `proxy_manipulation_iff` — Theorem 2 (Bielous–Meir): in the truthful state
  some proxy has a manipulation iff no proxy sits at the population median and
  proxies are present on both sides of it.
-/

namespace GameTheory

namespace ProxyVoting

open Finset

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]

/-! ## Delegation -/

omit [LinearOrder P] in
/-- The nearest-proxy candidates at a position: proxies whose reported position
minimizes the distance to `x`. -/
theorem delegateCandidates_nonempty (s : P → ℝ) (x : ℝ) :
    (univ.filter fun j => ∀ k, |s j - x| ≤ |s k - x|).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image univ (fun j => |s j - x|) univ_nonempty
  exact ⟨j, mem_filter.mpr ⟨mem_univ j, fun k => hj k (mem_univ k)⟩⟩

/-- Tullock delegation: the proxy with reported position nearest to `x`, ties
broken by the proxy order. -/
noncomputable def delegate (s : P → ℝ) (x : ℝ) : P :=
  (univ.filter fun j => ∀ k, |s j - x| ≤ |s k - x|).min'
    (delegateCandidates_nonempty s x)

theorem delegate_dist_le (s : P → ℝ) (x : ℝ) (k : P) :
    |s (delegate s x) - x| ≤ |s k - x| :=
  (mem_filter.mp (Finset.min'_mem _ (delegateCandidates_nonempty s x))).2 k

section Geometry

variable {s : P → ℝ}

private theorem two_mul_le_add_of_abs_le {a b x : ℝ} (hab : a < b)
    (h : |a - x| ≤ |b - x|) : 2 * x ≤ a + b := by
  rcases abs_cases (a - x) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rcases abs_cases (b - x) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rw [ha, hb] at h <;> linarith

private theorem add_le_two_mul_of_abs_le {a b y : ℝ} (hab : a < b)
    (h : |b - y| ≤ |a - y|) : a + b ≤ 2 * y := by
  rcases abs_cases (a - y) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rcases abs_cases (b - y) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rw [ha, hb] at h <;> linarith

/-- For two positions `a < b`, being weakly closer to `b` than to `a` is the
right closed half-line from their midpoint. -/
theorem abs_right_sub_le_abs_left_sub_iff {a b m : ℝ} (hab : a < b) :
    |b - m| ≤ |a - m| ↔ (a + b) / 2 ≤ m := by
  constructor
  · intro h
    have h2 := add_le_two_mul_of_abs_le hab h
    linarith
  · intro hm
    rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        rw [hb, ha] <;> linarith

/-- Strict version of `abs_right_sub_le_abs_left_sub_iff`. -/
theorem abs_right_sub_lt_abs_left_sub_iff {a b m : ℝ} (hab : a < b) :
    |b - m| < |a - m| ↔ (a + b) / 2 < m := by
  constructor
  · intro h
    rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        rw [hb, ha] at h <;> linarith
  · intro hm
    rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        rw [hb, ha] <;> linarith

/-- For two positions `a < b`, being weakly closer to `a` than to `b` is the
left closed half-line up to their midpoint. -/
theorem abs_left_sub_le_abs_right_sub_iff {a b m : ℝ} (hab : a < b) :
    |a - m| ≤ |b - m| ↔ m ≤ (a + b) / 2 := by
  constructor
  · intro h
    have h2 := two_mul_le_add_of_abs_le hab h
    linarith
  · intro hm
    rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
        rw [ha, hb] <;> linarith

/-- Strict version of `abs_left_sub_le_abs_right_sub_iff`. -/
theorem abs_left_sub_lt_abs_right_sub_iff {a b m : ℝ} (hab : a < b) :
    |a - m| < |b - m| ↔ m < (a + b) / 2 := by
  constructor
  · intro h
    rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
        rw [ha, hb] at h <;> linarith
  · intro hm
    rcases abs_cases (a - m) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (b - m) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
        rw [ha, hb] <;> linarith

/-- If the delegate's position at `x` is strictly below the delegate's position
at `y`, then `x` is strictly below `y`.  In particular the delegate's position
is monotone in the evaluation point. -/
theorem lt_of_delegate_pos_lt {x y : ℝ}
    (h : s (delegate s x) < s (delegate s y)) : x < y := by
  have h1 : |s (delegate s x) - x| ≤ |s (delegate s y) - x| :=
    delegate_dist_le s x _
  have h2 : |s (delegate s y) - y| ≤ |s (delegate s x) - y| :=
    delegate_dist_le s y _
  have hx2 : 2 * x ≤ s (delegate s x) + s (delegate s y) :=
    two_mul_le_add_of_abs_le h h1
  have hy2 : s (delegate s x) + s (delegate s y) ≤ 2 * y :=
    add_le_two_mul_of_abs_le h h2
  rcases eq_or_lt_of_le (by linarith : x ≤ y) with heq | hlt
  · subst heq
    exact absurd h (lt_irrefl _)
  · exact hlt

/-- The delegate's position is monotone in the evaluation point. -/
theorem delegate_pos_mono {x y : ℝ} (h : x ≤ y) :
    s (delegate s x) ≤ s (delegate s y) := by
  by_contra hc
  rw [not_le] at hc
  exact absurd (lt_of_delegate_pos_lt hc) (not_lt.mpr h)

/-- If replacing a report `r` by `p` moves it strictly closer to the evaluation
point `m`, then the nearest selected position after the replacement is either
the new report `p` itself or the same position selected before the replacement.
-/
theorem update_delegate_eq_self_or_eq_of_dist_lt
    {j : P} {m p r : ℝ} (hdist : |p - m| < |r - m|) :
    Function.update s j p (delegate (Function.update s j p) m) = p
      ∨ Function.update s j p (delegate (Function.update s j p) m)
        = Function.update s j r (delegate (Function.update s j r) m) := by
  set st := Function.update s j p
  set sr := Function.update s j r
  set kt := delegate st m
  set kr := delegate sr m
  by_cases hkt : kt = j
  · left
    simp [st, hkt]
  right
  by_cases hkr : kr = j
  · exfalso
    have htj : |st kt - m| ≤ |p - m| := by
      have h := delegate_dist_le st m j
      simpa [kt, st] using h
    have hrkt : |r - m| ≤ |st kt - m| := by
      have h := delegate_dist_le sr m kt
      simpa [kr, sr, st, hkr, hkt] using h
    linarith
  have hkt_same : sr kt = st kt := by
    simp [sr, st, hkt]
  have hkr_same : st kr = sr kr := by
    simp [sr, st, hkr]
  have hle_st : |st kt - m| ≤ |sr kr - m| := by
    have h := delegate_dist_le st m kr
    simpa [kt, hkr_same] using h
  have hle_sr : |sr kr - m| ≤ |st kt - m| := by
    have h := delegate_dist_le sr m kt
    simpa [kr, hkt_same] using h
  have hdist_eq : |sr kr - m| = |st kt - m| := le_antisymm hle_sr hle_st
  have hkt_le_kr : kt ≤ kr := by
    unfold kt
    unfold delegate
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro l
    by_cases hlj : l = j
    · have htj : |st kt - m| ≤ |p - m| := by
        have h := delegate_dist_le st m j
        simpa [kt, st] using h
      have : |st kr - m| ≤ |st kt - m| := by
        rw [hkr_same, hdist_eq]
      rw [show st l = p by simp [st, hlj]]
      exact this.trans htj
    · have h := delegate_dist_le sr m l
      calc
        |st kr - m| = |sr kr - m| := by rw [hkr_same]
        _ ≤ |sr l - m| := by simpa [kr] using h
        _ = |st l - m| := by simp [sr, st, hlj]
  have hkr_le_kt : kr ≤ kt := by
    unfold kr
    unfold delegate
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro l
    by_cases hlj : l = j
    · have htj : |st kt - m| ≤ |p - m| := by
        have h := delegate_dist_le st m j
        simpa [kt, st] using h
      have : |sr kt - m| ≤ |r - m| := by
        rw [hkt_same]
        exact le_of_lt (lt_of_le_of_lt htj hdist)
      rw [show sr l = r by simp [sr, hlj]]
      exact this
    · have h := delegate_dist_le st m l
      calc
        |sr kt - m| = |st kt - m| := by rw [hkt_same]
        _ ≤ |st l - m| := by simpa [kt] using h
        _ = |sr l - m| := by simp [sr, st, hlj]
  have htk : kt = kr := le_antisymm hkt_le_kr hkr_le_kt
  rw [← htk, hkt_same]

/-- After one proxy's report changes, the nearest selected position at the
same evaluation point is either the new report itself or the previously
selected position, provided the updating proxy was not previously selected. -/
theorem update_delegate_eq_new_or_eq_of_delegate_ne
    {j : P} {x m : ℝ} (hkj : delegate s m ≠ j) :
    Function.update s j x (delegate (Function.update s j x) m) = x
      ∨ Function.update s j x (delegate (Function.update s j x) m)
        = s (delegate s m) := by
  set st := Function.update s j x with hst
  set kt := delegate st m with hkt_def
  set kr := delegate s m with hkr_def
  by_cases hkt : kt = j
  · left
    simp [st, hkt]
  right
  have hkt_same : s kt = st kt := by simp [st, hkt]
  have hkr_same : st kr = s kr := by simp [st, hkj]
  have hle_st : |st kt - m| ≤ |s kr - m| := by
    have h := delegate_dist_le st m kr
    simpa [kt, hkr_same] using h
  have hle_sr : |s kr - m| ≤ |st kt - m| := by
    have h := delegate_dist_le s m kt
    simpa [kr, hkt_same] using h
  have hdist_eq : |s kr - m| = |st kt - m| := le_antisymm hle_sr hle_st
  have hkt_le_kr : kt ≤ kr := by
    unfold kt
    unfold delegate
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro l
    calc |st kr - m| = |s kr - m| := by rw [hkr_same]
      _ = |st kt - m| := hdist_eq
      _ ≤ |st l - m| := by
          have h := delegate_dist_le st m l
          simpa [kt] using h
  have hkr_le_kt : kr ≤ kt := by
    unfold kr
    unfold delegate
    apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro l
    calc |s kt - m| = |st kt - m| := hkt_same ▸ rfl
      _ = |s kr - m| := hdist_eq.symm
      _ ≤ |s l - m| := by
          have h := delegate_dist_le s m l
          simpa [kr] using h
  have htk : kt = kr := le_antisymm hkt_le_kr hkr_le_kt
  rw [← htk, ← hkt_same]

/-- If a report overshoots a left peak away from the median, moving it back to
the peak cannot make the nearest selected position farther from that peak. -/
theorem abs_update_delegate_sub_le_of_left_overshoot
    {j : P} {m p r : ℝ} (hrp : r < p) (hpm : p < m) :
    |Function.update s j p (delegate (Function.update s j p) m) - p|
      ≤ |Function.update s j r (delegate (Function.update s j r) m) - p| := by
  have hdist_pr : |p - m| < |r - m| := by
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  rcases update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := m) (p := p) (r := r) hdist_pr with hself | hsame
  · rw [hself, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [hsame]

/-- If a report overshoots a right peak away from the median, moving it back to
the peak cannot make the nearest selected position farther from that peak. -/
theorem abs_update_delegate_sub_le_of_right_overshoot
    {j : P} {m p r : ℝ} (hmp : m < p) (hpr : p < r) :
    |Function.update s j p (delegate (Function.update s j p) m) - p|
      ≤ |Function.update s j r (delegate (Function.update s j r) m) - p| := by
  have hdist_pr : |p - m| < |r - m| := by
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  rcases update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
      (m := m) (p := p) (r := r) hdist_pr with hself | hsame
  · rw [hself, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [hsame]

/-- A proxy position strictly below the delegate's position at `μ` is strictly
below `μ`. -/
theorem pos_lt_of_lt_delegate_pos {μ : ℝ} {k : P}
    (h : s k < s (delegate s μ)) : s k < μ := by
  by_contra hc
  rw [not_lt] at hc
  have hd := delegate_dist_le s μ k
  rcases abs_cases (s (delegate s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

/-- A proxy position strictly above the delegate's position at `μ` is strictly
above `μ`. -/
theorem pos_gt_of_gt_delegate_pos {μ : ℝ} {k : P}
    (h : s (delegate s μ) < s k) : μ < s k := by
  by_contra hc
  rw [not_lt] at hc
  have hd := delegate_dist_le s μ k
  rcases abs_cases (s (delegate s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

/-- The delegate is the least index attaining the minimum report distance:
weak optimality against everyone plus strict optimality against smaller
indices identify it. -/
theorem delegate_eq_of_forall_le_of_forall_lt {m : ℝ} {k : P}
    (hle : ∀ j, |s k - m| ≤ |s j - m|)
    (hlt : ∀ j < k, |s k - m| < |s j - m|) : delegate s m = k := by
  unfold delegate
  rw [Finset.min'_eq_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hle, fun b hb => ?_⟩
  by_contra hbk
  rw [not_le] at hbk
  exact absurd (hb k) (not_le.mpr (hlt b hbk))

/-- A report strictly nearest the evaluation point is the delegate. -/
theorem delegate_eq_of_forall_lt {m : ℝ} {k : P}
    (h : ∀ j ≠ k, |s k - m| < |s j - m|) : delegate s m = k := by
  refine delegate_eq_of_forall_le_of_forall_lt (fun j => ?_)
    (fun j hj => h j (ne_of_lt hj))
  by_cases hjk : j = k
  · rw [hjk]
  · exact le_of_lt (h j hjk)

/-- The delegate is at most any index whose report is weakly nearest. -/
theorem delegate_le_of_forall_le {m : ℝ} {k : P}
    (h : ∀ l, |s k - m| ≤ |s l - m|) : delegate s m ≤ k := by
  unfold delegate
  apply Finset.min'_le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- Exact delegate-cell certificate: `k` is selected at `m` iff it is nearest
to `m` and every lower-priority proxy is strictly farther away. -/
theorem delegate_eq_iff_forall_le_and_forall_lt {m : ℝ} {k : P} :
    delegate s m = k ↔
      (∀ j, |s k - m| ≤ |s j - m|)
        ∧ ∀ j, j < k → |s k - m| < |s j - m| := by
  constructor
  · intro hdel
    constructor
    · intro j
      rw [← hdel]
      exact delegate_dist_le s m j
    · intro j hj
      have hle : |s k - m| ≤ |s j - m| := by
        rw [← hdel]
        exact delegate_dist_le s m j
      have hne : |s k - m| ≠ |s j - m| := by
        intro heq
        have hnear : ∀ l, |s j - m| ≤ |s l - m| := by
          intro l
          rw [← heq, ← hdel]
          exact delegate_dist_le s m l
        have hjdel : delegate s m ≤ j := delegate_le_of_forall_le hnear
        rw [hdel] at hjdel
        exact (not_le_of_gt hj) hjdel
      exact lt_of_le_of_ne hle hne
  · rintro ⟨hle, hlt⟩
    exact delegate_eq_of_forall_le_of_forall_lt hle hlt

/-- Delegate-cell geometry in midpoint form.  The first two clauses say that
`m` lies weakly between the nearest left and right midpoint barriers for `k`;
the last three clauses encode the order tie-break against lower-priority
proxies, making the corresponding barriers strict and excluding lower proxies
reported at exactly the same position. -/
theorem delegate_eq_iff_midpoint_bounds {m : ℝ} {k : P} :
    delegate s m = k ↔
      (∀ l, s l < s k → (s l + s k) / 2 ≤ m)
        ∧ (∀ l, s k < s l → m ≤ (s k + s l) / 2)
        ∧ (∀ l, l < k → s l ≠ s k)
        ∧ (∀ l, l < k → s l < s k → (s l + s k) / 2 < m)
        ∧ (∀ l, l < k → s k < s l → m < (s k + s l) / 2) := by
  constructor
  · intro hdel
    have hcert := delegate_eq_iff_forall_le_and_forall_lt.mp hdel
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro l hlt
      exact (abs_right_sub_le_abs_left_sub_iff hlt).mp (hcert.1 l)
    · intro l hlt
      exact (abs_left_sub_le_abs_right_sub_iff hlt).mp (hcert.1 l)
    · intro l hl heq
      have hstrict := hcert.2 l hl
      rw [heq] at hstrict
      exact (lt_irrefl _) hstrict
    · intro l hl hlt
      exact (abs_right_sub_lt_abs_left_sub_iff hlt).mp (hcert.2 l hl)
    · intro l hl hlt
      exact (abs_left_sub_lt_abs_right_sub_iff hlt).mp (hcert.2 l hl)
  · rintro ⟨hleft, hright, hne, hleft_strict, hright_strict⟩
    refine delegate_eq_of_forall_le_of_forall_lt ?_ ?_
    · intro l
      rcases lt_trichotomy (s l) (s k) with hlt | heq | hgt
      · exact (abs_right_sub_le_abs_left_sub_iff hlt).mpr (hleft l hlt)
      · rw [heq]
      · exact (abs_left_sub_le_abs_right_sub_iff hgt).mpr (hright l hgt)
    · intro l hl
      rcases lt_trichotomy (s l) (s k) with hlt | heq | hgt
      · exact (abs_right_sub_lt_abs_left_sub_iff hlt).mpr (hleft_strict l hl hlt)
      · exact absurd heq (hne l hl)
      · exact (abs_left_sub_lt_abs_right_sub_iff hgt).mpr (hright_strict l hl hgt)

/-- Explicit open delegate cell when `jw` has nearest reported neighbors
`jl` and `jr` on the left and right, and both endpoint ties break away from
`jw` because those neighbors have lower proxy priority.  This is the
natural-order endpoint formula: left-neighbor midpoint first, right-neighbor
midpoint second. -/
theorem setOf_delegate_eq_eq_Ioo_of_neighbor_bounds
    {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hlprio : jl < jw) (hrprio : jr < jw)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    {m | delegate s m = jw}
      = Set.Ioo ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  ext m
  constructor
  · intro hdel
    obtain ⟨_, _, _, hleft_strict, hright_strict⟩ :=
      delegate_eq_iff_midpoint_bounds.mp hdel
    exact ⟨hleft_strict jl hlprio hlpos, hright_strict jr hrprio hrpos⟩
  · intro hm
    change delegate s m = jw
    rw [delegate_eq_iff_midpoint_bounds]
    refine ⟨?_, ?_, hneq, ?_, ?_⟩
    · intro k hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k hk
      have hle := hright k hk
      nlinarith [hm.2]
    · intro k _ hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k _ hk
      have hle := hright k hk
      nlinarith [hm.2]

/-- Explicit closed delegate cell when `jw` has nearest reported neighbors
`jl` and `jr`, and no lower-priority proxy sits at either endpoint barrier.
Endpoint closure is exactly the condition that every lower-priority proxy on
that side is strictly beyond the nearest-neighbor report. -/
theorem setOf_delegate_eq_eq_Icc_of_neighbor_bounds
    {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hleftLowerStrict : ∀ k, k < jw → s k < s jw → s k < s jl)
    (hrightLowerStrict : ∀ k, k < jw → s jw < s k → s jr < s k)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    {m | delegate s m = jw}
      = Set.Icc ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  ext m
  constructor
  · intro hdel
    obtain ⟨hleft_weak, hright_weak, _, _, _⟩ :=
      delegate_eq_iff_midpoint_bounds.mp hdel
    exact ⟨hleft_weak jl hlpos, hright_weak jr hrpos⟩
  · intro hm
    change delegate s m = jw
    rw [delegate_eq_iff_midpoint_bounds]
    refine ⟨?_, ?_, hneq, ?_, ?_⟩
    · intro k hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k hk
      have hle := hright k hk
      nlinarith [hm.2]
    · intro k hklt hk
      have hlt := hleftLowerStrict k hklt hk
      nlinarith [hm.1]
    · intro k hklt hk
      have hlt := hrightLowerStrict k hklt hk
      nlinarith [hm.2]

/-- Explicit left-closed/right-open delegate cell.  The left endpoint tie
breaks toward `jw` because lower-priority left reports are strictly farther
left; the right endpoint tie breaks away from `jw` because the nearest right
neighbor has lower proxy priority. -/
theorem setOf_delegate_eq_eq_Ico_of_neighbor_bounds
    {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hleftLowerStrict : ∀ k, k < jw → s k < s jw → s k < s jl)
    (hrprio : jr < jw)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    {m | delegate s m = jw}
      = Set.Ico ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  ext m
  constructor
  · intro hdel
    obtain ⟨hleft_weak, _, _, _, hright_strict⟩ :=
      delegate_eq_iff_midpoint_bounds.mp hdel
    exact ⟨hleft_weak jl hlpos, hright_strict jr hrprio hrpos⟩
  · intro hm
    change delegate s m = jw
    rw [delegate_eq_iff_midpoint_bounds]
    refine ⟨?_, ?_, hneq, ?_, ?_⟩
    · intro k hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k hk
      have hle := hright k hk
      nlinarith [hm.2]
    · intro k hklt hk
      have hlt := hleftLowerStrict k hklt hk
      nlinarith [hm.1]
    · intro k _ hk
      have hle := hright k hk
      nlinarith [hm.2]

/-- Explicit left-open/right-closed delegate cell.  This is the mirror of
`setOf_delegate_eq_eq_Ico_of_neighbor_bounds`. -/
theorem setOf_delegate_eq_eq_Ioc_of_neighbor_bounds
    {jw jl jr : P}
    (hlpos : s jl < s jw) (hrpos : s jw < s jr)
    (hleft : ∀ k, s k < s jw → s k ≤ s jl)
    (hright : ∀ k, s jw < s k → s jr ≤ s k)
    (hlprio : jl < jw)
    (hrightLowerStrict : ∀ k, k < jw → s jw < s k → s jr < s k)
    (hneq : ∀ k, k < jw → s k ≠ s jw) :
    {m | delegate s m = jw}
      = Set.Ioc ((s jl + s jw) / 2) ((s jw + s jr) / 2) := by
  ext m
  constructor
  · intro hdel
    obtain ⟨_, hright_weak, _, hleft_strict, _⟩ :=
      delegate_eq_iff_midpoint_bounds.mp hdel
    exact ⟨hleft_strict jl hlprio hlpos, hright_weak jr hrpos⟩
  · intro hm
    change delegate s m = jw
    rw [delegate_eq_iff_midpoint_bounds]
    refine ⟨?_, ?_, hneq, ?_, ?_⟩
    · intro k hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k hk
      have hle := hright k hk
      nlinarith [hm.2]
    · intro k _ hk
      have hle := hleft k hk
      nlinarith [hm.1]
    · intro k hklt hk
      have hlt := hrightLowerStrict k hklt hk
      nlinarith [hm.2]

/-- The delegate cell is order-convex: a proxy selected at two evaluation
points is selected everywhere between them.  Between the points the selected
position is squeezed to the proxy's own report by monotonicity, and the
tie-break cannot change hands: a lower index winning in the middle would
already have won at an endpoint. -/
theorem delegate_eq_of_delegate_eq_of_between {jw : P} {m₁ m₂ m : ℝ}
    (h1 : delegate s m₁ = jw) (h2 : delegate s m₂ = jw)
    (hm1 : m₁ ≤ m) (hm2 : m ≤ m₂) : delegate s m = jw := by
  have hpos : s (delegate s m) = s jw := by
    have hle1 : s (delegate s m₁) ≤ s (delegate s m) := delegate_pos_mono hm1
    have hle2 : s (delegate s m) ≤ s (delegate s m₂) := delegate_pos_mono hm2
    rw [h1] at hle1
    rw [h2] at hle2
    exact le_antisymm hle2 hle1
  refine le_antisymm ?_ ?_
  · refine delegate_le_of_forall_le fun l => ?_
    rw [← hpos]
    exact delegate_dist_le s m l
  · rw [← h1]
    refine delegate_le_of_forall_le fun l => ?_
    rw [hpos, ← h1]
    exact delegate_dist_le s m₁ l

/-- The set of evaluation points selecting a given proxy is an interval. -/
theorem ordConnected_setOf_delegate_eq (jw : P) :
    Set.OrdConnected {m | delegate s m = jw} := by
  constructor
  intro m₁ hm₁ m₂ hm₂ m hm
  exact delegate_eq_of_delegate_eq_of_between hm₁ hm₂ hm.1 hm.2

end Geometry

/-! ## The weighted median rule -/

/-- Delegation weight of a proxy: one self-vote plus the delegating followers. -/
noncomputable def weight (s : P → ℝ) (q : F → ℝ) (j : P) : ℕ :=
  (univ.filter fun i => delegate s (q i) = j).card + 1

/-- The weighted-median winner predicate of the paper: the proxy's reported
position is a weighted median of the reported proxy positions, weighted by
delegation counts. -/
def IsWMWinner (s : P → ℝ) (q : F → ℝ) (j : P) : Prop :=
  Math.IsWeightedMedian s (weight s q) (s j)

/-- Positions of the full population: proxies at their reports, followers at
their own positions. -/
def allPos (s : P → ℝ) (q : F → ℝ) : P ⊕ F → ℝ := Sum.elim s q

private instance : Nonempty (P ⊕ F) := ⟨Sum.inl (Classical.arbitrary P)⟩

omit [Fintype P] [Nonempty P] [Fintype F] in
theorem allPos_update_inl [DecidableEq (P ⊕ F)]
    (s : P → ℝ) (q : F → ℝ) (j : P) (r : ℝ) :
    allPos (Function.update s j r) q
      = Function.update (allPos s q) (Sum.inl j) r := by
  funext v
  cases v with
  | inl j' => simp [allPos, Function.update_apply, Sum.inl.injEq]
  | inr i => simp [allPos]

/-- The canonical median position of the full population. -/
noncomputable def socialMedian (s : P → ℝ) (q : F → ℝ) : ℝ :=
  Math.weightedMedian (allPos s q) (fun _ => 1)

/-- The winning proxy: the proxy nearest the population median, ties broken by
the proxy order. -/
noncomputable def winner (s : P → ℝ) (q : F → ℝ) : P :=
  delegate s (socialMedian s q)

/-- The winning position. -/
noncomputable def outcome (s : P → ℝ) (q : F → ℝ) : ℝ := s (winner s q)

/-- With strictly more followers than proxies, a point-mass follower profile
realizes its common position as the population median: the followers carry a
strict majority of the weight.  This is the richness mechanism for partial
information — every target median is attained by some follower profile,
whatever the reports. -/
theorem socialMedian_const (hcard : Fintype.card P < Fintype.card F)
    (s : P → ℝ) (μ : ℝ) :
    socialMedian s (fun _ : F => μ) = μ := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_eq_of_majority ?_
  have hsub : (univ.image (Sum.inr : F → P ⊕ F))
      ⊆ univ.filter fun v => allPos s (fun _ : F => μ) v = μ := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨f, -, rfl⟩ := hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcardF : Fintype.card F
      ≤ ∑ v ∈ univ.filter (fun v => allPos s (fun _ : F => μ) v = μ), (1 : ℕ) := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    calc Fintype.card F = (univ.image (Sum.inr : F → P ⊕ F)).card := by
          rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]
      _ ≤ _ := Finset.card_le_card hsub
  have htot : Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ))
      = Fintype.card P + Fintype.card F := by
    rw [Math.totalWeight_one, Fintype.card_sum]
  omega

/-- The utilitarian social cost of position `x`: total distance from the
population's true positions — proxies at their peaks, followers at their
own positions. -/
noncomputable def socialCost (pp : P → ℝ) (q : F → ℝ) (x : ℝ) : ℝ :=
  ∑ v, |allPos pp q v - x|

/-! ## Lemma 1: the winner is a weighted median of the proxies -/

omit [Nonempty P] [LinearOrder P] in
private theorem card_filter_sum (p : P ⊕ F → Prop) [DecidablePred p] :
    (univ.filter p).card
      = (univ.filter fun j : P => p (Sum.inl j)).card
        + (univ.filter fun i : F => p (Sum.inr i)).card := by
  rw [← Finset.card_toLeft_add_card_toRight]
  have hl : (univ.filter p).toLeft = univ.filter fun j : P => p (Sum.inl j) := by
    ext j; simp
  have hr : (univ.filter p).toRight = univ.filter fun i : F => p (Sum.inr i) := by
    ext i; simp
  rw [hl, hr]

/-- The strict-left delegation weight splits into followers whose delegate
reports below `c` and proxies reporting below `c`. -/
theorem leftWeight_weight_eq (s : P → ℝ) (q : F → ℝ) (c : ℝ) :
    Math.leftWeight s (weight s q) c
      = (univ.filter fun i : F => s (delegate s (q i)) < c).card
        + (univ.filter fun j : P => s j < c).card := by
  unfold Math.leftWeight weight
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext i
    simp
  · simp

/-- The strict-right delegation weight splits into followers whose delegate
reports above `c` and proxies reporting above `c`. -/
theorem rightWeight_weight_eq (s : P → ℝ) (q : F → ℝ) (c : ℝ) :
    Math.rightWeight s (weight s q) c
      = (univ.filter fun i : F => c < s (delegate s (q i))).card
        + (univ.filter fun j : P => c < s j).card := by
  unfold Math.rightWeight weight
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext i
    simp
  · simp

/-- The total delegation weight is the full population count. -/
theorem totalWeight_weight (s : P → ℝ) (q : F → ℝ) :
    Math.totalWeight (weight s q) = Fintype.card F + Fintype.card P := by
  unfold Math.totalWeight weight
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  · simp

/-- **Lemma 1** (Cohensius et al. 2017).  The proxy nearest the population
median is a weighted median of the reported proxy positions under delegation
weights: the weighted median rule elects the proxy chosen by the population's
median voter. -/
theorem winner_isWMWinner (s : P → ℝ) (q : F → ℝ) : IsWMWinner s q (winner s q) := by
  have hmed :=
    Math.isWeightedMedian_weightedMedian (Sum.elim s q) (fun _ : P ⊕ F => 1)
  have hL := hmed.1
  have hR := hmed.2
  rw [Math.leftWeight_one, card_filter_sum, Math.totalWeight_one,
    Fintype.card_sum] at hL
  rw [Math.rightWeight_one, card_filter_sum, Math.totalWeight_one,
    Fintype.card_sum] at hR
  simp only [Sum.elim_inl, Sum.elim_inr] at hL hR
  change Math.IsWeightedMedian s (weight s q)
    (s (delegate s (Math.weightedMedian (Sum.elim s q) (fun _ : P ⊕ F => 1))))
  set M := Math.weightedMedian (Sum.elim s q) (fun _ : P ⊕ F => 1) with hM
  constructor
  · rw [leftWeight_weight_eq, totalWeight_weight]
    have hF : (univ.filter fun i : F => s (delegate s (q i)) < s (delegate s M)).card
        ≤ (univ.filter fun i : F => q i < M).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact lt_of_delegate_pos_lt hi
    have hP : (univ.filter fun j : P => s j < s (delegate s M)).card
        ≤ (univ.filter fun j : P => s j < M).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact pos_lt_of_lt_delegate_pos hj
    omega
  · rw [rightWeight_weight_eq, totalWeight_weight]
    have hF : (univ.filter fun i : F => s (delegate s M) < s (delegate s (q i))).card
        ≤ (univ.filter fun i : F => M < q i).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact lt_of_delegate_pos_lt hi
    have hP : (univ.filter fun j : P => s (delegate s M) < s j).card
        ≤ (univ.filter fun j : P => M < s j).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact pos_gt_of_gt_delegate_pos hj
    omega

/-! ## Theorem 1: follower strategyproofness -/

section FollowerSP

variable [DecidableEq F]

omit [Fintype P] [Nonempty P] [Fintype F] in
private theorem allPos_update_inr (s : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    allPos s (Function.update q i x)
      = Function.update (allPos s q) (Sum.inr i) x := by
  funext v
  cases v with
  | inl j => simp [allPos]
  | inr i' => simp [allPos, Function.update_apply, Sum.inr.injEq]

/-- Raising a follower's report weakly raises the population median. -/
theorem socialMedian_le_update {s : P → ℝ} {q : F → ℝ} {i : F} {x : ℝ}
    (h : q i ≤ x) :
    socialMedian s q ≤ socialMedian s (Function.update q i x) := by
  unfold socialMedian
  rw [allPos_update_inr]
  refine Math.weightedMedian_le_weightedMedian_of_le _ Math.totalWeight_one_pos ?_
  intro v
  rw [Function.update_apply]
  split
  · rename_i hv
    subst hv
    exact h
  · exact le_refl _

/-- Lowering a follower's report weakly lowers the population median. -/
theorem socialMedian_update_le {s : P → ℝ} {q : F → ℝ} {i : F} {x : ℝ}
    (h : x ≤ q i) :
    socialMedian s (Function.update q i x) ≤ socialMedian s q := by
  unfold socialMedian
  rw [allPos_update_inr]
  refine Math.weightedMedian_le_weightedMedian_of_le _ Math.totalWeight_one_pos ?_
  intro v
  rw [Function.update_apply]
  split
  · rename_i hv
    subst hv
    exact h
  · exact le_refl _

/-- A follower strictly left of the median who reports weakly left of the
median does not move it. -/
theorem socialMedian_update_eq_of_lt_of_le {s : P → ℝ} {q : F → ℝ} {i : F} {x : ℝ}
    (hi : q i < socialMedian s q) (hx : x ≤ socialMedian s q) :
    socialMedian s (Function.update q i x) = socialMedian s q := by
  unfold socialMedian
  rw [allPos_update_inr]
  exact Math.weightedMedian_update_eq_of_lt_of_le Math.totalWeight_one_pos hi hx

/-- A follower strictly right of the median who reports weakly right of the
median does not move it. -/
theorem socialMedian_update_eq_of_gt_of_ge {s : P → ℝ} {q : F → ℝ} {i : F} {x : ℝ}
    (hi : socialMedian s q < q i) (hx : socialMedian s q ≤ x) :
    socialMedian s (Function.update q i x) = socialMedian s q := by
  unfold socialMedian
  rw [allPos_update_inr]
  exact Math.weightedMedian_update_eq_of_gt_of_ge Math.totalWeight_one_pos hi hx

end FollowerSP

section OutcomeLift

variable {s : P → ℝ}

/-- Every proxy position strictly above the winning position at `μ` clears the
reflection of the winning position across `μ`. -/
private theorem delegate_pos_gap {μ : ℝ} {k : P}
    (h : s (delegate s μ) < s k) :
    2 * μ - s (delegate s μ) ≤ s k := by
  have hd := delegate_dist_le s μ k
  rcases abs_cases (s (delegate s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

/-- Every proxy position strictly below the winning position at `μ` clears the
reflection of the winning position across `μ`. -/
private theorem delegate_pos_gap' {μ : ℝ} {k : P}
    (h : s k < s (delegate s μ)) :
    s k ≤ 2 * μ - s (delegate s μ) := by
  have hd := delegate_dist_le s μ k
  rcases abs_cases (s (delegate s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

/-- Lifting a rightward median move through the nearest-proxy map: for a peak
strictly left of the old median, the winning position moves weakly away. -/
private theorem abs_delegate_sub_le_of_le {μ μ' t : ℝ}
    (ht : t < μ) (hm : μ ≤ μ') :
    |s (delegate s μ) - t| ≤ |s (delegate s μ') - t| := by
  have hν : s (delegate s μ) ≤ s (delegate s μ') := delegate_pos_mono hm
  rcases le_or_gt t (s (delegate s μ)) with hcase | hcase
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rcases eq_or_lt_of_le hν with heq | hlt
    · rw [heq]
    · have hgap : 2 * μ - s (delegate s μ) ≤ s (delegate s μ') :=
        delegate_pos_gap hlt
      rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- Lifting a leftward median move through the nearest-proxy map: for a peak
strictly right of the old median, the winning position moves weakly away. -/
private theorem abs_delegate_sub_le_of_ge {μ μ' t : ℝ}
    (ht : μ < t) (hm : μ' ≤ μ) :
    |s (delegate s μ) - t| ≤ |s (delegate s μ') - t| := by
  have hν : s (delegate s μ') ≤ s (delegate s μ) := delegate_pos_mono hm
  rcases le_or_gt (s (delegate s μ)) t with hcase | hcase
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rcases eq_or_lt_of_le hν with heq | hlt
    · rw [← heq]
    · have hgap : s (delegate s μ') ≤ 2 * μ - s (delegate s μ) :=
        delegate_pos_gap' hlt
      rw [abs_of_pos (by linarith), abs_of_nonpos (by linarith)]
      linarith

end OutcomeLift

/-- **Theorem 1** (Bielous–Meir).  The weighted median rule is strategyproof
with respect to follower positions: no misreport brings the winning position
strictly closer to the follower's own position. -/
theorem follower_strategyproof [DecidableEq F] (s : P → ℝ) (q : F → ℝ)
    (i : F) (x : ℝ) :
    |outcome s q - q i| ≤ |outcome s (Function.update q i x) - q i| := by
  simp only [outcome, winner]
  rcases lt_trichotomy (q i) (socialMedian s q) with hqi | hqi | hqi
  · rcases le_or_gt x (socialMedian s q) with hx | hx
    · rw [socialMedian_update_eq_of_lt_of_le hqi hx]
    · exact abs_delegate_sub_le_of_le hqi
        (socialMedian_le_update (le_of_lt (lt_trans hqi hx)))
  · rw [← hqi]
    exact delegate_dist_le s (q i) _
  · rcases le_or_gt (socialMedian s q) x with hx | hx
    · rw [socialMedian_update_eq_of_gt_of_ge hqi hx]
    · exact abs_delegate_sub_le_of_ge hqi
        (socialMedian_update_le (le_of_lt (lt_trans hx hqi)))

/-- Theorem 1 in preference form: a follower never strictly prefers the
outcome of a misreport under Euclidean single-peaked preferences. -/
theorem follower_no_manipulation [DecidableEq F] (s : P → ℝ) (q : F → ℝ)
    (i : F) (x : ℝ) :
    ¬ Prefers q i (outcome s (Function.update q i x)) (outcome s q) :=
  not_lt.mpr (follower_strategyproof s q i x)

/-! ## Theorem 2: characterization of proxy manipulability -/

/-- The comparison forced by single-peakedness: every single-peaked preference
with peak `t` strictly prefers `a` to `b` when `a` lies strictly between `b`
and the peak, weakly on the peak's side. -/
def SPPrefers (t a b : ℝ) : Prop := (t ≤ a ∧ a < b) ∨ (b < a ∧ a ≤ t)

/-- The weak comparison forced by single-peakedness: every single-peaked
preference with peak `t` weakly prefers `a` to `b` when `a` lies between `t`
and `b`. -/
def SPWeaklyPrefers (t a b : ℝ) : Prop := (t ≤ a ∧ a ≤ b) ∨ (b ≤ a ∧ a ≤ t)

section ProxyManipulation

/-- Raising a proxy's report weakly raises the population median. -/
theorem socialMedian_le_update_proxy {s : P → ℝ} {q : F → ℝ} {j : P} {r : ℝ}
    (h : s j ≤ r) :
    socialMedian s q ≤ socialMedian (Function.update s j r) q := by
  classical
  unfold socialMedian
  rw [allPos_update_inl]
  refine Math.weightedMedian_le_weightedMedian_of_le _ Math.totalWeight_one_pos ?_
  intro v
  rw [Function.update_apply]
  split
  · rename_i hv
    subst hv
    exact h
  · exact le_refl _

/-- Lowering a proxy's report weakly lowers the population median. -/
theorem socialMedian_update_proxy_le {s : P → ℝ} {q : F → ℝ} {j : P} {r : ℝ}
    (h : r ≤ s j) :
    socialMedian (Function.update s j r) q ≤ socialMedian s q := by
  classical
  unfold socialMedian
  rw [allPos_update_inl]
  refine Math.weightedMedian_le_weightedMedian_of_le _ Math.totalWeight_one_pos ?_
  intro v
  rw [Function.update_apply]
  split
  · rename_i hv
    subst hv
    exact h
  · exact le_refl _

omit [LinearOrder P] in
/-- If the population median strictly rises between two proxy-report states
with the same follower profile, some population coordinate crosses strictly
above the old median. -/
theorem exists_allPos_le_socialMedian_lt_of_socialMedian_lt
    {s s' : P → ℝ} {q : F → ℝ} (h : socialMedian s q < socialMedian s' q) :
    ∃ a : P ⊕ F, allPos s q a ≤ socialMedian s q ∧ socialMedian s q < allPos s' q a := by
  unfold socialMedian at h ⊢
  exact Math.exists_le_weightedMedian_lt_of_weightedMedian_lt
    (pos := allPos s q) (pos' := allPos s' q) (w := fun _ : P ⊕ F => 1)
    Math.totalWeight_one_pos h

omit [LinearOrder P] in
/-- If the population median strictly falls between two proxy-report states
with the same follower profile, some population coordinate crosses weakly below
the new median. -/
theorem exists_socialMedian_lt_allPos_ge_of_socialMedian_lt
    {s s' : P → ℝ} {q : F → ℝ} (h : socialMedian s' q < socialMedian s q) :
    ∃ a : P ⊕ F, socialMedian s' q < allPos s q a ∧ allPos s' q a ≤ socialMedian s' q := by
  unfold socialMedian at h ⊢
  exact Math.exists_weightedMedian_lt_ge_of_weightedMedian_lt
    (pos := allPos s q) (pos' := allPos s' q) (w := fun _ : P ⊕ F => 1)
    Math.totalWeight_one_pos h

/-- Reporting `p` minimizes the movement of the population median away from
`p`, among all reports by the same proxy. -/
theorem abs_socialMedian_update_proxy_sub_le_update
    (s : P → ℝ) (q : F → ℝ) (j : P) (p u : ℝ) :
    |socialMedian (Function.update s j p) q - p|
      ≤ |socialMedian (Function.update s j u) q - p| := by
  classical
  have h := Math.abs_weightedMedian_sub_le_update
    (pos := allPos (Function.update s j p) q) (w := fun _ : P ⊕ F => 1)
    Math.totalWeight_one_pos (Sum.inl j) u
  have hpoint : allPos (Function.update s j p) q (Sum.inl j) = p := by
    simp [allPos]
  have hupdate :
      Function.update (allPos (Function.update s j p) q) (Sum.inl j) u
        = allPos (Function.update s j u) q := by
    ext v
    cases v with
    | inl k =>
        by_cases hkj : k = j
        · subst hkj
          rw [Function.update_self]
          change u = Function.update s k u k
          rw [Function.update_self]
        · have hsum : (Sum.inl k : P ⊕ F) ≠ Sum.inl j := by
            intro h
            exact hkj (Sum.inl.inj h)
          rw [Function.update_apply, if_neg hsum]
          change Function.update s j p k = Function.update s j u k
          rw [Function.update_apply, if_neg hkj, Function.update_apply, if_neg hkj]
    | inr i =>
        have hsum : Sum.inr i ≠ Sum.inl j := by intro h; cases h
        rw [Function.update_apply, if_neg hsum]
        rfl
  unfold socialMedian
  rw [hpoint] at h
  rwa [hupdate] at h

/-- A proxy strictly left of the median reporting weakly left of the median
does not move it. -/
theorem socialMedian_update_eq_of_proxy_lt {s : P → ℝ} {q : F → ℝ} {j : P} {r : ℝ}
    (hj : s j < socialMedian s q) (hr : r ≤ socialMedian s q) :
    socialMedian (Function.update s j r) q = socialMedian s q := by
  classical
  unfold socialMedian
  rw [allPos_update_inl]
  exact Math.weightedMedian_update_eq_of_lt_of_le Math.totalWeight_one_pos hj hr

/-- A proxy strictly right of the median reporting weakly right of the median
does not move it. -/
theorem socialMedian_update_eq_of_proxy_gt {s : P → ℝ} {q : F → ℝ} {j : P} {r : ℝ}
    (hj : socialMedian s q < s j) (hr : socialMedian s q ≤ r) :
    socialMedian (Function.update s j r) q = socialMedian s q := by
  classical
  unfold socialMedian
  rw [allPos_update_inl]
  exact Math.weightedMedian_update_eq_of_gt_of_ge Math.totalWeight_one_pos hj hr

/-- The population median is immune to a single proxy when the rest of the
population already pins it: `m` is attained off `j`, the off-`j` weight
weakly left of `m` reaches half the total, and the off-`j` weight strictly
left of `m` plus one stays strictly below half. -/
theorem socialMedian_update_eq_of_pinned [DecidableEq F]
    {s : P → ℝ} {q : F → ℝ} {j : P} {m : ℝ}
    (hattain : ∃ v, v ≠ Sum.inl j ∧ allPos s q v = m)
    (hcum : Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ))
      ≤ 2 * ∑ _v ∈ univ.filter fun v => v ≠ Sum.inl j ∧ allPos s q v ≤ m,
          (1 : ℕ))
    (hbelow : 2 * ((∑ _v ∈ univ.filter
        fun v => v ≠ Sum.inl j ∧ allPos s q v < m, (1 : ℕ)) + 1)
      < Math.totalWeight (fun _ : P ⊕ F => (1 : ℕ)))
    (y : ℝ) : socialMedian (Function.update s j y) q = m := by
  classical
  unfold socialMedian
  rw [allPos_update_inl]
  exact Math.weightedMedian_update_eq_of_pinned hattain hcum hbelow y

/-- If a proxy drifts left of a target `p`, and `p` remains weakly left of the
post-drift population median, retargeting the same proxy to `p` has the same
median effect as the drift. -/
theorem socialMedian_update_eq_of_update_lt_of_le
    {s : P → ℝ} {q : F → ℝ} {j : P} {u p : ℝ}
    (hu : u < p) (hp : p ≤ socialMedian (Function.update s j u) q) :
    socialMedian (Function.update s j p) q =
      socialMedian (Function.update s j u) q := by
  have hj : Function.update s j u j < socialMedian (Function.update s j u) q := by
    rw [Function.update_self]
    exact lt_of_lt_of_le hu hp
  have h := socialMedian_update_eq_of_proxy_lt (s := Function.update s j u)
    (q := q) (j := j) (r := p) hj hp
  simpa [Function.update_eq_self] using h

/-- If a proxy drifts right of a target `p`, and `p` remains weakly right of the
post-drift population median, retargeting the same proxy to `p` has the same
median effect as the drift. -/
theorem socialMedian_update_eq_of_le_of_update_gt
    {s : P → ℝ} {q : F → ℝ} {j : P} {u p : ℝ}
    (hp : socialMedian (Function.update s j u) q ≤ p) (hu : p < u) :
    socialMedian (Function.update s j p) q =
      socialMedian (Function.update s j u) q := by
  have hj : socialMedian (Function.update s j u) q < Function.update s j u j := by
    rw [Function.update_self]
    exact lt_of_le_of_lt hp hu
  have h := socialMedian_update_eq_of_proxy_gt (s := Function.update s j u)
    (q := q) (j := j) (r := p) hj hp
  simpa [Function.update_eq_self] using h

/-- For a left drift below `p` whose post-drift median is weakly right of `p`,
truthful retargeting either selects `p` itself or preserves the drift outcome. -/
theorem outcome_update_eq_self_or_eq_of_update_lt_of_le
    {s : P → ℝ} {q : F → ℝ} {j : P} {u p : ℝ}
    (hu : u < p) (hp : p ≤ socialMedian (Function.update s j u) q) :
    outcome (Function.update s j p) q = p ∨
      outcome (Function.update s j p) q = outcome (Function.update s j u) q := by
  have hmed := socialMedian_update_eq_of_update_lt_of_le (s := s) (q := q)
    (j := j) hu hp
  have hd : |p - socialMedian (Function.update s j u) q|
      < |u - socialMedian (Function.update s j u) q| := by
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith
  unfold outcome winner
  rw [hmed]
  exact update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
    (m := socialMedian (Function.update s j u) q) (p := p) (r := u) hd

/-- For a right drift above `p` whose post-drift median is weakly left of `p`,
truthful retargeting either selects `p` itself or preserves the drift outcome. -/
theorem outcome_update_eq_self_or_eq_of_le_of_update_gt
    {s : P → ℝ} {q : F → ℝ} {j : P} {u p : ℝ}
    (hp : socialMedian (Function.update s j u) q ≤ p) (hu : p < u) :
    outcome (Function.update s j p) q = p ∨
      outcome (Function.update s j p) q = outcome (Function.update s j u) q := by
  have hmed := socialMedian_update_eq_of_le_of_update_gt (s := s) (q := q)
    (j := j) hp hu
  have hd : |p - socialMedian (Function.update s j u) q|
      < |u - socialMedian (Function.update s j u) q| := by
    rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
    linarith
  unfold outcome winner
  rw [hmed]
  exact update_delegate_eq_self_or_eq_of_dist_lt (s := s) (j := j)
    (m := socialMedian (Function.update s j u) q) (p := p) (r := u) hd

/-- Another proxy's report strictly above the population median remains an
upper bound for the median after a one-proxy update. -/
theorem socialMedian_update_le_of_lt {s : P → ℝ} {q : F → ℝ} {j k : P} {x : ℝ}
    (hkj : k ≠ j) (h : socialMedian s q < s k) :
    socialMedian (Function.update s j x) q ≤ s k := by
  classical
  unfold socialMedian at h ⊢
  rw [allPos_update_inl]
  exact Math.weightedMedian_update_le_of_lt (pos := allPos s q) (w := fun _ => 1)
    (i := Sum.inl j) (a := Sum.inl k) (x := x)
    (fun hEq => hkj (Sum.inl.inj hEq)) le_rfl h

/-- Another proxy's report strictly below the population median remains a
lower bound for the median after a one-proxy update. -/
theorem le_socialMedian_update_of_lt {s : P → ℝ} {q : F → ℝ} {j k : P} {x : ℝ}
    (hkj : k ≠ j) (h : s k < socialMedian s q) :
    s k ≤ socialMedian (Function.update s j x) q := by
  classical
  unfold socialMedian at h ⊢
  rw [allPos_update_inl]
  exact Math.le_weightedMedian_update_of_lt (pos := allPos s q) (w := fun _ => 1)
    (i := Sum.inl j) (a := Sum.inl k) (x := x)
    (fun hEq => hkj (Sum.inl.inj hEq)) le_rfl Math.totalWeight_one_pos h

omit [LinearOrder P] in
/-- With integral reports and follower positions, the population median is
integral: the canonical median is attained. -/
theorem exists_int_socialMedian {s : P → ℝ} {q : F → ℝ}
    (hs : ∀ j, ∃ n : ℤ, s j = n) (hq : ∀ i, ∃ n : ℤ, q i = n) :
    ∃ n : ℤ, socialMedian s q = n := by
  obtain ⟨a, ha⟩ := Math.exists_pos_eq_weightedMedian (allPos s q) (fun _ => 1)
  rcases a with j | i
  · obtain ⟨n, hn⟩ := hs j
    refine ⟨n, ?_⟩
    unfold socialMedian
    rw [← ha]
    exact hn
  · obtain ⟨n, hn⟩ := hq i
    refine ⟨n, ?_⟩
    unfold socialMedian
    rw [← ha]
    exact hn

/-- With integral reports, the outcome is integral: it is a report. -/
theorem exists_int_outcome {s : P → ℝ} (q : F → ℝ)
    (hs : ∀ j, ∃ n : ℤ, s j = n) :
    ∃ n : ℤ, outcome s q = n :=
  hs (winner s q)

variable {pp : P → ℝ} {q : F → ℝ}

/-- With a proxy at the median, the outcome is the median. -/
private theorem outcome_eq_median_of_proxy_at {k : P}
    (hk : pp k = socialMedian pp q) : outcome pp q = socialMedian pp q := by
  have hd := delegate_dist_le pp (socialMedian pp q) k
  rw [hk, sub_self, abs_zero] at hd
  have h0 := abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))
  have := sub_eq_zero.mp h0
  simpa [outcome, winner] using this

/-- No proxy can manipulate when some proxy sits at the population median: no
report brings the outcome strictly closer to the manipulator's peak. -/
private theorem no_manipulation_of_proxy_at_median {k : P}
    (hk : pp k = socialMedian pp q) (j : P) (r : ℝ) :
    SPWeaklyPrefers (pp j) (outcome pp q) (outcome (Function.update pp j r) q) := by
  rw [outcome_eq_median_of_proxy_at hk]
  rcases lt_trichotomy (pp j) (socialMedian pp q) with hj | hj | hj
  · -- peak strictly left of the median: the new outcome stays weakly right of
    -- the median, so it cannot land strictly between the peak and the median
    have hout : socialMedian pp q ≤ outcome (Function.update pp j r) q := by
      have hkj : k ≠ j := fun h => by rw [h] at hk; exact absurd (hk ▸ hj) (lt_irrefl _)
      have hs'k : Function.update pp j r k = socialMedian pp q := by
        rw [Function.update_apply, if_neg hkj, hk]
      rcases le_or_gt r (socialMedian pp q) with hr | hr
      · -- median unchanged; the proxy at the median still wins it exactly
        have hμ := socialMedian_update_eq_of_proxy_lt hj hr
        have hd := delegate_dist_le (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hμ, hs'k, sub_self, abs_zero] at hd
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simp only [outcome, winner, hμ, h0, le_refl]
      · -- median weakly rises; the proxy at the old median caps the distance
        have hμ : socialMedian pp q ≤ socialMedian (Function.update pp j r) q :=
          socialMedian_le_update_proxy (le_of_lt (lt_trans hj hr))
        have hd := delegate_dist_le (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hs'k] at hd
        have habs : |socialMedian pp q - socialMedian (Function.update pp j r) q|
            = socialMedian (Function.update pp j r) q - socialMedian pp q := by
          rw [abs_of_nonpos (by linarith)]
          ring
        rw [habs] at hd
        have := neg_le_of_abs_le hd
        simp only [outcome, winner]
        linarith
    exact Or.inl ⟨le_of_lt hj, hout⟩
  · -- peak at the median: the median is weakly preferred to every outcome
    rcases le_total (socialMedian pp q) (outcome (Function.update pp j r) q) with h | h
    · exact Or.inl ⟨hj.le, h⟩
    · exact Or.inr ⟨h, hj.ge⟩
  · -- peak strictly right of the median: mirror of the first case
    have hout : outcome (Function.update pp j r) q ≤ socialMedian pp q := by
      have hkj : k ≠ j := fun h => by rw [h] at hk; exact absurd (hk ▸ hj) (lt_irrefl _)
      have hs'k : Function.update pp j r k = socialMedian pp q := by
        rw [Function.update_apply, if_neg hkj, hk]
      rcases le_or_gt (socialMedian pp q) r with hr | hr
      · have hμ := socialMedian_update_eq_of_proxy_gt hj hr
        have hd := delegate_dist_le (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hμ, hs'k, sub_self, abs_zero] at hd
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simp only [outcome, winner, hμ, h0, le_refl]
      · have hμ : socialMedian (Function.update pp j r) q ≤ socialMedian pp q :=
          socialMedian_update_proxy_le (le_of_lt (lt_trans hr hj))
        have hd := delegate_dist_le (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hs'k] at hd
        have habs : |socialMedian pp q - socialMedian (Function.update pp j r) q|
            = socialMedian pp q - socialMedian (Function.update pp j r) q :=
          abs_of_nonneg (by linarith)
        rw [habs] at hd
        have := le_of_abs_le hd
        simp only [outcome, winner]
        linarith
    exact Or.inr ⟨hout, le_of_lt hj⟩

/-- No proxy can manipulate when every proxy reports weakly left of the
median: no report brings the outcome strictly closer to any peak. -/
private theorem no_manipulation_of_proxies_le
    (hall : ∀ k, pp k ≤ socialMedian pp q) (j : P) (r : ℝ) :
    SPWeaklyPrefers (pp j) (outcome pp q) (outcome (Function.update pp j r) q) := by
  -- The truthful outcome is the greatest proxy position.
  have hcle : outcome pp q ≤ socialMedian pp q := by
    simp only [outcome, winner]
    exact hall _
  have hmax : ∀ k, pp k ≤ outcome pp q := by
    intro k
    have hd := delegate_dist_le pp (socialMedian pp q) k
    have h1 : pp (delegate pp (socialMedian pp q)) - socialMedian pp q ≤ 0 := by
      have := hall (delegate pp (socialMedian pp q))
      linarith
    have h2 : pp k - socialMedian pp q ≤ 0 := by
      have := hall k
      linarith
    rw [abs_of_nonpos h1, abs_of_nonpos h2] at hd
    change pp k ≤ pp (delegate pp (socialMedian pp q))
    linarith
  rcases eq_or_lt_of_le (hmax j) with hj | hj
  · -- the manipulator already holds the winning position: its peak is the
    -- truthful outcome, weakly single-peaked-preferred to every outcome
    rcases le_total (outcome pp q) (outcome (Function.update pp j r) q) with h | h
    · exact Or.inl ⟨hj.le, h⟩
    · exact Or.inr ⟨h, hj.ge⟩
  · -- the manipulator's peak is strictly below the winning position: the new
    -- outcome never falls strictly below the old one
    have hout : outcome pp q ≤ outcome (Function.update pp j r) q := by
      have hj₀ : winner pp q ≠ j := by
        intro h
        rw [← h] at hj
        simp only [outcome, winner] at hj
        exact absurd hj (lt_irrefl _)
      have hs'j₀ : Function.update pp j r (winner pp q) = outcome pp q := by
        rw [Function.update_apply, if_neg hj₀]
        rfl
      have hcμ' : outcome pp q ≤ socialMedian (Function.update pp j r) q := by
        rcases le_or_gt r (socialMedian pp q) with hr | hr
        · rw [socialMedian_update_eq_of_proxy_lt
            (lt_of_lt_of_le hj hcle) hr]
          exact hcle
        · exact le_trans hcle
            (socialMedian_le_update_proxy (le_of_lt (lt_of_le_of_lt (le_trans (hmax j) hcle) hr)))
      have hd := delegate_dist_le (Function.update pp j r)
        (socialMedian (Function.update pp j r) q) (winner pp q)
      rw [hs'j₀, abs_of_nonpos (sub_nonpos.mpr hcμ')] at hd
      have := neg_le_of_abs_le hd
      simp only [outcome, winner] at *
      linarith
    exact Or.inl ⟨le_of_lt hj, hout⟩

/-- No proxy can manipulate when every proxy reports weakly right of the
median: no report brings the outcome strictly closer to any peak. -/
private theorem no_manipulation_of_proxies_ge
    (hall : ∀ k, socialMedian pp q ≤ pp k) (j : P) (r : ℝ) :
    SPWeaklyPrefers (pp j) (outcome pp q) (outcome (Function.update pp j r) q) := by
  have hcge : socialMedian pp q ≤ outcome pp q := by
    simp only [outcome, winner]
    exact hall _
  have hmin : ∀ k, outcome pp q ≤ pp k := by
    intro k
    have hd := delegate_dist_le pp (socialMedian pp q) k
    have h1 : 0 ≤ pp (delegate pp (socialMedian pp q)) - socialMedian pp q := by
      have := hall (delegate pp (socialMedian pp q))
      linarith
    have h2 : 0 ≤ pp k - socialMedian pp q := by
      have := hall k
      linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hd
    change pp (delegate pp (socialMedian pp q)) ≤ pp k
    linarith
  rcases eq_or_lt_of_le (hmin j) with hj | hj
  · rcases le_total (outcome pp q) (outcome (Function.update pp j r) q) with h | h
    · exact Or.inl ⟨hj.ge, h⟩
    · exact Or.inr ⟨h, hj.le⟩
  · have hout : outcome (Function.update pp j r) q ≤ outcome pp q := by
      have hj₀ : winner pp q ≠ j := by
        intro h
        rw [← h] at hj
        simp only [outcome, winner] at hj
        exact absurd hj (lt_irrefl _)
      have hs'j₀ : Function.update pp j r (winner pp q) = outcome pp q := by
        rw [Function.update_apply, if_neg hj₀]
        rfl
      have hcμ' : socialMedian (Function.update pp j r) q ≤ outcome pp q := by
        rcases le_or_gt (socialMedian pp q) r with hr | hr
        · rw [socialMedian_update_eq_of_proxy_gt
            (lt_of_le_of_lt hcge hj) hr]
          exact hcge
        · exact le_trans
            (socialMedian_update_proxy_le (le_of_lt (lt_of_lt_of_le hr (le_trans hcge (hmin j)))))
            hcge
      have hd := delegate_dist_le (Function.update pp j r)
        (socialMedian (Function.update pp j r) q) (winner pp q)
      rw [hs'j₀, abs_of_nonneg (sub_nonneg.mpr hcμ')] at hd
      have := le_of_abs_le hd
      simp only [outcome, winner] at *
      linarith
    exact Or.inr ⟨hout, le_of_lt hj⟩

/-- A strictly-between comparison on the peak's side is a strict-distance
improvement: `SPPrefers` implies the Euclidean preference. -/
theorem SPPrefers.abs_lt {t a b : ℝ} (h : SPPrefers t a b) :
    |a - t| < |b - t| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- A forced strict single-peaked comparison is a forced weak one. -/
theorem SPPrefers.spWeaklyPrefers {t a b : ℝ} (h : SPPrefers t a b) :
    SPWeaklyPrefers t a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, le_of_lt h2⟩
  · exact Or.inr ⟨le_of_lt h1, h2⟩

/-- A forced weak single-peaked comparison implies weak Euclidean preference. -/
theorem SPWeaklyPrefers.abs_le {t a b : ℝ} (h : SPWeaklyPrefers t a b) :
    |a - t| ≤ |b - t| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- A forced weak single-peaked comparison between distinct outcomes is the
forced strict one. -/
theorem SPWeaklyPrefers.spPrefers_of_ne {t a b : ℝ} (h : SPWeaklyPrefers t a b)
    (hne : a ≠ b) : SPPrefers t a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, lt_of_le_of_ne h2 hne⟩
  · exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩

/-- **Theorem 2** (Bielous–Meir).  In the truthful state, some proxy has a
manipulation — a report whose outcome every single-peaked preference at the
proxy's peak strictly prefers — iff no proxy sits at the population median and
proxies are present strictly on both sides of it. -/
theorem proxy_manipulation_iff (pp : P → ℝ) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        SPPrefers (pp j) (outcome (Function.update pp j r) q) (outcome pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) := by
  constructor
  · rintro ⟨j, r, hpref⟩
    have hlt := hpref.abs_lt
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have := (no_manipulation_of_proxy_at_median hk j r).abs_le
      linarith
    · by_contra hno
      rw [not_exists] at hno
      have := (no_manipulation_of_proxies_ge (fun k => not_lt.mp (hno k)) j r).abs_le
      linarith
    · by_contra hno
      rw [not_exists] at hno
      have := (no_manipulation_of_proxies_le (fun k => not_lt.mp (hno k)) j r).abs_le
      linarith
  · rintro ⟨hne, ⟨jl, hjl⟩, ⟨jr, hjr⟩⟩
    have hcne : outcome pp q ≠ socialMedian pp q := hne (winner pp q)
    rcases lt_or_gt_of_ne hcne with hc | hc
    · -- outcome left of the median: the right-side proxy moves to the median
      refine ⟨jr, socialMedian pp q, ?_⟩
      have hμ := socialMedian_update_eq_of_proxy_gt hjr (le_refl _)
      have hs'jr : Function.update pp jr (socialMedian pp q) jr
          = socialMedian pp q := Function.update_self ..
      have hd := delegate_dist_le
        (Function.update pp jr (socialMedian pp q))
        (socialMedian (Function.update pp jr (socialMedian pp q)) q) jr
      rw [hμ, hs'jr, sub_self, abs_zero] at hd
      have hout : outcome (Function.update pp jr (socialMedian pp q)) q
          = socialMedian pp q := by
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simpa [outcome, winner, hμ] using h0
      rw [hout]
      exact Or.inr ⟨hc, le_of_lt hjr⟩
    · -- outcome right of the median: the left-side proxy moves to the median
      refine ⟨jl, socialMedian pp q, ?_⟩
      have hμ := socialMedian_update_eq_of_proxy_lt hjl (le_refl _)
      have hs'jl : Function.update pp jl (socialMedian pp q) jl
          = socialMedian pp q := Function.update_self ..
      have hd := delegate_dist_le
        (Function.update pp jl (socialMedian pp q))
        (socialMedian (Function.update pp jl (socialMedian pp q)) q) jl
      rw [hμ, hs'jl, sub_self, abs_zero] at hd
      have hout : outcome (Function.update pp jl (socialMedian pp q)) q
          = socialMedian pp q := by
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simpa [outcome, winner, hμ] using h0
      rw [hout]
      exact Or.inl ⟨le_of_lt hjl, hc⟩

/-- **Theorem 2** (Bielous–Meir), Euclidean form.  In the truthful state, some
proxy has a report that moves the outcome strictly closer to their peak iff no
proxy sits at the population median and proxies are present strictly on both
sides of it. -/
theorem proxy_manipulation_iff_prefers (pp : P → ℝ) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        Prefers pp j (outcome (Function.update pp j r) q) (outcome pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) := by
  constructor
  · rintro ⟨j, r, hpref⟩
    simp only [Prefers] at hpref
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have := (no_manipulation_of_proxy_at_median hk j r).abs_le
      linarith
    · by_contra hno
      rw [not_exists] at hno
      have := (no_manipulation_of_proxies_ge (fun k => not_lt.mp (hno k)) j r).abs_le
      linarith
    · by_contra hno
      rw [not_exists] at hno
      have := (no_manipulation_of_proxies_le (fun k => not_lt.mp (hno k)) j r).abs_le
      linarith
  · intro h
    obtain ⟨j, r, hpref⟩ := (proxy_manipulation_iff pp q).mpr h
    exact ⟨j, r, hpref.abs_lt⟩

/-- **Theorem 2** (Bielous–Meir), general single-peaked form.  For any family
of proxy preferences `spref` that is irreflexive (`hirr`), respects the
single-peaked geometry (`hresp`: it never strictly ranks an outcome above one
that single-peakedness forces the other way), and extends the forced
single-peaked comparisons (`hext`) — the order axioms characterizing
single-peaked, possibly *asymmetric*, preferences — some proxy has a
manipulation in the truthful state iff no proxy sits at the population median
and proxies are present strictly on both sides of it.  This is the form matching
the paper's model; the `SPPrefers` and Euclidean characterizations above are the
instances at the minimal such preference and at Euclidean distance, which
satisfy all three hypotheses.  These hypotheses are definitionally
`StrictPrefIrrefl`, `StrictPrefRespectsSinglePeaked`, and
`StrictPrefExtendsSinglePeaked` from `ProxyVoting.Preferences`. -/
theorem proxy_manipulation_iff_of_singlePeaked {spref : P → ℝ → ℝ → Prop}
    (hirr : ∀ j x, ¬ spref j x x)
    (hresp : ∀ j {x y}, spref j x y → ¬ SPPrefers (pp j) y x)
    (hext : ∀ j {x y}, SPPrefers (pp j) x y → spref j x y) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        spref j (outcome (Function.update pp j r) q) (outcome pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) := by
  constructor
  · rintro ⟨j, r, hpref⟩
    have hfalse : SPWeaklyPrefers (pp j) (outcome pp q)
        (outcome (Function.update pp j r) q) → False := by
      intro hsw
      by_cases hne : outcome pp q = outcome (Function.update pp j r) q
      · rw [← hne] at hpref
        exact hirr j _ hpref
      · exact hresp j hpref (hsw.spPrefers_of_ne hne)
    refine ⟨fun k hk => hfalse (no_manipulation_of_proxy_at_median hk j r), ?_, ?_⟩
    · by_contra hno
      rw [not_exists] at hno
      exact hfalse (no_manipulation_of_proxies_ge (fun k => not_lt.mp (hno k)) j r)
    · by_contra hno
      rw [not_exists] at hno
      exact hfalse (no_manipulation_of_proxies_le (fun k => not_lt.mp (hno k)) j r)
  · intro h
    obtain ⟨j, r, hsp⟩ := (proxy_manipulation_iff pp q).mpr h
    exact ⟨j, r, hext j hsp⟩

end ProxyManipulation

end ProxyVoting

end GameTheory
