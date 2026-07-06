/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Weighted medians of finite real position families

A *weighted median* of a finite family of real positions is a point with at
most half the total weight strictly on each side.  This file defines the
predicate, a canonical choice `weightedMedian` — the least attained position at
which the cumulative weight reaches half the total — and the lemmas that drive
median-based voting rules:

* `isWeightedMedian_weightedMedian` — the canonical choice is a weighted median;
* `weightedMedian_le_weightedMedian_of_le` — the canonical median is monotone in
  the positions;
* `weightedMedian_update_eq_of_lt_of_le` / `weightedMedian_update_eq_of_gt_of_ge`
  — the median does not move when a position strictly on one side changes
  without crossing to the other side;
* `abs_weightedMedian_sub_le_update` — moving a single position cannot bring the
  median strictly closer to that position's original location.  This is the
  core of the strategyproofness of the median rule for symmetric single-peaked
  preferences (Moulin 1980).
-/

namespace Math

open Finset

variable {α : Type*} [Fintype α]

/-- Total weight at positions at most `x`. -/
noncomputable def cumWeight (pos : α → ℝ) (w : α → ℕ) (x : ℝ) : ℕ :=
  ∑ a ∈ univ.filter (fun a => pos a ≤ x), w a

/-- Total weight at positions strictly below `x`. -/
noncomputable def leftWeight (pos : α → ℝ) (w : α → ℕ) (x : ℝ) : ℕ :=
  ∑ a ∈ univ.filter (fun a => pos a < x), w a

/-- Total weight at positions strictly above `x`. -/
noncomputable def rightWeight (pos : α → ℝ) (w : α → ℕ) (x : ℝ) : ℕ :=
  ∑ a ∈ univ.filter (fun a => x < pos a), w a

/-- Total weight of the family. -/
def totalWeight (w : α → ℕ) : ℕ := ∑ a, w a

/-- `x` is a weighted median when at most half the total weight lies strictly
on each side of `x`. -/
def IsWeightedMedian (pos : α → ℝ) (w : α → ℕ) (x : ℝ) : Prop :=
  2 * leftWeight pos w x ≤ totalWeight w ∧ 2 * rightWeight pos w x ≤ totalWeight w

section Basic

variable (pos : α → ℝ) (w : α → ℕ) (x y : ℝ)

theorem cumWeight_add_rightWeight :
    cumWeight pos w x + rightWeight pos w x = totalWeight w := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not univ (fun a => pos a ≤ x) w
  simpa [cumWeight, rightWeight, totalWeight, not_le] using h

theorem cumWeight_mono (hxy : x ≤ y) : cumWeight pos w x ≤ cumWeight pos w y := by
  refine Finset.sum_le_sum_of_subset ?_
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  exact le_trans ha hxy

theorem cumWeight_le_totalWeight : cumWeight pos w x ≤ totalWeight w := by
  refine Finset.sum_le_sum_of_subset ?_
  exact filter_subset _ _

/-- If some weight sits at or below `x`, the greatest attained position at or
below `x` has the same cumulative weight as `x`. -/
theorem exists_attained_cumWeight_eq {pos : α → ℝ} {w : α → ℕ} {x : ℝ}
    (h : 0 < cumWeight pos w x) :
    ∃ a : α, pos a ≤ x ∧ cumWeight pos w (pos a) = cumWeight pos w x := by
  classical
  have hne : (univ.filter fun a => pos a ≤ x).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [cumWeight, hne] at h
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image _ pos hne
  simp only [mem_filter, mem_univ, true_and] at hb
  refine ⟨b, hb, ?_⟩
  unfold cumWeight
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro ha; exact le_trans ha hb
  · intro ha
    exact hmax a (by simp only [mem_filter, mem_univ, true_and]; exact ha)

@[simp] theorem cumWeight_one (pos : α → ℝ) (x : ℝ) :
    cumWeight pos (fun _ => 1) x = (univ.filter fun a => pos a ≤ x).card := by
  simp [cumWeight]

@[simp] theorem leftWeight_one (pos : α → ℝ) (x : ℝ) :
    leftWeight pos (fun _ => 1) x = (univ.filter fun a => pos a < x).card := by
  simp [leftWeight]

@[simp] theorem rightWeight_one (pos : α → ℝ) (x : ℝ) :
    rightWeight pos (fun _ => 1) x = (univ.filter fun a => x < pos a).card := by
  simp [rightWeight]

@[simp] theorem totalWeight_one :
    totalWeight (fun _ : α => 1) = Fintype.card α := by
  simp [totalWeight, Finset.card_univ]

theorem totalWeight_one_pos [Nonempty α] :
    0 < totalWeight (fun _ : α => 1) := by
  rw [totalWeight_one]
  exact Fintype.card_pos_iff.mpr inferInstance

/-- Comparison of cumulative weights along a pointwise implication between
position families. -/
theorem cumWeight_le_cumWeight_of_imp {pos pos' : α → ℝ} (w : α → ℕ) {x x' : ℝ}
    (h : ∀ a, pos a ≤ x → pos' a ≤ x') :
    cumWeight pos w x ≤ cumWeight pos' w x' := by
  refine Finset.sum_le_sum_of_subset ?_
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  exact h a ha

end Basic

section Median

variable [Nonempty α] (pos : α → ℝ) (w : α → ℕ)

/-- The candidate set for the canonical weighted median: attained positions at
which the cumulative weight reaches half the total. -/
theorem medianCandidates_nonempty :
    ((univ.image pos).filter fun p => totalWeight w ≤ 2 * cumWeight pos w p).Nonempty := by
  classical
  have himg : (univ.image pos).Nonempty := (univ_nonempty).image pos
  set p₀ := (univ.image pos).max' himg with hp₀
  refine ⟨p₀, mem_filter.mpr ⟨(univ.image pos).max'_mem himg, ?_⟩⟩
  have hall : cumWeight pos w p₀ = totalWeight w := by
    unfold cumWeight totalWeight
    congr 1
    refine Finset.filter_true_of_mem ?_
    intro a _
    exact Finset.le_max' _ _ (mem_image_of_mem pos (mem_univ a))
  omega

/-- The canonical weighted median: the least attained position at which the
cumulative weight reaches half the total weight. -/
noncomputable def weightedMedian : ℝ :=
  (((univ : Finset α).image pos).filter
    fun p => totalWeight w ≤ 2 * cumWeight pos w p).min'
      (medianCandidates_nonempty pos w)

theorem weightedMedian_mem_image : weightedMedian pos w ∈ univ.image pos :=
  (mem_filter.mp (Finset.min'_mem _ (medianCandidates_nonempty pos w))).1

theorem exists_pos_eq_weightedMedian : ∃ a, pos a = weightedMedian pos w := by
  have h := weightedMedian_mem_image pos w
  simp only [mem_image, mem_univ, true_and] at h
  exact h

theorem totalWeight_le_two_mul_cumWeight_weightedMedian :
    totalWeight w ≤ 2 * cumWeight pos w (weightedMedian pos w) :=
  (mem_filter.mp (Finset.min'_mem _ (medianCandidates_nonempty pos w))).2

theorem weightedMedian_le {pos : α → ℝ} {w : α → ℕ} {p : ℝ}
    (hp : p ∈ univ.image pos) (h : totalWeight w ≤ 2 * cumWeight pos w p) :
    weightedMedian pos w ≤ p :=
  Finset.min'_le _ _ (mem_filter.mpr ⟨hp, h⟩)

/-- A qualifying attained point is the canonical weighted median if no smaller
attained point qualifies. -/
theorem weightedMedian_eq_of_candidate_of_forall_lt
    {pos : α → ℝ} {w : α → ℕ} {p : ℝ}
    (hp : p ∈ univ.image pos) (h : totalWeight w ≤ 2 * cumWeight pos w p)
    (hlt : ∀ q ∈ univ.image pos, q < p → 2 * cumWeight pos w q < totalWeight w) :
    weightedMedian pos w = p := by
  refine le_antisymm (weightedMedian_le hp h) ?_
  by_contra hle
  rw [not_le] at hle
  exact absurd (totalWeight_le_two_mul_cumWeight_weightedMedian pos w)
    (not_le.mpr (hlt (weightedMedian pos w) (weightedMedian_mem_image pos w) hle))

/-- A position carrying a strict majority of the total weight is the canonical
weighted median, regardless of how the remaining weight is placed. -/
theorem weightedMedian_eq_of_majority {pos : α → ℝ} {w : α → ℕ} {x : ℝ}
    (h : totalWeight w < 2 * ∑ a ∈ univ.filter fun a => pos a = x, w a) :
    weightedMedian pos w = x := by
  classical
  have hne : (univ.filter fun a => pos a = x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.sum_empty] at h
    omega
  obtain ⟨a, ha⟩ := hne
  have hax : pos a = x := (Finset.mem_filter.mp ha).2
  have hcum : ∑ a ∈ univ.filter (fun a => pos a = x), w a ≤ cumWeight pos w x := by
    unfold cumWeight
    refine Finset.sum_le_sum_of_subset fun b hb => ?_
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, le_of_eq hb.2⟩
  refine weightedMedian_eq_of_candidate_of_forall_lt
    (hax ▸ mem_image_of_mem pos (mem_univ a)) (by omega) fun z _ hzx => ?_
  have hdisj : Disjoint (univ.filter fun b => pos b ≤ z)
      (univ.filter fun b => pos b = x) := by
    refine Finset.disjoint_left.mpr fun b hbz hbx => ?_
    rw [Finset.mem_filter] at hbz hbx
    rw [hbx.2] at hbz
    exact absurd hbz.2 (not_le.mpr hzx)
  have hsplit : cumWeight pos w z + ∑ a ∈ univ.filter (fun a => pos a = x), w a
      ≤ totalWeight w := by
    unfold cumWeight totalWeight
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- The canonical weighted median is immune to a single coordinate: if `m` is
attained off `i`, the off-`i` weight weakly left of `m` reaches half the
total, and the off-`i` weight strictly left of `m` plus `i`'s full weight
stays strictly below half, then the median is `m` wherever `i` moves. -/
theorem weightedMedian_update_eq_of_pinned [DecidableEq α]
    {pos : α → ℝ} {w : α → ℕ} {i : α} {m : ℝ}
    (hattain : ∃ v, v ≠ i ∧ pos v = m)
    (hcum : totalWeight w
      ≤ 2 * ∑ v ∈ univ.filter fun v => v ≠ i ∧ pos v ≤ m, w v)
    (hbelow : 2 * ((∑ v ∈ univ.filter fun v => v ≠ i ∧ pos v < m, w v) + w i)
      < totalWeight w)
    (y : ℝ) : weightedMedian (Function.update pos i y) w = m := by
  classical
  obtain ⟨v₀, hv₀i, hv₀⟩ := hattain
  refine weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · refine mem_image.mpr ⟨v₀, mem_univ _, ?_⟩
    rw [Function.update_of_ne hv₀i, hv₀]
  · have hsub : (univ.filter fun v => v ≠ i ∧ pos v ≤ m)
        ⊆ univ.filter fun v => Function.update pos i y v ≤ m := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      rw [Function.update_of_ne hv.2.1]
      exact hv.2.2
    have hle : (∑ v ∈ univ.filter fun v => v ≠ i ∧ pos v ≤ m, w v)
        ≤ ∑ v ∈ univ.filter (fun v => Function.update pos i y v ≤ m), w v :=
      Finset.sum_le_sum_of_subset hsub
    unfold cumWeight
    omega
  · intro z _ hzm
    have hsub : (univ.filter fun v => Function.update pos i y v ≤ z)
        ⊆ insert i (univ.filter fun v => v ≠ i ∧ pos v < m) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      by_cases hvi : v = i
      · rw [hvi]
        exact Finset.mem_insert_self i _
      · refine Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨mem_univ _, hvi, ?_⟩)
        rw [Function.update_of_ne hvi] at hv
        exact lt_of_le_of_lt hv.2 hzm
    have hle : cumWeight (Function.update pos i y) w z
        ≤ (∑ v ∈ univ.filter fun v => v ≠ i ∧ pos v < m, w v) + w i := by
      calc cumWeight (Function.update pos i y) w z
          ≤ ∑ v ∈ insert i (univ.filter fun v => v ≠ i ∧ pos v < m), w v :=
            Finset.sum_le_sum_of_subset hsub
        _ = w i + ∑ v ∈ univ.filter fun v => v ≠ i ∧ pos v < m, w v := by
            rw [Finset.sum_insert (by simp)]
        _ = _ := by omega
    omega

/-- Below the canonical median the cumulative weight is strictly less than half
the total, at every real point. -/
theorem two_mul_cumWeight_lt_of_lt_weightedMedian {pos : α → ℝ} {w : α → ℕ} {p : ℝ}
    (hW : 0 < totalWeight w) (hp : p < weightedMedian pos w) :
    2 * cumWeight pos w p < totalWeight w := by
  by_contra h
  rw [not_lt] at h
  have hpos : 0 < cumWeight pos w p := by omega
  obtain ⟨a, ha, hcum⟩ := exists_attained_cumWeight_eq hpos
  have hqual : weightedMedian pos w ≤ pos a :=
    weightedMedian_le (mem_image_of_mem pos (mem_univ a)) (by omega)
  exact absurd (lt_of_le_of_lt (le_trans hqual ha) hp) (lt_irrefl _)

/-- Strictly less than half the total weight lies strictly below the canonical
least weighted median. -/
theorem two_mul_leftWeight_weightedMedian_lt (hW : 0 < totalWeight w) :
    2 * leftWeight pos w (weightedMedian pos w) < totalWeight w := by
  by_contra h
  rw [not_lt] at h
  have hpos : 0 < leftWeight pos w (weightedMedian pos w) := by omega
  have hne : (univ.filter fun a => pos a < weightedMedian pos w).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [leftWeight, hne] at hpos
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image _ pos hne
  simp only [mem_filter, mem_univ, true_and] at hb
  have hcum : cumWeight pos w (pos b) = leftWeight pos w (weightedMedian pos w) := by
    unfold cumWeight leftWeight
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro ha; exact lt_of_le_of_lt ha hb
    · intro ha
      exact hmax a (by simp only [mem_filter, mem_univ, true_and]; exact ha)
  have hqual : weightedMedian pos w ≤ pos b :=
    weightedMedian_le (mem_image_of_mem pos (mem_univ b)) (by omega)
  exact absurd (lt_of_le_of_lt hqual hb) (lt_irrefl _)

/-- The canonical choice is a weighted median. -/
theorem isWeightedMedian_weightedMedian :
    IsWeightedMedian pos w (weightedMedian pos w) := by
  constructor
  · by_cases hW : 0 < totalWeight w
    · exact le_of_lt (two_mul_leftWeight_weightedMedian_lt pos w hW)
    · have hle : leftWeight pos w (weightedMedian pos w) ≤ totalWeight w := by
        refine Finset.sum_le_sum_of_subset ?_
        exact filter_subset _ _
      omega
  · -- Right side: complement of the defining half-weight condition.
    have h₁ := totalWeight_le_two_mul_cumWeight_weightedMedian pos w
    have h₂ := cumWeight_add_rightWeight pos w (weightedMedian pos w)
    omega

/-- The canonical weighted median is monotone in the position family. -/
theorem weightedMedian_le_weightedMedian_of_le {pos pos' : α → ℝ} (w : α → ℕ)
    (hW : 0 < totalWeight w) (h : ∀ a, pos a ≤ pos' a) :
    weightedMedian pos w ≤ weightedMedian pos' w := by
  set m' := weightedMedian pos' w with hm'
  have hsub : cumWeight pos' w m' ≤ cumWeight pos w m' := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact le_trans (h a) ha
  have hcum : totalWeight w ≤ 2 * cumWeight pos w m' := by
    have hd := totalWeight_le_two_mul_cumWeight_weightedMedian pos' w
    rw [← hm'] at hd
    omega
  have hpos : 0 < cumWeight pos w m' := by omega
  obtain ⟨a, ha, hcumeq⟩ := exists_attained_cumWeight_eq hpos
  exact le_trans
    (weightedMedian_le (mem_image_of_mem pos (mem_univ a)) (by omega)) ha

/-- Lower-bound a canonical weighted median by showing that every point
strictly below the proposed bound comes from strictly below a reference
median. -/
theorem le_weightedMedian_of_imp_lt_weightedMedian
    {pos pos' : α → ℝ} {w : α → ℕ} {c : ℝ}
    (hW : 0 < totalWeight w)
    (himp : ∀ a, pos' a < c → pos a < weightedMedian pos w) :
    c ≤ weightedMedian pos' w := by
  by_contra hle
  rw [not_le] at hle
  have hsub : cumWeight pos' w (weightedMedian pos' w)
      ≤ leftWeight pos w (weightedMedian pos w) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact himp a (lt_of_le_of_lt ha hle)
  have hcum := totalWeight_le_two_mul_cumWeight_weightedMedian pos' w
  have hstrict := two_mul_leftWeight_weightedMedian_lt pos w hW
  omega

/-- Upper-bound a canonical weighted median by showing that every point
strictly above the proposed bound comes from strictly above a reference
median. -/
theorem weightedMedian_le_of_imp_weightedMedian_lt
    {pos pos' : α → ℝ} {w : α → ℕ} {c : ℝ}
    (hW : 0 < totalWeight w)
    (himp : ∀ a, c < pos' a → weightedMedian pos w < pos a) :
    weightedMedian pos' w ≤ c := by
  by_contra hle
  rw [not_le] at hle
  have hsub : cumWeight pos w (weightedMedian pos w) ≤ cumWeight pos' w c := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    by_contra hc
    rw [not_le] at hc
    have hpos := himp a hc
    exact absurd (lt_of_le_of_lt ha hpos) (lt_irrefl _)
  have hcum := totalWeight_le_two_mul_cumWeight_weightedMedian pos w
  have hstrict := two_mul_cumWeight_lt_of_lt_weightedMedian hW hle
  omega

/-- If the canonical weighted median strictly rises, some coordinate that was
weakly at or below the old median crosses strictly above it. -/
theorem exists_le_weightedMedian_lt_of_weightedMedian_lt
    {pos pos' : α → ℝ} {w : α → ℕ}
    (hW : 0 < totalWeight w) (h : weightedMedian pos w < weightedMedian pos' w) :
    ∃ a, pos a ≤ weightedMedian pos w ∧ weightedMedian pos w < pos' a := by
  by_contra hnone
  push Not at hnone
  have hsub : cumWeight pos w (weightedMedian pos w)
      ≤ cumWeight pos' w (weightedMedian pos w) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact hnone a ha
  have hcum := totalWeight_le_two_mul_cumWeight_weightedMedian pos w
  have hstrict := two_mul_cumWeight_lt_of_lt_weightedMedian hW h
  omega

/-- If the canonical weighted median strictly falls, some coordinate that was
strictly above the new median crosses weakly below it. -/
theorem exists_weightedMedian_lt_ge_of_weightedMedian_lt
    {pos pos' : α → ℝ} {w : α → ℕ}
    (hW : 0 < totalWeight w) (h : weightedMedian pos' w < weightedMedian pos w) :
    ∃ a, weightedMedian pos' w < pos a ∧ pos' a ≤ weightedMedian pos' w := by
  by_contra hnone
  push Not at hnone
  have hsub : cumWeight pos' w (weightedMedian pos' w)
      ≤ cumWeight pos w (weightedMedian pos' w) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    by_contra hle
    exact absurd (hnone a (lt_of_not_ge hle)) (not_lt.mpr ha)
  have hcum := totalWeight_le_two_mul_cumWeight_weightedMedian pos' w
  have hstrict := two_mul_cumWeight_lt_of_lt_weightedMedian hW h
  omega

/-- With positive total weight, the canonical weighted median is attained at a
position of positive weight: zero-weight members never determine it. -/
theorem exists_pos_weight_eq_weightedMedian {pos : α → ℝ} {w : α → ℕ}
    (hW : 0 < totalWeight w) :
    ∃ a, 0 < w a ∧ pos a = weightedMedian pos w := by
  classical
  have hcum : totalWeight w ≤ 2 * cumWeight pos w (weightedMedian pos w) :=
    totalWeight_le_two_mul_cumWeight_weightedMedian pos w
  have hcpos : 0 < cumWeight pos w (weightedMedian pos w) := by omega
  have hne : (univ.filter fun a =>
      0 < w a ∧ pos a ≤ weightedMedian pos w).Nonempty := by
    obtain ⟨a, ha, hwa⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcpos.ne'
    simp only [mem_filter, mem_univ, true_and] at ha
    exact ⟨a, mem_filter.mpr ⟨mem_univ a, Nat.pos_of_ne_zero hwa, ha⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image _ pos hne
  simp only [mem_filter, mem_univ, true_and] at hb
  obtain ⟨hwb, hbm⟩ := hb
  have hcumeq : cumWeight pos w (pos b)
      = cumWeight pos w (weightedMedian pos w) := by
    unfold cumWeight
    refine Finset.sum_subset ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact le_trans ha hbm
    · intro a ha hna
      simp only [mem_filter, mem_univ, true_and] at ha hna
      by_contra hwa0
      exact hna (hmax a (mem_filter.mpr
        ⟨mem_univ a, Nat.pos_of_ne_zero hwa0, ha⟩))
  have hle : weightedMedian pos w ≤ pos b :=
    weightedMedian_le (mem_image_of_mem pos (mem_univ b)) (by omega)
  exact ⟨b, hwb, le_antisymm hbm hle⟩

end Median

section UpdateBounds

variable [DecidableEq α]

/-- Cumulative weight after an update, bounded by the cumulative weight at the
larger of the evaluation point and the updated coordinate's old position. -/
theorem cumWeight_update_le (pos : α → ℝ) (w : α → ℕ) (i : α) (x q : ℝ) :
    cumWeight (Function.update pos i x) w q ≤ cumWeight pos w (max q (pos i)) := by
  refine Finset.sum_le_sum_of_subset ?_
  intro a ha
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  by_cases hai : a = i
  · subst hai; exact le_max_right _ _
  · rw [Function.update_apply, if_neg hai] at ha
    exact le_trans ha (le_max_left _ _)

/-- An update below both the evaluation point's strict bounds leaves the
cumulative weight unchanged. -/
theorem cumWeight_update_eq_of_lt_of_lt (pos : α → ℝ) (w : α → ℕ) (i : α)
    {x q : ℝ} (hqi : q < pos i) (hqx : q < x) :
    cumWeight (Function.update pos i x) w q = cumWeight pos w q := by
  unfold cumWeight
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  by_cases hai : a = i
  · subst hai
    rw [Function.update_self]
    constructor
    · intro h; exact absurd (lt_of_le_of_lt h hqx) (lt_irrefl _)
    · intro h; exact absurd (lt_of_le_of_lt h hqi) (lt_irrefl _)
  · rw [Function.update_apply, if_neg hai]

end UpdateBounds

section Update

variable [Nonempty α] [DecidableEq α] {pos : α → ℝ} {w : α → ℕ} {i : α} {x : ℝ}

/-- Moving a position that sits strictly left of the canonical median to any
point still weakly left of the median does not move the median. -/
theorem weightedMedian_update_eq_of_lt_of_le (hW : 0 < totalWeight w)
    (hi : pos i < weightedMedian pos w) (hx : x ≤ weightedMedian pos w) :
    weightedMedian (Function.update pos i x) w = weightedMedian pos w := by
  classical
  set m := weightedMedian pos w with hm
  -- The median's cumulative weight is unchanged: the updated coordinate stays
  -- weakly below `m` on both sides of the update.
  have hcum_eq : cumWeight (Function.update pos i x) w m = cumWeight pos w m := by
    unfold cumWeight
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and]
    by_cases hai : a = i
    · subst hai
      rw [Function.update_self]
      exact ⟨fun _ => le_of_lt hi, fun _ => hx⟩
    · rw [Function.update_apply, if_neg hai]
  -- `m` is attained by a coordinate other than `i`.
  have hmem : m ∈ univ.image (Function.update pos i x) := by
    obtain ⟨a, ha⟩ := exists_pos_eq_weightedMedian pos w
    have hai : a ≠ i := by
      intro h; subst h
      exact absurd (ha ▸ hi) (lt_irrefl _)
    refine mem_image.mpr ⟨a, mem_univ a, ?_⟩
    rw [Function.update_apply, if_neg hai]
    exact ha
  refine le_antisymm ?_ ?_
  · exact weightedMedian_le hmem
      (by rw [hcum_eq]; exact totalWeight_le_two_mul_cumWeight_weightedMedian pos w)
  · -- No candidate strictly below `m` qualifies after the update.
    refine Finset.le_min' _ _ _ ?_
    intro q hq
    simp only [mem_filter] at hq
    by_contra hqm
    rw [not_le] at hqm
    have hle : cumWeight (Function.update pos i x) w q
        ≤ cumWeight pos w (max q (pos i)) := cumWeight_update_le pos w i x q
    have hmax_lt : max q (pos i) < m := max_lt hqm hi
    have := two_mul_cumWeight_lt_of_lt_weightedMedian hW hmax_lt
    omega

/-- Moving a position that sits strictly right of the canonical median to any
point still weakly right of the median does not move the median. -/
theorem weightedMedian_update_eq_of_gt_of_ge (hW : 0 < totalWeight w)
    (hi : weightedMedian pos w < pos i) (hx : weightedMedian pos w ≤ x) :
    weightedMedian (Function.update pos i x) w = weightedMedian pos w := by
  classical
  set m := weightedMedian pos w with hm
  -- The updated coordinate contributes to the cumulative weight at `m` at most
  -- as much as before (namely, not at all before; possibly at `x = m` after).
  have hcum_ge : cumWeight pos w m ≤ cumWeight (Function.update pos i x) w m := by
    refine Finset.sum_le_sum_of_subset ?_
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    have hai : a ≠ i := by
      intro h; subst h
      exact absurd (lt_of_le_of_lt ha hi) (lt_irrefl _)
    rw [Function.update_apply, if_neg hai]
    exact ha
  have hmem : m ∈ univ.image (Function.update pos i x) := by
    obtain ⟨a, ha⟩ := exists_pos_eq_weightedMedian pos w
    have hai : a ≠ i := by
      intro h; subst h
      exact absurd (ha ▸ hi) (lt_irrefl _)
    refine mem_image.mpr ⟨a, mem_univ a, ?_⟩
    rw [Function.update_apply, if_neg hai]
    exact ha
  refine le_antisymm ?_ ?_
  · refine weightedMedian_le hmem ?_
    have hd := totalWeight_le_two_mul_cumWeight_weightedMedian pos w
    rw [← hm] at hd
    omega
  · refine Finset.le_min' _ _ _ ?_
    intro q hq
    simp only [mem_filter] at hq
    by_contra hqm
    rw [not_le] at hqm
    have heq : cumWeight (Function.update pos i x) w q = cumWeight pos w q :=
      cumWeight_update_eq_of_lt_of_lt pos w i (lt_trans hqm hi)
        (lt_of_lt_of_le hqm hx)
    have := two_mul_cumWeight_lt_of_lt_weightedMedian hW hqm
    omega

/-- **Median strategyproofness core** (Moulin 1980).  Changing a single position
cannot move the canonical weighted median strictly closer to that position's
original location. -/
theorem abs_weightedMedian_sub_le_update (hW : 0 < totalWeight w) (i : α) (x : ℝ) :
    |weightedMedian pos w - pos i|
      ≤ |weightedMedian (Function.update pos i x) w - pos i| := by
  set m := weightedMedian pos w with hm
  set m' := weightedMedian (Function.update pos i x) w with hm'
  rcases lt_trichotomy (pos i) m with hi | hi | hi
  · rcases le_or_gt x m with hx | hx
    · rw [hm', weightedMedian_update_eq_of_lt_of_le hW hi hx]
    · -- The update raises the position, so the median weakly rises: it moves
      -- weakly away from `pos i`.
      have hmono : m ≤ m' := by
        refine weightedMedian_le_weightedMedian_of_le w hW ?_
        intro a
        by_cases hai : a = i
        · subst hai
          rw [Function.update_self]
          exact le_of_lt (lt_trans hi hx)
        · rw [Function.update_apply, if_neg hai]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
  · rw [← hi]
    simp [abs_nonneg]
  · rcases le_or_gt m x with hx | hx
    · rw [hm', weightedMedian_update_eq_of_gt_of_ge hW hi hx]
    · have hmono : m' ≤ m := by
        refine weightedMedian_le_weightedMedian_of_le w hW ?_
        intro a
        by_cases hai : a = i
        · subst hai
          rw [Function.update_self]
          exact le_of_lt (lt_trans hx hi)
        · rw [Function.update_apply, if_neg hai]
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith

/-- A position attained by a coordinate other than the updated one, strictly
above the canonical median, remains an upper bound for the median after the
update, provided the updated coordinate carries no more weight. -/
theorem weightedMedian_update_le_of_lt {a : α}
    (hai : a ≠ i) (hw : w i ≤ w a) (h : weightedMedian pos w < pos a) :
    weightedMedian (Function.update pos i x) w ≤ pos a := by
  classical
  refine weightedMedian_le ?_ ?_
  · refine mem_image.mpr ⟨a, mem_univ a, ?_⟩
    rw [Function.update_apply, if_neg hai]
  · have hsplit : cumWeight pos w (weightedMedian pos w)
        ≤ w i + ∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w, w b := by
      have hsub : univ.filter (fun b => pos b ≤ weightedMedian pos w)
          ⊆ insert i (univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w) := by
        intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        by_cases hbi : b = i
        · subst hbi; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ b, hbi, hb⟩)
      calc cumWeight pos w (weightedMedian pos w)
          ≤ ∑ b ∈ insert i (univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w), w b :=
            Finset.sum_le_sum_of_subset hsub
        _ = w i + ∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w, w b := by
            rw [Finset.sum_insert (by simp)]
    have hins : (∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w, w b) + w a
        ≤ cumWeight (Function.update pos i x) w (pos a) := by
      have hnotmem : a ∉ univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w := by
        simp only [mem_filter, mem_univ, true_and, not_and]
        intro _
        exact not_le.mpr h
      have hsub : insert a (univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w)
          ⊆ univ.filter fun b => Function.update pos i x b ≤ pos a := by
        intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · simp only [mem_filter, mem_univ, true_and]
          rw [Function.update_apply, if_neg hai]
        · simp only [mem_filter, mem_univ, true_and] at hb ⊢
          rw [Function.update_apply, if_neg hb.1]
          exact le_of_lt (lt_of_le_of_lt hb.2 h)
      calc (∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w, w b) + w a
          = ∑ b ∈ insert a (univ.filter fun b => b ≠ i ∧ pos b ≤ weightedMedian pos w), w b := by
            rw [Finset.sum_insert hnotmem, add_comm]
        _ ≤ _ := Finset.sum_le_sum_of_subset hsub
    have hmed := totalWeight_le_two_mul_cumWeight_weightedMedian pos w
    omega

/-- A position attained by a coordinate other than the updated one, strictly
below the canonical median, remains a lower bound for the median after the
update, provided the updated coordinate carries no more weight. -/
theorem le_weightedMedian_update_of_lt {a : α}
    (hai : a ≠ i) (hw : w i ≤ w a) (hW : 0 < totalWeight w)
    (h : pos a < weightedMedian pos w) :
    pos a ≤ weightedMedian (Function.update pos i x) w := by
  classical
  by_contra hle
  rw [not_le] at hle
  set m' := weightedMedian (Function.update pos i x) w with hm'
  have hqual := totalWeight_le_two_mul_cumWeight_weightedMedian (Function.update pos i x) w
  rw [← hm'] at hqual
  have h1 : cumWeight (Function.update pos i x) w m'
      ≤ w i + ∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ m', w b := by
    have hsub : univ.filter (fun b => Function.update pos i x b ≤ m')
        ⊆ insert i (univ.filter fun b => b ≠ i ∧ pos b ≤ m') := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      by_cases hbi : b = i
      · subst hbi; exact mem_insert_self _ _
      · rw [Function.update_apply, if_neg hbi] at hb
        exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ b, hbi, hb⟩)
    calc cumWeight (Function.update pos i x) w m'
        ≤ ∑ b ∈ insert i (univ.filter fun b => b ≠ i ∧ pos b ≤ m'), w b :=
          Finset.sum_le_sum_of_subset hsub
      _ = w i + ∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ m', w b := by
          rw [Finset.sum_insert (by simp)]
  have h2 : (∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ m', w b) + w a
      ≤ cumWeight pos w (pos a) := by
    have hnotmem : a ∉ univ.filter fun b => b ≠ i ∧ pos b ≤ m' := by
      simp only [mem_filter, mem_univ, true_and, not_and]
      intro _
      exact not_le.mpr hle
    have hsub : insert a (univ.filter fun b => b ≠ i ∧ pos b ≤ m')
        ⊆ univ.filter fun b => pos b ≤ pos a := by
      intro b hb
      rcases mem_insert.mp hb with rfl | hb
      · simp
      · simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact le_of_lt (lt_of_le_of_lt hb.2 hle)
    calc (∑ b ∈ univ.filter fun b => b ≠ i ∧ pos b ≤ m', w b) + w a
        = ∑ b ∈ insert a (univ.filter fun b => b ≠ i ∧ pos b ≤ m'), w b := by
          rw [Finset.sum_insert hnotmem, add_comm]
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have h3 := two_mul_cumWeight_lt_of_lt_weightedMedian hW h
  omega

end Update

end Math
