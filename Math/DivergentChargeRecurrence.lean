/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic
import Mathlib.Topology.Sequences

/-!
# Compact recurrence across a divergent charge block

Compact recurrence by itself need not produce a return small relative to a
vanishing one-step charge.  The correct denominator for a cyclic affine
closing argument is instead the charge accumulated over the whole returned
segment.

This file proves the game-free selection principle.  If a sequence remains in
a compact metric set and a nonnegative charge has divergent partial sums, then
for every metric tolerance and every prescribed charge budget there are two
ordered visits which are close while the charge accumulated between them is at
least that budget.

The second part records the elementary survival estimate

`prod (1 - q_k) * (1 + sum q_k) <= 1`.

Consequently a segment with raw charge at least one has aggregate absorption
`1 - prod (1 - q_k)` at least one half.  This is the fixed denominator needed
to close an exact affine/Bellman orbit with one small endpoint seam.
-/

noncomputable section

namespace Math

open Filter Set Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- **Compact return with an arbitrarily large prefix-clock gap.**

A sequence in a compact metric set has a convergent subsequence.  Composing an
unbounded prefix clock with the strictly increasing subsequence leaves it
unbounded, so two sufficiently late visits are simultaneously close and
separated by any prescribed clock gap. -/
theorem exists_close_pair_with_large_prefix_gap_of_compact
    (K : Set X) (hK : IsCompact K)
    (state : ℕ → X) (hstate : ∀ n, state n ∈ K)
    (clock : ℕ → ℝ) (hclock : Tendsto clock atTop atTop)
    (radius gap : ℝ) (hradius : 0 < radius) :
    ∃ first second : ℕ,
      first < second ∧
      dist (state first) (state second) < radius ∧
      gap ≤ clock second - clock first := by
  obtain ⟨limit, _hlimit, subsequence, hsubsequence, hconverges⟩ :=
    hK.tendsto_subseq hstate
  have hhalf : 0 < radius / 2 := by
    linarith
  have hclose : ∀ᶠ rank : ℕ in atTop,
      dist (state (subsequence rank)) limit < radius / 2 := by
    have hball : ∀ᶠ rank : ℕ in atTop,
        (state ∘ subsequence) rank ∈ Metric.ball limit (radius / 2) :=
      hconverges (Metric.ball_mem_nhds limit hhalf)
    simpa only [Function.comp_apply, Metric.mem_ball] using hball
  obtain ⟨firstRank, hcloseFrom⟩ := Filter.eventually_atTop.1 hclose
  have hfirstClose :
      dist (state (subsequence firstRank)) limit < radius / 2 :=
    hcloseFrom firstRank le_rfl
  have hclockSubsequence :
      Tendsto (clock ∘ subsequence) atTop atTop :=
    hclock.comp hsubsequence.tendsto_atTop
  have hlarge : ∀ᶠ rank : ℕ in atTop,
      clock (subsequence firstRank) + gap ≤
        clock (subsequence rank) := by
    have h := hclockSubsequence
      (eventually_ge_atTop (clock (subsequence firstRank) + gap))
    simpa only [Function.comp_apply] using h
  have hlater : ∀ᶠ rank : ℕ in atTop, firstRank + 1 ≤ rank :=
    eventually_ge_atTop (firstRank + 1)
  obtain ⟨secondRank, hsecondClose, hsecondLarge, hsecondLater⟩ :=
    (hclose.and (hlarge.and hlater)).exists
  refine ⟨subsequence firstRank, subsequence secondRank, ?_, ?_, ?_⟩
  · exact hsubsequence
      (lt_of_lt_of_le (Nat.lt_succ_self firstRank) hsecondLater)
  · calc
      dist (state (subsequence firstRank))
          (state (subsequence secondRank)) ≤
        dist (state (subsequence firstRank)) limit +
          dist limit (state (subsequence secondRank)) :=
        dist_triangle _ _ _
      _ = dist (state (subsequence firstRank)) limit +
          dist (state (subsequence secondRank)) limit := by
        rw [dist_comm limit]
      _ < radius := by
        linarith
  · linarith

/-- Nonnegative nonsummable charge supplies the unbounded prefix clock in
`exists_close_pair_with_large_prefix_gap_of_compact`. -/
theorem exists_close_pair_with_large_charge_gap_of_compact
    (K : Set X) (hK : IsCompact K)
    (state : ℕ → X) (hstate : ∀ n, state n ∈ K)
    (charge : ℕ → ℝ) (hcharge : ∀ n, 0 ≤ charge n)
    (hdiverges : ¬Summable charge)
    (radius gap : ℝ) (hradius : 0 < radius) :
    ∃ first second : ℕ,
      first < second ∧
      dist (state first) (state second) < radius ∧
      gap ≤
        (∑ n ∈ Finset.range second, charge n) -
          ∑ n ∈ Finset.range first, charge n := by
  exact exists_close_pair_with_large_prefix_gap_of_compact
    K hK state hstate
    (fun cutoff => ∑ n ∈ Finset.range cutoff, charge n)
    ((not_summable_iff_tendsto_nat_atTop_of_nonneg hcharge).1 hdiverges)
    radius gap hradius

/-- Survival times one plus cumulative hazard is at most one.

The estimate is sharper than the exponential bound needed for recurrence
closing and uses only `0 <= q_k <= 1`. -/
theorem prod_one_sub_mul_one_add_sum_range_le_one
    (charge : ℕ → ℝ)
    (hcharge0 : ∀ n, 0 ≤ charge n)
    (hcharge1 : ∀ n, charge n ≤ 1)
    (start fuel : ℕ) :
    (∏ offset ∈ Finset.range fuel,
        (1 - charge (start + offset))) *
      (1 + ∑ offset ∈ Finset.range fuel,
        charge (start + offset)) ≤ 1 := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hq0 : 0 ≤ charge (start + fuel) :=
        hcharge0 (start + fuel)
      have hq1 : charge (start + fuel) ≤ 1 :=
        hcharge1 (start + fuel)
      have hsum0 : 0 ≤ ∑ offset ∈ Finset.range fuel,
          charge (start + offset) :=
        Finset.sum_nonneg fun offset _ => hcharge0 (start + offset)
      have hprod0 : 0 ≤ ∏ offset ∈ Finset.range fuel,
          (1 - charge (start + offset)) :=
        Finset.prod_nonneg fun offset _ => by
          linarith [hcharge1 (start + offset)]
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        ((∏ offset ∈ Finset.range fuel,
              (1 - charge (start + offset))) *
            (1 - charge (start + fuel))) *
            (1 + ((∑ offset ∈ Finset.range fuel,
              charge (start + offset)) + charge (start + fuel))) =
          (∏ offset ∈ Finset.range fuel,
              (1 - charge (start + offset))) *
            ((1 - charge (start + fuel)) *
              (1 + (∑ offset ∈ Finset.range fuel,
                charge (start + offset)) + charge (start + fuel))) := by
          ring
        _ ≤ (∏ offset ∈ Finset.range fuel,
              (1 - charge (start + offset))) *
            (1 + ∑ offset ∈ Finset.range fuel,
              charge (start + offset)) := by
          apply mul_le_mul_of_nonneg_left _ hprod0
          nlinarith [sq_nonneg (charge (start + fuel))]
        _ ≤ 1 := ih

/-- A block whose raw hazards sum to at least one absorbs with probability at
least one half. -/
theorem half_le_one_sub_prod_one_sub_of_one_le_sum_range
    (charge : ℕ → ℝ)
    (hcharge0 : ∀ n, 0 ≤ charge n)
    (hcharge1 : ∀ n, charge n ≤ 1)
    (start fuel : ℕ)
    (hsum : 1 ≤ ∑ offset ∈ Finset.range fuel,
      charge (start + offset)) :
    (1 : ℝ) / 2 ≤
      1 - ∏ offset ∈ Finset.range fuel,
        (1 - charge (start + offset)) := by
  have hprod0 : 0 ≤ ∏ offset ∈ Finset.range fuel,
      (1 - charge (start + offset)) :=
    Finset.prod_nonneg fun offset _ => by
      linarith [hcharge1 (start + offset)]
  have hmain := prod_one_sub_mul_one_add_sum_range_le_one
    charge hcharge0 hcharge1 start fuel
  have htwo :
      2 * (∏ offset ∈ Finset.range fuel,
        (1 - charge (start + offset))) ≤ 1 := by
    calc
      2 * (∏ offset ∈ Finset.range fuel,
          (1 - charge (start + offset))) ≤
        (1 + ∑ offset ∈ Finset.range fuel,
          charge (start + offset)) *
            (∏ offset ∈ Finset.range fuel,
              (1 - charge (start + offset))) := by
          apply mul_le_mul_of_nonneg_right _ hprod0
          linarith
      _ = (∏ offset ∈ Finset.range fuel,
          (1 - charge (start + offset))) *
            (1 + ∑ offset ∈ Finset.range fuel,
              charge (start + offset)) := by
          ring
      _ ≤ 1 := hmain
  linarith

end Math
