/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite charged return

An infinite nonsummable orbit is not needed to obtain a charged compact
return.  Suppose a finite path is labelled by one of `m` cells, and its
nondecreasing prefix clock moves by at most one per step.  If the clock gains
at least `2m`, then two ordered times have the same label and are separated by
clock gain at least one.

The proof samples the first hitting times of the levels

`clock 0 + 2j`, `j = 0, ..., m`.

There are `m + 1` samples and only `m` labels.  A repeated label at ranks
`j < k` gives clock gap at least one: the later sample is at or above level
`2k`, while minimality and the unit step bound put the earlier sample strictly
below level `2j + 1`.

This is the finite quantifier form needed by projective-lasso closing.  For a
fixed metric tolerance, choose a finite cover of the compact value box and ask
the orbit producer for one prefix with charge at least twice the number of
cover cells.  No single orbit has to work for every charge target.
-/

noncomputable section

namespace Math

/-- **Finite charged-return pigeonhole theorem.** -/
theorem exists_same_label_with_large_clock_gap
    {Cell : Type*} [Fintype Cell]
    (label : ℕ → Cell) (clock : ℕ → ℝ) (horizon : ℕ)
    (hstep0 : ∀ time, clock time ≤ clock (time + 1))
    (hstep1 : ∀ time, clock (time + 1) ≤ clock time + 1)
    (hlarge :
      clock 0 + 2 * (Fintype.card Cell : ℝ) ≤ clock horizon) :
    ∃ first second : ℕ,
      first < second ∧ second ≤ horizon ∧
      label first = label second ∧
      1 ≤ clock second - clock first := by
  classical
  let level : Fin (Fintype.card Cell + 1) → ℝ := fun rank =>
    clock 0 + 2 * (rank.val : ℝ)
  have hexists : ∀ rank : Fin (Fintype.card Cell + 1),
      ∃ time : ℕ, time ≤ horizon ∧ level rank ≤ clock time := by
    intro rank
    refine ⟨horizon, le_rfl, ?_⟩
    have hrank : (rank.val : ℝ) ≤ Fintype.card Cell := by
      exact_mod_cast Nat.le_of_lt_succ rank.isLt
    dsimp only [level]
    linarith
  let hit : Fin (Fintype.card Cell + 1) → ℕ := fun rank =>
    Nat.find (hexists rank)
  have hhit_spec : ∀ rank : Fin (Fintype.card Cell + 1),
      hit rank ≤ horizon ∧ level rank ≤ clock (hit rank) := by
    intro rank
    exact Nat.find_spec (hexists rank)
  have hmono : Monotone clock := monotone_nat_of_le_succ hstep0
  have hhit_upper : ∀ rank : Fin (Fintype.card Cell + 1),
      clock (hit rank) < level rank + 1 := by
    intro rank
    by_cases hzero : hit rank = 0
    · rw [hzero]
      have hrank0 : (0 : ℝ) ≤ rank.val := by positivity
      dsimp only [level]
      linarith
    · have hpos : 0 < hit rank := Nat.pos_of_ne_zero hzero
      let previous := hit rank - 1
      have hprevious_lt : previous < hit rank := by
        dsimp only [previous]
        omega
      have hprevious_le : previous ≤ horizon :=
        le_trans (Nat.sub_le _ _) (hhit_spec rank).1
      have hprevious_clock : clock previous < level rank := by
        by_contra hnot
        have hlevel : level rank ≤ clock previous := le_of_not_gt hnot
        exact (Nat.find_min (hexists rank) hprevious_lt)
          ⟨hprevious_le, hlevel⟩
      have hnext := hstep1 previous
      have hprevious_succ : previous + 1 = hit rank := by
        dsimp only [previous]
        omega
      rw [hprevious_succ] at hnext
      linarith
  have hhit_strict : StrictMono hit := by
    intro firstRank secondRank hrank
    by_contra hnot
    have htime : hit secondRank ≤ hit firstRank := Nat.le_of_not_gt hnot
    have hclock := hmono htime
    have hrankGap :
        (firstRank.val : ℝ) + 1 ≤ secondRank.val := by
      exact_mod_cast Nat.succ_le_of_lt hrank
    have hlower := (hhit_spec secondRank).2
    have hupper := hhit_upper firstRank
    dsimp only [level] at hlower hupper
    linarith
  let observed : Fin (Fintype.card Cell + 1) → Cell := fun rank =>
    label (hit rank)
  have hcard :
      Fintype.card Cell <
        Fintype.card (Fin (Fintype.card Cell + 1)) := by
    simp
  obtain ⟨firstRank, secondRank, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt observed hcard
  rcases lt_or_gt_of_ne hne with hrank | hrank
  · refine ⟨hit firstRank, hit secondRank, hhit_strict hrank,
      (hhit_spec secondRank).1, ?_, ?_⟩
    · simpa only [observed] using heq
    · have hrankGap :
          (firstRank.val : ℝ) + 1 ≤ secondRank.val := by
        exact_mod_cast Nat.succ_le_of_lt hrank
      have hlower := (hhit_spec secondRank).2
      have hupper := hhit_upper firstRank
      dsimp only [level] at hlower hupper
      linarith
  · refine ⟨hit secondRank, hit firstRank, hhit_strict hrank,
      (hhit_spec firstRank).1, ?_, ?_⟩
    · simpa only [observed] using heq.symm
    · have hrankGap :
          (secondRank.val : ℝ) + 1 ≤ firstRank.val := by
        exact_mod_cast Nat.succ_le_of_lt hrank
      have hlower := (hhit_spec firstRank).2
      have hupper := hhit_upper secondRank
      dsimp only [level] at hlower hupper
      linarith

/-- Nonnegative charges bounded by one instantiate the unit-step prefix clock. -/
theorem exists_same_label_with_large_charge_gap
    {Cell : Type*} [Fintype Cell]
    (label : ℕ → Cell) (charge : ℕ → ℝ) (horizon : ℕ)
    (hcharge0 : ∀ time, 0 ≤ charge time)
    (hcharge1 : ∀ time, charge time ≤ 1)
    (hlarge :
      2 * (Fintype.card Cell : ℝ) ≤
        ∑ time ∈ Finset.range horizon, charge time) :
    ∃ first second : ℕ,
      first < second ∧ second ≤ horizon ∧
      label first = label second ∧
      1 ≤
        (∑ time ∈ Finset.range second, charge time) -
          ∑ time ∈ Finset.range first, charge time := by
  let clock : ℕ → ℝ := fun cutoff =>
    ∑ time ∈ Finset.range cutoff, charge time
  apply exists_same_label_with_large_clock_gap label clock horizon
  · intro time
    rw [show time + 1 = Nat.succ time by omega,
      Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hcharge0 time)
  · intro time
    rw [show time + 1 = Nat.succ time by omega,
      Finset.sum_range_succ]
    linarith [hcharge1 time]
  · simpa only [clock, Finset.sum_range_zero, zero_add] using hlarge

/-- A finite labelling whose fibres have small diameter turns the charged
pigeonhole theorem into a metric return. -/
theorem exists_close_pair_with_large_charge_gap_of_finite_labels
    {X Cell : Type*} [PseudoMetricSpace X] [Fintype Cell]
    (state : ℕ → X) (label : ℕ → Cell)
    (radius : ℝ)
    (hsame : ∀ first second,
      label first = label second →
        dist (state first) (state second) < radius)
    (charge : ℕ → ℝ) (horizon : ℕ)
    (hcharge0 : ∀ time, 0 ≤ charge time)
    (hcharge1 : ∀ time, charge time ≤ 1)
    (hlarge :
      2 * (Fintype.card Cell : ℝ) ≤
        ∑ time ∈ Finset.range horizon, charge time) :
    ∃ first second : ℕ,
      first < second ∧ second ≤ horizon ∧
      dist (state first) (state second) < radius ∧
      1 ≤
        (∑ time ∈ Finset.range second, charge time) -
          ∑ time ∈ Finset.range first, charge time := by
  obtain ⟨first, second, hlt, hsecond, hlabel, hgap⟩ :=
    exists_same_label_with_large_charge_gap
      label charge horizon hcharge0 hcharge1 hlarge
  exact ⟨first, second, hlt, hsecond, hsame first second hlabel, hgap⟩

end Math
