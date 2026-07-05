/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.EuclideanPreference
import Math.Probability
import Math.WeightedMedian

/-!
# The Median Voter Theorem

Black's median voter theorem (1948). When voters have **single-peaked** preferences
over a one-dimensional set of alternatives — each voter has an ideal point and
prefers alternatives closer to it — a **median** of the ideal points is a *Condorcet
winner*: it is not beaten by any alternative in a pairwise majority vote. This is the
positive counterpart to Condorcet's paradox: restricting the preference domain to
single-peaked profiles restores a majority winner.

We use the Euclidean form of single-peakedness (preference measured by distance to
the ideal point) and the standard median condition: at least half the voters have
ideal point at most `m`, and at least half have ideal point at least `m`.

## Main results

* `median_is_condorcet_winner` — a median ideal point beats every alternative
  (weakly) in pairwise majority
* `medianIdeal_is_condorcet_winner` — the canonical median of the ideal points
  is a Condorcet winner
* `medianIdeal_strategyproof` / `medianIdeal_no_manipulation` — the canonical
  median rule is strategyproof (Moulin 1980)
-/

namespace GameTheory

open Finset

variable {ι : Type*} [Fintype ι]

open Classical in
/-- **Median Voter Theorem** (Black 1948). Under Euclidean single-peaked preferences,
a median `m` of the voters' ideal points — at least half the voters have ideal point
`≤ m` and at least half have ideal point `≥ m` — is a Condorcet winner: against any
alternative `x`, at least as many voters prefer `m` to `x` as prefer `x` to `m`. -/
theorem median_is_condorcet_winner (peak : ι → ℝ) (m x : ℝ)
    (hlo : Fintype.card ι ≤ 2 * (univ.filter (fun i => peak i ≤ m)).card)
    (hhi : Fintype.card ι ≤ 2 * (univ.filter (fun i => m ≤ peak i)).card) :
    (univ.filter (fun i => Prefers peak i x m)).card
      ≤ (univ.filter (fun i => Prefers peak i m x)).card := by
  rcases lt_trichotomy x m with hx | hx | hx
  · -- `x < m`: every voter with ideal point `≥ m` (a majority) prefers `m` to `x`
    have hsub1 : univ.filter (fun i => m ≤ peak i)
        ⊆ univ.filter (fun i => Prefers peak i m x) := by
      intro i hi
      rw [mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      simp only [Prefers]
      rw [abs_of_nonpos (by linarith [hi.2]), abs_of_nonpos (by linarith [hi.2])]
      linarith
    have hsub2 : univ.filter (fun i => Prefers peak i x m)
        ⊆ univ.filter (fun i => ¬ m ≤ peak i) := by
      intro i hi
      rw [mem_filter] at hi ⊢
      refine ⟨hi.1, fun hge => ?_⟩
      have hp := hi.2
      simp only [Prefers] at hp
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hp
      linarith
    have c1 := Finset.card_le_card hsub1
    have c2 := Finset.card_le_card hsub2
    have c3 : (univ.filter (fun i => m ≤ peak i)).card
        + (univ.filter (fun i => ¬ m ≤ peak i)).card = Fintype.card ι := by
      rw [Finset.card_filter_add_card_filter_not, card_univ]
    omega
  · -- `x = m`: no voter strictly prefers either
    subst hx
    simp [Prefers]
  · -- `m < x`: every voter with ideal point `≤ m` (a majority) prefers `m` to `x`
    have hsub1 : univ.filter (fun i => peak i ≤ m)
        ⊆ univ.filter (fun i => Prefers peak i m x) := by
      intro i hi
      rw [mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      simp only [Prefers]
      rw [abs_of_nonneg (by linarith [hi.2]), abs_of_nonneg (by linarith [hi.2])]
      linarith
    have hsub2 : univ.filter (fun i => Prefers peak i x m)
        ⊆ univ.filter (fun i => ¬ peak i ≤ m) := by
      intro i hi
      rw [mem_filter] at hi ⊢
      refine ⟨hi.1, fun hle => ?_⟩
      have hp := hi.2
      simp only [Prefers] at hp
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hp
      linarith
    have c1 := Finset.card_le_card hsub1
    have c2 := Finset.card_le_card hsub2
    have c3 : (univ.filter (fun i => peak i ≤ m)).card
        + (univ.filter (fun i => ¬ peak i ≤ m)).card = Fintype.card ι := by
      rw [Finset.card_filter_add_card_filter_not, card_univ]
    omega

section CanonicalMedian

variable [Nonempty ι] (peak : ι → ℝ)

/-- The canonical median of the ideal points. -/
noncomputable def medianIdeal : ℝ := Math.weightedMedian peak (fun _ => 1)

open Classical in
/-- The canonical median of the ideal points is a Condorcet winner. -/
theorem medianIdeal_is_condorcet_winner (x : ℝ) :
    (univ.filter (fun i => Prefers peak i x (medianIdeal peak))).card
      ≤ (univ.filter (fun i => Prefers peak i (medianIdeal peak) x)).card := by
  apply median_is_condorcet_winner
  · have h := Math.totalWeight_le_two_mul_cumWeight_weightedMedian peak
      (fun _ => 1)
    rw [Math.totalWeight_one, Math.cumWeight_one] at h
    exact h
  · have h := (Math.isWeightedMedian_weightedMedian peak (fun _ => 1)).1
    rw [Math.totalWeight_one, Math.leftWeight_one] at h
    have hsplit := Finset.card_filter_add_card_filter_not (s := univ)
      (p := fun i => peak i < medianIdeal peak)
    simp only [not_lt, card_univ] at hsplit
    have : (univ.filter fun i => peak i < medianIdeal peak).card
        = (univ.filter fun a => peak a < Math.weightedMedian peak fun _ => 1).card :=
      rfl
    omega

/-- **Median strategyproofness** (Moulin 1980).  Reporting the true ideal point
is optimal against the canonical median rule: no misreport moves the median
strictly closer to a voter's ideal point. -/
theorem medianIdeal_strategyproof [DecidableEq ι] (i : ι) (x : ℝ) :
    |medianIdeal peak - peak i|
      ≤ |medianIdeal (Function.update peak i x) - peak i| := by
  refine Math.abs_weightedMedian_sub_le_update ?_ i x
  rw [Math.totalWeight_one]
  exact Fintype.card_pos

/-- Median strategyproofness in preference form: no voter strictly prefers the
median of a misreported profile. -/
theorem medianIdeal_no_manipulation [DecidableEq ι] (i : ι) (x : ℝ) :
    ¬ Prefers peak i (medianIdeal (Function.update peak i x)) (medianIdeal peak) :=
  not_lt.mpr (medianIdeal_strategyproof peak i x)

end CanonicalMedian

end GameTheory
