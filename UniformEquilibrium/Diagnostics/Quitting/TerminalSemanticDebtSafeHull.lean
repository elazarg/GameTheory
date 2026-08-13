/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.Caratheodory
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Stationary.Payoff

/-!
# Debt-safe hulls of terminal semantic pairs

This module records a closure operation on prescribed-payoff/best-response
semantic pairs.  It convexifies the prescribed coordinates and permits only
pointwise increases of the best-response coordinates.  The operation is
extensive, monotone, idempotent, preserves lower bounds on total debt, and is
compatible with every literal quitting-root prefix.

Carathéodory compression is applied only in the prescribed-payoff space.  It
therefore gives witnesses using at most `Fintype.card ι + 1` source pairs
without losing the pointwise best-response-coordinate bounds.

No semialgebraicity, finite termination, or completeness assertion is made.
-/

noncomputable section

namespace GameTheory

open Finset Set Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The debt-safe hull of a set of terminal semantic pairs.  The finite
support is initially unrestricted; `exists_small_witness_of_mem` compresses
it to at most one more than the number of players. -/
def quittingTerminalSemanticDebtSafeHull
    (A : Set (QuittingTerminalSemanticPair ι)) :
    Set (QuittingTerminalSemanticPair ι) :=
  fun pair ↦ ∃ (m : ℕ)
      (point : Fin m → QuittingTerminalSemanticPair ι)
      (weight : Fin m → ℝ),
    (∀ k, 0 ≤ weight k) ∧
    (∑ k, weight k) = 1 ∧
    (∀ k, point k ∈ A) ∧
    (∀ who, pair.1 who ≤ ∑ k, weight k * (point k).1 who) ∧
    (∀ who k, (point k).2 who ≤ pair.2 who)

omit [Fintype ι] [DecidableEq ι] in
theorem quittingTerminalSemanticDebtSafeHull_mono
    {A B : Set (QuittingTerminalSemanticPair ι)} (hAB : A ⊆ B) :
    quittingTerminalSemanticDebtSafeHull A ⊆
      quittingTerminalSemanticDebtSafeHull B := by
  rintro pair ⟨m, point, weight, hweight, hsum, hpoint, hu, hb⟩
  exact ⟨m, point, weight, hweight, hsum,
    fun k ↦ hAB (hpoint k), hu, hb⟩

omit [Fintype ι] [DecidableEq ι] in
theorem subset_quittingTerminalSemanticDebtSafeHull
    (A : Set (QuittingTerminalSemanticPair ι)) :
    A ⊆ quittingTerminalSemanticDebtSafeHull A := by
  intro pair hpair
  refine ⟨1, fun _ ↦ pair, fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    positivity
  · simp
  · intro k
    exact hpair
  · intro who
    simp
  · intro who k
    exact le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem quittingTerminalSemanticDebtSafeHull_hull_subset
    (A : Set (QuittingTerminalSemanticPair ι)) :
    quittingTerminalSemanticDebtSafeHull
        (quittingTerminalSemanticDebtSafeHull A) ⊆
      quittingTerminalSemanticDebtSafeHull A := by
  classical
  rintro pair ⟨m, outerPoint, outerWeight, hOuterWeight, hOuterSum,
    hOuterPoint, hOuterU, hOuterB⟩
  choose innerSize innerPoint innerWeight hInnerWeight hInnerSum
    hInnerPoint hInnerU hInnerB using hOuterPoint
  let FlatIndex := Σ k : Fin m, Fin (innerSize k)
  let equivalence := Fintype.equivFin FlatIndex
  let flatPoint : Fin (Fintype.card FlatIndex) →
      QuittingTerminalSemanticPair ι := fun index ↦
    innerPoint (equivalence.symm index).1 (equivalence.symm index).2
  let flatWeight : Fin (Fintype.card FlatIndex) → ℝ := fun index ↦
    outerWeight (equivalence.symm index).1 *
      innerWeight (equivalence.symm index).1 (equivalence.symm index).2
  refine ⟨Fintype.card FlatIndex, flatPoint, flatWeight, ?_, ?_, ?_, ?_, ?_⟩
  · intro index
    exact mul_nonneg (hOuterWeight _) (hInnerWeight _ _)
  · change ∑ index, (fun p : FlatIndex ↦
      outerWeight p.1 * innerWeight p.1 p.2) (equivalence.symm index) = 1
    calc
      ∑ index, (fun p : FlatIndex ↦
          outerWeight p.1 * innerWeight p.1 p.2) (equivalence.symm index) =
          ∑ p : FlatIndex, outerWeight p.1 * innerWeight p.1 p.2 := by
        simpa only using equivalence.symm.sum_comp
          (fun p : FlatIndex ↦ outerWeight p.1 * innerWeight p.1 p.2)
      _ = ∑ k, ∑ j, outerWeight k * innerWeight k j := by
        rw [Fintype.sum_sigma]
      _ = ∑ k, outerWeight k * (∑ j, innerWeight k j) := by
        apply sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      _ = ∑ k, outerWeight k := by
        apply sum_congr rfl
        intro k _
        rw [hInnerSum k, mul_one]
      _ = 1 := hOuterSum
  · intro index
    exact hInnerPoint _ _
  · intro who
    change pair.1 who ≤ ∑ index, flatWeight index * (flatPoint index).1 who
    calc
      pair.1 who ≤ ∑ k, outerWeight k * (outerPoint k).1 who := hOuterU who
      _ ≤ ∑ k, outerWeight k *
          (∑ j, innerWeight k j * (innerPoint k j).1 who) := by
        apply sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hInnerU k who) (hOuterWeight k)
      _ = ∑ p : FlatIndex,
          (outerWeight p.1 * innerWeight p.1 p.2) *
            (innerPoint p.1 p.2).1 who := by
        rw [Fintype.sum_sigma]
        apply sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ index, flatWeight index * (flatPoint index).1 who := by
        change (∑ p : FlatIndex,
            (outerWeight p.1 * innerWeight p.1 p.2) *
              (innerPoint p.1 p.2).1 who) =
          ∑ index, (fun p : FlatIndex ↦
            (outerWeight p.1 * innerWeight p.1 p.2) *
              (innerPoint p.1 p.2).1 who) (equivalence.symm index)
        simpa only using (equivalence.symm.sum_comp
          (fun p : FlatIndex ↦
            (outerWeight p.1 * innerWeight p.1 p.2) *
              (innerPoint p.1 p.2).1 who)).symm
  · intro who index
    exact (hInnerB _ who _).trans (hOuterB who _)

omit [Fintype ι] [DecidableEq ι] in
theorem quittingTerminalSemanticDebtSafeHull_idempotent
    (A : Set (QuittingTerminalSemanticPair ι)) :
    quittingTerminalSemanticDebtSafeHull
        (quittingTerminalSemanticDebtSafeHull A) =
      quittingTerminalSemanticDebtSafeHull A := by
  apply Set.Subset.antisymm
    (quittingTerminalSemanticDebtSafeHull_hull_subset A)
  exact subset_quittingTerminalSemanticDebtSafeHull
    (quittingTerminalSemanticDebtSafeHull A)

omit [DecidableEq ι] in
/-- Total debt at a hull point dominates the weighted average of the source
debts in any hull witness. -/
theorem quittingTerminalSemanticDebtSum_ge_weighted_of_mem_debtSafeHull
    {A : Set (QuittingTerminalSemanticPair ι)}
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticDebtSafeHull A) :
    ∃ (m : ℕ) (point : Fin m → QuittingTerminalSemanticPair ι)
      (weight : Fin m → ℝ),
      (∀ k, 0 ≤ weight k) ∧
      (∑ k, weight k) = 1 ∧
      (∀ k, point k ∈ A) ∧
      quittingTerminalSemanticDebtSum pair ≥
        ∑ k, weight k * quittingTerminalSemanticDebtSum (point k) := by
  rcases hpair with ⟨m, point, weight, hweight, hsum, hpoint, hu, hb⟩
  refine ⟨m, point, weight, hweight, hsum, hpoint, ?_⟩
  have hb' : ∀ who, ∑ k, weight k * (point k).2 who ≤ pair.2 who := by
    intro who
    calc
      ∑ k, weight k * (point k).2 who ≤
          ∑ k, weight k * pair.2 who := by
        apply sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hb who k) (hweight k)
      _ = pair.2 who := by rw [← sum_mul, hsum, one_mul]
  have hcoordinate : ∀ who,
      ∑ k, weight k * ((point k).2 who - (point k).1 who) ≤
        pair.2 who - pair.1 who := by
    intro who
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    linarith [hb' who, hu who]
  calc
    ∑ k, weight k * quittingTerminalSemanticDebtSum (point k) =
        ∑ who, ∑ k,
          weight k * ((point k).2 who - (point k).1 who) := by
      simp only [quittingTerminalSemanticDebtSum,
        quittingTerminalSemanticDebt, mul_sum]
      rw [sum_comm]
    _ ≤ ∑ who, (pair.2 who - pair.1 who) :=
      sum_le_sum fun who _ ↦ hcoordinate who
    _ = quittingTerminalSemanticDebtSum pair := by
      simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]

omit [DecidableEq ι] in
theorem quittingTerminalSemanticDebtSafeHull_preserves_floor
    {A : Set (QuittingTerminalSemanticPair ι)} {δ : ℝ}
    (hfloor : ∀ pair ∈ A, δ ≤ quittingTerminalSemanticDebtSum pair) :
    ∀ pair ∈ quittingTerminalSemanticDebtSafeHull A,
      δ ≤ quittingTerminalSemanticDebtSum pair := by
  intro pair hpair
  obtain ⟨m, point, weight, hweight, hsum, hpoint, hdebt⟩ :=
    quittingTerminalSemanticDebtSum_ge_weighted_of_mem_debtSafeHull hpair
  calc
    δ = ∑ k : Fin m, weight k * δ := by
      rw [← sum_mul, hsum, one_mul]
    _ ≤ ∑ k, weight k * quittingTerminalSemanticDebtSum (point k) := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hfloor _ (hpoint k)) (hweight k)
    _ ≤ quittingTerminalSemanticDebtSum pair := hdebt

omit [DecidableEq ι] in
/-- Carathéodory compression of an arbitrary hull witness in prescribed-payoff
space, retaining source states so their best-response coordinates remain
bounded by the target pair. -/
theorem quittingTerminalSemanticDebtSafeHull_exists_small_witness
    {A : Set (QuittingTerminalSemanticPair ι)}
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticDebtSafeHull A) :
    ∃ (m : ℕ) (_ : m ≤ Fintype.card ι + 1)
      (point : Fin m → QuittingTerminalSemanticPair ι)
      (weight : Fin m → ℝ),
      (∀ k, 0 ≤ weight k) ∧
      (∑ k, weight k) = 1 ∧
      (∀ k, point k ∈ A) ∧
      (∀ who, pair.1 who ≤ ∑ k, weight k * (point k).1 who) ∧
      (∀ who k, (point k).2 who ≤ pair.2 who) := by
  classical
  rcases hpair with ⟨m, sourcePoint, sourceWeight, hweight, hsum,
    hpoint, hu, hb⟩
  let sourceU : Fin m → Payoff ι := fun k ↦ (sourcePoint k).1
  let eligibleU : Set (Payoff ι) := Set.range sourceU
  let ubar : Payoff ι := ∑ k, sourceWeight k • sourceU k
  have hubar : ubar ∈ convexHull ℝ eligibleU := by
    apply (convex_convexHull ℝ eligibleU).sum_mem
    · intro k _
      exact hweight k
    · simpa using hsum
    · intro k _
      exact subset_convexHull ℝ eligibleU ⟨k, rfl⟩
  obtain ⟨κ, inst, selectedU, selectedWeight, hselected, hindependent,
    hpositive, hselectedSum, hselectedBar⟩ :=
    eq_pos_convex_span_of_mem_convexHull hubar
  letI : Fintype κ := inst
  have hcard : Fintype.card κ ≤ Fintype.card ι + 1 := by
    calc
      Fintype.card κ ≤
          Module.finrank ℝ (vectorSpan ℝ (Set.range selectedU)) + 1 :=
        hindependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Payoff ι) + 1 :=
        Nat.add_le_add_right
          (Submodule.finrank_le (vectorSpan ℝ (Set.range selectedU))) 1
      _ = Fintype.card ι + 1 := by simp [Payoff]
  have hselectedSource : ∀ k : κ, ∃ j : Fin m, sourceU j = selectedU k := by
    intro k
    simpa [eligibleU] using hselected ⟨k, rfl⟩
  choose sourceIndex hsourceIndex using hselectedSource
  let selectedPoint : κ → QuittingTerminalSemanticPair ι := fun k ↦
    sourcePoint (sourceIndex k)
  let equivalence := Fintype.equivFin κ
  let point : Fin (Fintype.card κ) → QuittingTerminalSemanticPair ι := fun k ↦
    selectedPoint (equivalence.symm k)
  let weight : Fin (Fintype.card κ) → ℝ := fun k ↦
    selectedWeight (equivalence.symm k)
  refine ⟨Fintype.card κ, hcard, point, weight, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hpositive _).le
  · change ∑ k, selectedWeight (equivalence.symm k) = 1
    simpa only using
      (equivalence.symm.sum_comp selectedWeight).trans hselectedSum
  · intro k
    exact hpoint _
  · intro who
    calc
      pair.1 who ≤ ∑ k, sourceWeight k * (sourcePoint k).1 who := hu who
      _ = ubar who := by simp [ubar, sourceU]
      _ = ∑ k : κ, selectedWeight k * (selectedPoint k).1 who := by
        have hcoordinate := congrFun hselectedBar who
        simpa [selectedPoint, sourceU, hsourceIndex] using hcoordinate.symm
      _ = ∑ k, weight k * (point k).1 who := by
        change (∑ k : κ,
          selectedWeight k * (selectedPoint k).1 who) =
          ∑ k, (fun k : κ ↦
            selectedWeight k * (selectedPoint k).1 who) (equivalence.symm k)
        simpa only using (equivalence.symm.sum_comp
          (fun k : κ ↦ selectedWeight k * (selectedPoint k).1 who)).symm
  · intro who k
    exact hb who _

private theorem quittingStationaryContinueMass_update_pure_true_eq_zero_local
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass
      (Function.update root who (PMF.pure true)) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (i := who)
  · simp
  · simp

/-- Prescribed payoffs transform affinely under a literal root prefix, with a
single coefficient shared by all players. -/
theorem quittingTerminalSemanticPrefix_fst_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (who : ι) :
    (quittingTerminalSemanticPrefix reward root pair).1 who =
      quittingStationaryContinueMass root * pair.1 who +
        quittingRootAbsorbingContribution reward root who := by
  simp only [quittingTerminalSemanticPrefix]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

/-- Best-response coordinates transform by a coordinatewise monotone
max-affine map under a literal root prefix. -/
theorem quittingTerminalSemanticPrefix_snd_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (who : ι) :
    (quittingTerminalSemanticPrefix reward root pair).2 who =
      max
        (quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure true)) who)
        (quittingRootOpponentContinueMass root who * pair.2 who +
          quittingRootAbsorbingContribution reward
            (Function.update root who (PMF.pure false)) who) := by
  simp only [quittingTerminalSemanticPrefix]
  unfold quittingRootQuitPayoff quittingRootContinuePayoff
    quittingRootOpponentContinueMass
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero_local]
  simp only [Function.update_self]
  ring_nf

/-- Literal quitting-root prefixing commutes with the debt-safe hull in the
post-fixed direction needed for barrier synthesis. -/
theorem quittingTerminalSemanticPrefix_image_debtSafeHull_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (A : Set (QuittingTerminalSemanticPair ι)) :
    quittingTerminalSemanticPrefix reward root ''
        quittingTerminalSemanticDebtSafeHull A ⊆
      quittingTerminalSemanticDebtSafeHull
        (quittingTerminalSemanticPrefix reward root '' A) := by
  rintro _ ⟨pair, hpair, rfl⟩
  rcases hpair with ⟨m, point, weight, hweight, hsum, hpoint, hu, hb⟩
  refine ⟨m, fun k ↦ quittingTerminalSemanticPrefix reward root (point k),
    weight, hweight, hsum, ?_, ?_, ?_⟩
  · intro k
    exact ⟨point k, hpoint k, rfl⟩
  · intro who
    simp_rw [quittingTerminalSemanticPrefix_fst_apply]
    calc
      quittingStationaryContinueMass root * pair.1 who +
          quittingRootAbsorbingContribution reward root who ≤
        quittingStationaryContinueMass root *
            (∑ k, weight k * (point k).1 who) +
          quittingRootAbsorbingContribution reward root who := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hu who)
            (quittingStationaryContinueMass_nonneg root)) le_rfl
      _ = ∑ k, weight k *
          (quittingStationaryContinueMass root * (point k).1 who +
            quittingRootAbsorbingContribution reward root who) := by
        calc
          quittingStationaryContinueMass root *
                (∑ k, weight k * (point k).1 who) +
              quittingRootAbsorbingContribution reward root who =
            (∑ k, quittingStationaryContinueMass root *
              (weight k * (point k).1 who)) +
              ∑ k, weight k *
                quittingRootAbsorbingContribution reward root who := by
              rw [mul_sum]
              congr 1
              calc
                quittingRootAbsorbingContribution reward root who =
                    1 * quittingRootAbsorbingContribution reward root who :=
                  (one_mul _).symm
                _ = (∑ k, weight k) *
                    quittingRootAbsorbingContribution reward root who := by
                  rw [hsum]
                _ = ∑ k, weight k *
                    quittingRootAbsorbingContribution reward root who := by
                  rw [Finset.sum_mul]
          _ = _ := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro k _
            ring
  · intro who k
    simp_rw [quittingTerminalSemanticPrefix_snd_apply]
    apply max_le_max le_rfl
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hb who k)
        (quittingRootOpponentContinueMass_nonneg root who)) le_rfl

/-- A positive-debt barrier contains a named anchor, is closed under every
literal quitting-root prefix, and has a strictly positive total-debt floor. -/
structure IsPositiveQuittingTerminalSemanticDebtBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι) (δ : ℝ)
    (B : Set (QuittingTerminalSemanticPair ι)) : Prop where
  floor_pos : 0 < δ
  anchor_mem : anchor ∈ B
  prefix_mem : ∀ root pair, pair ∈ B →
    quittingTerminalSemanticPrefix reward root pair ∈ B
  debt_floor : ∀ pair, pair ∈ B →
    δ ≤ quittingTerminalSemanticDebtSum pair

/-- Finite-horizon hull stabilization is sufficient for a positive-debt
barrier.  This is only a consumer of a supplied stabilization inclusion; it
does not assert that such an inclusion eventually occurs. -/
theorem positiveQuittingTerminalSemanticDebtBarrier_of_hull_stabilization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : QuittingTerminalSemanticPair ι) (δ : ℝ)
    (current next : Set (QuittingTerminalSemanticPair ι))
    (hδ : 0 < δ) (hanchor : anchor ∈ current)
    (hstep : ∀ root,
      quittingTerminalSemanticPrefix reward root '' current ⊆ next)
    (hstabilizes : next ⊆ quittingTerminalSemanticDebtSafeHull current)
    (hfloor : ∀ pair ∈ current,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    IsPositiveQuittingTerminalSemanticDebtBarrier reward anchor δ
      (quittingTerminalSemanticDebtSafeHull current) := by
  refine ⟨hδ, subset_quittingTerminalSemanticDebtSafeHull current hanchor,
    ?_, quittingTerminalSemanticDebtSafeHull_preserves_floor hfloor⟩
  intro root pair hpair
  have hprefixed : quittingTerminalSemanticPrefix reward root pair ∈
      quittingTerminalSemanticDebtSafeHull
        (quittingTerminalSemanticPrefix reward root '' current) :=
    quittingTerminalSemanticPrefix_image_debtSafeHull_subset
      reward root current ⟨pair, hpair, rfl⟩
  have hnext : quittingTerminalSemanticPrefix reward root pair ∈
      quittingTerminalSemanticDebtSafeHull next :=
    quittingTerminalSemanticDebtSafeHull_mono (hstep root) hprefixed
  have hhull : quittingTerminalSemanticPrefix reward root pair ∈
      quittingTerminalSemanticDebtSafeHull
        (quittingTerminalSemanticDebtSafeHull current) :=
    quittingTerminalSemanticDebtSafeHull_mono hstabilizes hnext
  rw [quittingTerminalSemanticDebtSafeHull_idempotent] at hhull
  exact hhull

end GameTheory
