/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Reset error budgets and eventual activation

This file contains the measure-theoretic composition layer used after an
anytime concentration inequality has been proved for each monitoring epoch.
The epoch starts may be adaptive: all such dependence is encapsulated in the
per-epoch failure events and their probability bounds.

The first theorem converts summable per-epoch error budgets into a familywise
error bound.  The second records the corresponding Borel--Cantelli conclusion.
The final results show that an eventually linear signal crosses every
sublinear boundary.
-/

namespace Math.Probability

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A summable family of per-epoch failure bounds controls the probability of
at least one failure.  No independence between epochs is required. -/
theorem measure_iUnion_failure_le
    (failure : ℕ → Set Ω) (budget : ℕ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hfailure : ∀ k, μ (failure k) ≤ budget k)
    (hbudget : ∑' k, budget k ≤ δ) :
    μ (⋃ k, failure k) ≤ δ := by
  calc
    μ (⋃ k, failure k) ≤ ∑' k, μ (failure k) := measure_iUnion_le _
    _ ≤ ∑' k, budget k := ENNReal.tsum_le_tsum hfailure
    _ ≤ δ := hbudget

/-- Two-level form used for stitched monitoring: `j` indexes time blocks
inside reset epoch `k`.  Summing the block budgets controls every crossing
in every epoch, even when the corresponding events are dependent. -/
theorem measure_iUnion_iUnion_failure_le
    (failure : ℕ → ℕ → Set Ω) (budget : ℕ → ℕ → ℝ≥0∞) (δ : ℝ≥0∞)
    (hfailure : ∀ k j, μ (failure k j) ≤ budget k j)
    (hbudget : ∑' k, ∑' j, budget k j ≤ δ) :
    μ (⋃ k, ⋃ j, failure k j) ≤ δ := by
  apply measure_iUnion_failure_le
    (fun k => ⋃ j, failure k j) (fun k => ∑' j, budget k j) δ
  · intro k
    calc
      μ (⋃ j, failure k j) ≤ ∑' j, μ (failure k j) :=
        measure_iUnion_le _
      _ ≤ ∑' j, budget k j :=
        ENNReal.tsum_le_tsum (hfailure k)
  · exact hbudget

/-- If the total per-epoch error budget is finite, only finitely many epochs
fail almost surely.  This is the first Borel--Cantelli lemma and needs no
independence. -/
theorem ae_eventually_not_mem_failure
    (failure : ℕ → Set Ω) (hsum : ∑' k, μ (failure k) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ failure k :=
  ae_eventually_notMem hsum

/-- A convenient budgeted form of the first Borel--Cantelli lemma. -/
theorem ae_eventually_not_mem_failure_of_budget
    (failure : ℕ → Set Ω) (budget : ℕ → ℝ≥0∞)
    (hfailure : ∀ k, μ (failure k) ≤ budget k)
    (hbudget : ∑' k, budget k ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ failure k := by
  apply ae_eventually_notMem
  apply ne_of_lt
  calc
    ∑' k, μ (failure k) ≤ ∑' k, budget k :=
      ENNReal.tsum_le_tsum hfailure
    _ < ∞ := lt_top_iff_ne_top.mpr hbudget

/-- An eventually linear signal eventually dominates a boundary whose ratio
to time tends to zero. -/
theorem eventually_boundary_lt_of_sublinear
    (signal boundary : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hsignal : ∀ᶠ n in atTop, c * n ≤ signal n)
    (hboundary :
      Tendsto (fun n : ℕ => boundary n / n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, boundary n < signal n := by
  have hratio : ∀ᶠ n : ℕ in atTop, boundary n / n < c :=
    (tendsto_order.1 hboundary).2 c hc
  have hn : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
    eventually_atTop.2 ⟨1, fun n hn => by exact_mod_cast hn⟩
  filter_upwards [hsignal, hratio, hn] with n hsignal_n hratio_n hn
  have hboundary_n : boundary n < c * n := by
    rw [div_lt_iff₀ hn] at hratio_n
    simpa [mul_comm] using hratio_n
  exact hboundary_n.trans_le hsignal_n

/-- In particular, an eventually linear signal crosses a sublinear boundary
at some finite time. -/
theorem exists_boundary_crossing_of_sublinear
    (signal boundary : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hsignal : ∀ᶠ n in atTop, c * n ≤ signal n)
    (hboundary :
      Tendsto (fun n : ℕ => boundary n / n) atTop (𝓝 0)) :
    ∃ n, boundary n < signal n := by
  rcases (eventually_boundary_lt_of_sublinear signal boundary hc hsignal hboundary).exists
    with ⟨n, hn⟩
  exact ⟨n, hn⟩

end Math.Probability
