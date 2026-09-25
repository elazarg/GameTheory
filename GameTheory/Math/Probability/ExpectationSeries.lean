/-
# Expectations of dominated real series under a PMF

A summable numerical majorant on the support controls both the pointwise
series and its expected value. The carrier need not be finite or countable.
-/

import GameTheory.Math.Probability.Expectation
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

namespace GameTheory.Math.Probability

private theorem summable_weight_majorant {α : Type*} (μ : PMF α)
    (majorant : ℕ → ℝ) (hsum : Summable majorant)
    (hnonneg : ∀ n, 0 ≤ majorant n) :
    Summable fun pair : α × ℕ =>
      (μ pair.1).toReal * majorant pair.2 := by
  have hmajorNonneg :
      0 ≤ fun pair : α × ℕ =>
        (μ pair.1).toReal * majorant pair.2 := by
    intro pair
    exact mul_nonneg ENNReal.toReal_nonneg (hnonneg pair.2)
  apply (summable_prod_of_nonneg hmajorNonneg).2
  constructor
  · intro a
    exact hsum.mul_left (μ a).toReal
  · have houter := (pmf_weight_summable μ).mul_right (∑' n, majorant n)
    simpa only [tsum_mul_left] using houter

private theorem summable_weight_term {α : Type*} (μ : PMF α)
    (term : ℕ → α → ℝ) (majorant : ℕ → ℝ)
    (hsum : Summable majorant)
    (hbound : ∀ n, ∀ a ∈ μ.support, |term n a| ≤ majorant n) :
    Summable fun pair : α × ℕ =>
      (μ pair.1).toReal * term pair.2 pair.1 := by
  have hnonneg (n : ℕ) : 0 ≤ majorant n := by
    obtain ⟨a, ha⟩ := PMF.support_nonempty μ
    exact le_trans (abs_nonneg _) (hbound n a ha)
  apply Summable.of_norm_bounded
    (summable_weight_majorant μ majorant hsum hnonneg)
  intro ⟨a, n⟩
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (hbound n a ha)
      ENNReal.toReal_nonneg
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [hzero]

private theorem summable_term_on_support {α : Type*} (μ : PMF α)
    (term : ℕ → α → ℝ) (majorant : ℕ → ℝ)
    (hsum : Summable majorant)
    (hbound : ∀ n, ∀ a ∈ μ.support, |term n a| ≤ majorant n)
    (a : α) (ha : a ∈ μ.support) :
    Summable fun n => term n a := by
  apply Summable.of_norm_bounded hsum
  intro n
  simpa only [Real.norm_eq_abs] using hbound n a ha

/-- The pointwise series is integrable under the PMF when its terms have a
common summable majorant on the support. -/
theorem payoffIntegrable_tsum_of_majorant {α : Type*} (μ : PMF α)
    (term : ℕ → α → ℝ) (majorant : ℕ → ℝ)
    (hsum : Summable majorant)
    (hbound : ∀ n, ∀ a ∈ μ.support, |term n a| ≤ majorant n) :
    PayoffIntegrable μ (fun a => ∑' n, term n a) := by
  apply payoffIntegrable_of_bounded_on_support μ _
  intro a ha
  have hs := summable_term_on_support μ term majorant hsum hbound a ha
  have hsabs : Summable fun n => |term n a| := by
    simpa only [Real.norm_eq_abs] using hs.norm
  have hle := norm_tsum_le_tsum_norm hs.norm
  have hsumLe := hsabs.tsum_le_tsum
    (fun n => hbound n a ha) hsum
  exact le_trans (by simpa only [Real.norm_eq_abs] using hle) hsumLe

/-- The sequence of guarded term expectations is summable. -/
theorem summable_expect_of_majorant {α : Type*} (μ : PMF α)
    (term : ℕ → α → ℝ) (majorant : ℕ → ℝ)
    (hsum : Summable majorant)
    (hbound : ∀ n, ∀ a ∈ μ.support, |term n a| ≤ majorant n) :
    Summable fun n =>
      expect μ (term n)
        (payoffIntegrable_of_bounded_on_support μ (term n)
          (hbound n)) := by
  have hprod := summable_weight_term μ term majorant
    hsum hbound
  simpa [expect] using hprod.prod_symm.prod

/-- A dominated real series commutes with PMF expectation on an arbitrary
carrier. All operation guards are derived from the same support-local
majorant. -/
theorem expect_tsum_of_majorant {α : Type*} (μ : PMF α)
    (term : ℕ → α → ℝ) (majorant : ℕ → ℝ)
    (hsum : Summable majorant)
    (hbound : ∀ n, ∀ a ∈ μ.support, |term n a| ≤ majorant n) :
    (∑' n, expect μ (term n)
      (payoffIntegrable_of_bounded_on_support μ (term n)
        (hbound n))) =
      expect μ (fun a => ∑' n, term n a)
        (payoffIntegrable_tsum_of_majorant μ term majorant
          hsum hbound) := by
  have hprod := summable_weight_term μ term majorant
    hsum hbound
  calc
    (∑' n, expect μ (term n)
        (payoffIntegrable_of_bounded_on_support μ (term n)
          (hbound n))) =
        ∑' n, ∑' a, (μ a).toReal * term n a := rfl
    _ = ∑' a, ∑' n, (μ a).toReal * term n a :=
      hprod.tsum_comm
    _ = ∑' a, (μ a).toReal * ∑' n, term n a := by
      apply tsum_congr
      intro a
      by_cases ha : a ∈ μ.support
      · exact (summable_term_on_support μ term majorant
          hsum hbound a ha).tsum_mul_left (μ a).toReal
      · have hzero : μ a = 0 := not_ne_iff.mp ha
        simp [hzero]
    _ = expect μ (fun a => ∑' n, term n a)
        (payoffIntegrable_tsum_of_majorant μ term majorant
          hsum hbound) := rfl

end GameTheory.Math.Probability
