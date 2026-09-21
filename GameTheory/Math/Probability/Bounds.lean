/-
# Elementary finite-law probability bounds

This small facade collects proof-facing inequalities derived solely from the
public `FinDist` algebra.  It does not expose or inspect the underlying PMF
representation.  The first consumers are high-probability approximate-Nash
certification and Bayes-plausible posterior concentration (EXP-094).
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u

/-- A pointwise discrepancy confined to an event costs at most its size times
the event's probability. The discrepancy may have either sign. -/
theorem expect_le_add_event_gap {α : Type u}
    (law : FinDist α) (event : Set α)
    (sourceValue targetValue : α → ℝ) (gap : ℝ)
    (houtside : ∀ state ∈ law.support, state ∉ event →
      targetValue state ≤ sourceValue state)
    (hinside : ∀ state ∈ law.support, state ∈ event →
      targetValue state ≤ sourceValue state + gap) :
    law.expect targetValue ≤ law.expect sourceValue + gap * law.probOf event := by
  classical
  have hpointwise : law.expect targetValue ≤
      law.expect (fun state => sourceValue state + gap * if state ∈ event then 1 else 0) := by
    apply expect_mono
    intro state hstate
    by_cases hevent : state ∈ event
    · simpa [hevent] using hinside state hstate hevent
    · simpa [hevent] using houtside state hstate hevent
  simpa only [expect_add, expect_smul, expect_indicator_eq_probOf] using hpointwise

/-- Comparison on every supported information fiber implies comparison of
expectations. The fiber expectations are unnormalized. -/
theorem expect_le_of_fiber_expect_le {α β : Type*}
    (law : FinDist α) (information : α → β) (sourceValue targetValue : α → ℝ)
    (hfiber : ∀ observed ∈ (law.map information).support,
      law.expect ((information ⁻¹' {observed}).indicator targetValue) ≤
        law.expect ((information ⁻¹' {observed}).indicator sourceValue)) :
    law.expect targetValue ≤ law.expect sourceValue := by
  rw [expect_eq_sum_fibers law information targetValue,
    expect_eq_sum_fibers law information sourceValue]
  exact Finset.sum_le_sum fun observed hmem => hfiber observed (mem_supportFinset.mp hmem)

/-- A finite-support event bound. If a nonnegative observable is at least a
positive threshold throughout an event, that event's probability is at most
the observable's expectation divided by the threshold. -/
theorem probOf_le_expect_div {α : Type u} (law : FinDist α) (event : Set α)
    (observable : α → ℝ) {threshold : ℝ} (hthreshold : 0 < threshold)
    (hnonnegative : ∀ value ∈ law.support, 0 ≤ observable value)
    (hlower : ∀ value ∈ law.support, value ∈ event → threshold ≤ observable value) :
    law.probOf event ≤ law.expect observable / threshold := by
  classical
  have hpointwise :
      ∀ value ∈ law.support,
        threshold * (if value ∈ event then 1 else 0) ≤ observable value := by
    intro value hsupport
    by_cases hevent : value ∈ event
    · simpa [hevent] using hlower value hsupport hevent
    · simpa [hevent] using hnonnegative value hsupport
  have hexpect := FinDist.expect_mono hpointwise
  rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf] at hexpect
  rw [mul_comm] at hexpect
  exact (le_div_iff₀ hthreshold).2 hexpect

/-- Markov's inequality for a nonnegative observable under a finite-support
law. Nonnegativity is required only on the law's support. -/
theorem markov_inequality {α : Type u} (law : FinDist α) (observable : α → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hnonnegative : ∀ value ∈ law.support, 0 ≤ observable value) :
    law.probOf {value | threshold ≤ observable value} ≤
      law.expect observable / threshold :=
  law.probOf_le_expect_div _ observable hthreshold hnonnegative
    (fun _ _ hlower => hlower)

end GameTheory.Math.Probability.FinDist
