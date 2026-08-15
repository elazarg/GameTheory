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
