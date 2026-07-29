/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.MarkovOccupation

/-!
# Pathwise shadow-or-separator accounting

This file isolates the deterministic finite-horizon ledger behind a
shadow-or-separator compiler.  The theorem does not construct a stochastic
process.  Instead it records exactly the identities and inequalities that a
later coupling or martingale construction must supply.

The signs of all three noise terms are explicit:

* `potentialNoise` is added to the potential telescope;
* `goodNoise` is added to the legal-shadow mismatch budget;
* `separatorNoise` is added to the realized separator charge.

Consequently, a later probabilistic application can prove that their sum is
a martingale (or has nonpositive expectation) without reopening the pathwise
accounting argument.
-/

namespace Math.Probability

noncomputable section

/-- The exact finite-horizon shadow-or-separator ledger.

`transientCost` is paid through a telescoping nonnegative potential,
`goodMismatch` through the legal-shadow budget, and `badTolerance` through
the realized separator charge.  The conclusion deliberately retains
`L * ∑ badTolerance` on the left: a non-shadowable round must either pay that
amount or expose the corresponding separator evidence.
-/
theorem shadowSeparatorLedgerSum_le
    (T : ℕ) (L : ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hpayoff : ∀ t ∈ Finset.range T,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) + implementationCost t)
    (htransient : ∀ t ∈ Finset.range T,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t ∈ Finset.range T,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t ∈ Finset.range T,
      badTolerance t ≤ separatorCharge t + separatorNoise t) :
    (∑ t ∈ Finset.range T, payoffError t) +
        L * ∑ t ∈ Finset.range T, badTolerance t ≤
      L * (potential 0 - potential T +
        ∑ t ∈ Finset.range T,
          (potentialDrift t + goodBudget t + separatorCharge t +
            potentialNoise t + goodNoise t + separatorNoise t)) +
        ∑ t ∈ Finset.range T, implementationCost t := by
  have hround : ∀ t ∈ Finset.range T,
      payoffError t + L * badTolerance t ≤
        L * ((potential t - potential (t + 1)) +
          (potentialDrift t + goodBudget t + separatorCharge t +
            potentialNoise t + goodNoise t + separatorNoise t)) +
          implementationCost t := by
    intro t ht
    have hcost :
        transientCost t + goodMismatch t + badTolerance t ≤
          (potential t - potential (t + 1)) +
            (potentialDrift t + goodBudget t + separatorCharge t +
              potentialNoise t + goodNoise t + separatorNoise t) := by
      rw [htransient t ht]
      linarith [hgood t ht, hbad t ht]
    have hscaled := mul_le_mul_of_nonneg_left hcost hL
    linarith [hpayoff t ht]
  calc
    (∑ t ∈ Finset.range T, payoffError t) +
        L * ∑ t ∈ Finset.range T, badTolerance t =
        ∑ t ∈ Finset.range T,
          (payoffError t + L * badTolerance t) := by
            rw [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ∑ t ∈ Finset.range T,
        (L * ((potential t - potential (t + 1)) +
          (potentialDrift t + goodBudget t + separatorCharge t +
            potentialNoise t + goodNoise t + separatorNoise t)) +
          implementationCost t) :=
      Finset.sum_le_sum hround
    _ = L * (potential 0 - potential T +
        ∑ t ∈ Finset.range T,
          (potentialDrift t + goodBudget t + separatorCharge t +
            potentialNoise t + goodNoise t + separatorNoise t)) +
        ∑ t ∈ Finset.range T, implementationCost t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_range_sub']

/-- If separator tolerances and the terminal potential are nonnegative, the
ledger bounds payoff error alone by the initial potential, predictable
budgets, realized separator charges, and the three noise sums. -/
theorem shadowSeparatorPayoffErrorSum_le
    (T : ℕ) (L : ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hterminal : 0 ≤ potential T)
    (hbad_nonneg : ∀ t ∈ Finset.range T, 0 ≤ badTolerance t)
    (hpayoff : ∀ t ∈ Finset.range T,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) + implementationCost t)
    (htransient : ∀ t ∈ Finset.range T,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t ∈ Finset.range T,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t ∈ Finset.range T,
      badTolerance t ≤ separatorCharge t + separatorNoise t) :
    (∑ t ∈ Finset.range T, payoffError t) ≤
      L * (potential 0 +
        ∑ t ∈ Finset.range T,
          (potentialDrift t + goodBudget t + separatorCharge t +
            potentialNoise t + goodNoise t + separatorNoise t)) +
        ∑ t ∈ Finset.range T, implementationCost t := by
  have hledger := shadowSeparatorLedgerSum_le T L
    potential payoffError implementationCost
    transientCost potentialDrift potentialNoise
    goodMismatch goodBudget goodNoise
    badTolerance separatorCharge separatorNoise
    hL hpayoff htransient hgood hbad
  have hbadSum : 0 ≤ ∑ t ∈ Finset.range T, badTolerance t :=
    Finset.sum_nonneg hbad_nonneg
  have hdropLeft :
      (∑ t ∈ Finset.range T, payoffError t) ≤
        (∑ t ∈ Finset.range T, payoffError t) +
          L * ∑ t ∈ Finset.range T, badTolerance t := by
    exact le_add_of_nonneg_right (mul_nonneg hL hbadSum)
  calc
    (∑ t ∈ Finset.range T, payoffError t) ≤
        (∑ t ∈ Finset.range T, payoffError t) +
          L * ∑ t ∈ Finset.range T, badTolerance t :=
      hdropLeft
    _ ≤ L * (potential 0 - potential T +
          ∑ t ∈ Finset.range T,
            (potentialDrift t + goodBudget t + separatorCharge t +
              potentialNoise t + goodNoise t + separatorNoise t)) +
          ∑ t ∈ Finset.range T, implementationCost t :=
      hledger
    _ ≤ L * (potential 0 +
          ∑ t ∈ Finset.range T,
            (potentialDrift t + goodBudget t + separatorCharge t +
              potentialNoise t + goodNoise t + separatorNoise t)) +
          ∑ t ∈ Finset.range T, implementationCost t := by
      gcongr
      linarith

end

end Math.Probability
