import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Integer numerator certificates for payoff-constrained symmetric bimatrix
equilibria. The verifier uses finite sums and exact integer comparisons. -/

namespace GameTheory.Finite

open scoped BigOperators

/-- Two distributions with common denominators and their best-response payoff
numerators. All data are natural numbers; signed table entries remain integers. -/
structure NumeratorCertificate (q : ℕ) where
  /-- Row probability numerators. -/
  rowWeights : Fin q → ℕ
  /-- Column probability numerators. -/
  colWeights : Fin q → ℕ
  /-- Common denominator of the row distribution. -/
  rowDenominator : ℕ
  /-- Common denominator of the column distribution. -/
  colDenominator : ℕ
  /-- Row best-response payoff numerator, over the column denominator. -/
  rowUtilityNumerator : ℕ
  /-- Column best-response payoff numerator, over the row denominator. -/
  colUtilityNumerator : ℕ

namespace NumeratorCertificate

/-- Integer payoff numerator for a row pure action against the column weights. -/
def rowScore {q : ℕ} (A : Fin q → Fin q → ℤ) (c : NumeratorCertificate q)
    (i : Fin q) : ℤ := ∑ j, A i j * (c.colWeights j : ℤ)

/-- Integer payoff numerator for a column pure action against the row weights. -/
def colScore {q : ℕ} (A : Fin q → Fin q → ℤ) (c : NumeratorCertificate q)
    (j : Fin q) : ℤ := ∑ i, A j i * (c.rowWeights i : ℤ)

/-- Exact certificate constraints: simplex equations, payoff-one thresholds,
pure-deviation inequalities, and equality for every positively weighted action. -/
def Valid {q : ℕ} (A : Fin q → Fin q → ℤ) (c : NumeratorCertificate q) : Prop :=
  0 < c.rowDenominator ∧ 0 < c.colDenominator ∧
    (∑ i, c.rowWeights i) = c.rowDenominator ∧
    (∑ j, c.colWeights j) = c.colDenominator ∧
    c.colDenominator ≤ c.rowUtilityNumerator ∧
    c.rowDenominator ≤ c.colUtilityNumerator ∧
    (∀ i, rowScore A c i ≤ (c.rowUtilityNumerator : ℤ) ∧
      (0 < c.rowWeights i → rowScore A c i = (c.rowUtilityNumerator : ℤ))) ∧
    (∀ j, colScore A c j ≤ (c.colUtilityNumerator : ℤ) ∧
      (0 < c.colWeights j → colScore A c j = (c.colUtilityNumerator : ℤ)))

instance {q : ℕ} (A : Fin q → Fin q → ℤ) (c : NumeratorCertificate q) :
    Decidable (Valid A c) := by unfold Valid; infer_instance

end NumeratorCertificate

/-- Verify a supplied numerator certificate using exact arithmetic. -/
def verifyNashNumerators {q : ℕ} (A : Fin q → Fin q → ℤ)
    (c : NumeratorCertificate q) : Bool := decide (c.Valid A)

@[simp] theorem verifyNashNumerators_eq_true_iff {q : ℕ}
    (A : Fin q → Fin q → ℤ) (c : NumeratorCertificate q) :
    verifyNashNumerators A c = true ↔ c.Valid A := by
  simp [verifyNashNumerators]

end GameTheory.Finite
