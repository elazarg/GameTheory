module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! Exact integer certificates for rectangular bimatrix Nash equilibria.
Natural probability numerators have independent positive denominators, while
payoff numerators are signed integers. Verification uses only finite sums and
integer comparisons. -/

namespace GameTheory.Finite

open scoped BigOperators

/-- Common-denominator mixed strategies and their best-response payoff numerators. -/
structure BimatrixCertificate (m n : ℕ) where
  /-- Row probability numerators. -/
  rowWeights : Fin m → ℕ
  /-- Column probability numerators. -/
  colWeights : Fin n → ℕ
  /-- Common denominator for row probabilities. -/
  rowDenominator : ℕ
  /-- Common denominator for column probabilities. -/
  colDenominator : ℕ
  /-- Row best-response payoff numerator, over the column denominator. -/
  rowUtilityNumerator : ℤ
  /-- Column best-response payoff numerator, over the row denominator. -/
  colUtilityNumerator : ℤ

namespace BimatrixCertificate

/-- Probability and signed payoff fields fit the advertised binary magnitude width. -/
def FitsWidth {m n : ℕ} (c : BimatrixCertificate m n) (W : ℕ) : Prop :=
  c.rowDenominator < 2 ^ W ∧ c.colDenominator < 2 ^ W ∧
    (∀ i, c.rowWeights i < 2 ^ W) ∧ (∀ j, c.colWeights j < 2 ^ W) ∧
    c.rowUtilityNumerator.natAbs < 2 ^ W ∧ c.colUtilityNumerator.natAbs < 2 ^ W

/-- Payoff numerator for a pure row against the column weights. -/
def rowScore {m n : ℕ} (A : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n)
    (i : Fin m) : ℤ := ∑ j, A i j * (c.colWeights j : ℤ)

/-- Payoff numerator for a pure column against the row weights. -/
def colScore {m n : ℕ} (B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n)
    (j : Fin n) : ℤ := ∑ i, B i j * (c.rowWeights i : ℤ)

/-- Normalized weights, no improving pure deviation, and best-response equality
for every action given positive weight. -/
def Valid {m n : ℕ} (A B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n) : Prop :=
  0 < c.rowDenominator ∧ 0 < c.colDenominator ∧
    (∑ i, c.rowWeights i) = c.rowDenominator ∧
    (∑ j, c.colWeights j) = c.colDenominator ∧
    (∀ i, rowScore A c i ≤ c.rowUtilityNumerator ∧
      (0 < c.rowWeights i → rowScore A c i = c.rowUtilityNumerator)) ∧
    (∀ j, colScore B c j ≤ c.colUtilityNumerator ∧
      (0 < c.colWeights j → colScore B c j = c.colUtilityNumerator))

instance {m n : ℕ} (A B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n) :
    Decidable (Valid A B c) := by unfold Valid; infer_instance

/-- A valid certificate has a positive row probability denominator. -/
theorem Valid.rowDenominator_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) : 0 < c.rowDenominator := hc.1

/-- A valid certificate has a positive column probability denominator. -/
theorem Valid.colDenominator_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) : 0 < c.colDenominator := hc.2.1

/-- Row probability numerators sum to the row denominator. -/
theorem Valid.sum_rowWeights {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) :
    (∑ i, c.rowWeights i) = c.rowDenominator := hc.2.2.1

/-- Column probability numerators sum to the column denominator. -/
theorem Valid.sum_colWeights {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) :
    (∑ j, c.colWeights j) = c.colDenominator := hc.2.2.2.1

/-- Every row score is bounded by the certified row utility numerator. -/
theorem Valid.rowScore_le {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) (i : Fin m) :
    rowScore A c i ≤ c.rowUtilityNumerator := (hc.2.2.2.2.1 i).1

/-- Every column score is bounded by the certified column utility numerator. -/
theorem Valid.colScore_le {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) (j : Fin n) :
    colScore B c j ≤ c.colUtilityNumerator := (hc.2.2.2.2.2 j).1

/-- A positively weighted row attains the certified row utility numerator. -/
theorem Valid.rowScore_eq_of_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {i : Fin m}
    (hi : 0 < c.rowWeights i) : rowScore A c i = c.rowUtilityNumerator :=
  (hc.2.2.2.2.1 i).2 hi

/-- A positively weighted column attains the certified column utility numerator. -/
theorem Valid.colScore_eq_of_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {j : Fin n}
    (hj : 0 < c.colWeights j) : colScore B c j = c.colUtilityNumerator :=
  (hc.2.2.2.2.2 j).2 hj

/-- Every positively weighted row weakly outperforms every alternative row. -/
theorem rowScore_le_of_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {i : Fin m}
    (hi : 0 < c.rowWeights i) (j : Fin m) : rowScore A c j ≤ rowScore A c i := by
  rw [hc.rowScore_eq_of_pos hi]
  exact hc.rowScore_le j

/-- Every positively weighted column weakly outperforms every alternative column. -/
theorem colScore_le_of_pos {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {i : Fin n}
    (hi : 0 < c.colWeights i) (j : Fin n) : colScore B c j ≤ colScore B c i := by
  rw [hc.colScore_eq_of_pos hi]
  exact hc.colScore_le j

/-- A strictly inferior row has zero weight in every accepted certificate. -/
theorem rowWeights_eq_zero_of_rowScore_lt {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {i j : Fin m}
    (hij : rowScore A c i < rowScore A c j) : c.rowWeights i = 0 := by
  by_contra hi
  exact (not_lt_of_ge (rowScore_le_of_pos hc (Nat.pos_of_ne_zero hi) j)) hij

/-- A strictly inferior column has zero weight in every accepted certificate. -/
theorem colWeights_eq_zero_of_colScore_lt {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {c : BimatrixCertificate m n} (hc : c.Valid A B) {i j : Fin n}
    (hij : colScore B c i < colScore B c j) : c.colWeights i = 0 := by
  by_contra hi
  exact (not_lt_of_ge (colScore_le_of_pos hc (Nat.pos_of_ne_zero hi) j)) hij

end BimatrixCertificate

/-- Check a supplied rectangular bimatrix certificate using exact arithmetic. -/
def verifyBimatrixCertificate {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) : Bool := decide (c.Valid A B)

@[simp] theorem verifyBimatrixCertificate_eq_true_iff {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n) :
    verifyBimatrixCertificate A B c = true ↔ c.Valid A B := by
  simp [verifyBimatrixCertificate]

end GameTheory.Finite
