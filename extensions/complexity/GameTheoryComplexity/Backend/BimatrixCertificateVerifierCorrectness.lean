import GameTheoryComplexity.Backend.BimatrixCertificateVerifier
import GameTheoryComplexity.Backend.NashCertificateFormat

/-! The binary verifier checks exactly the integer numerator certificate constraints.
Signed payoffs are evaluated as separate positive and negative binary sums.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixTable
open scoped BigOperators

private theorem andBit_singleton (a b : Bool) :
    andBit [a] [b] = [a && b] := by cases a <;> cases b <;> rfl

private theorem orBit_singleton (a b : Bool) :
    orBit [a] [b] = [a || b] := by cases a <;> cases b <;> rfl

private theorem notBit_singleton (a : Bool) : notBit [a] = [!a] := by cases a <;> rfl

/-- A dimension ruler consists only of true bits. -/
theorem certificateDimensionWord_eq (input : List Bool) :
    certificateDimensionWord input = List.replicate (decodeDimension input) true := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    cases b
    · rfl
    · simpa [certificateDimensionWord, decodeDimension, List.replicate_succ] using
        congrArg (List.cons true) ih

/-- Machine field addressing is the shared total certificate parser. -/
theorem certificateFieldWord_eq (k : ℕ) (input cert : List Bool) :
    certificateFieldWord ![List.replicate k true, input, cert] =
      nashCertificateField (certificateWidthWord input).length k cert := by
  simp [certificateFieldWord, nashCertificateField]

/-- Weight addressing uses the row block followed by the column block. -/
theorem certificateWeightWord_eq (rowWeights : Bool) (k : ℕ) (input cert : List Bool) :
    certificateWeightWord rowWeights ![List.replicate k true, input, cert] =
      nashCertificateField (certificateWidthWord input).length
        (if rowWeights then 4 + k else 4 + decodeDimension input + k) cert := by
  cases rowWeights <;> simp [certificateWeightWord, certificateFieldWord,
    nashCertificateField, certificateDimensionWord_length]
    <;> congr 2 <;> ring

/-- Binary equality compares values rather than bit padding. -/
theorem certificateEqualWord_value (x y : List Bool) :
    certificateEqualWord x y = [decide (Nat.fromBitsLE x = Nat.fromBitsLE y)] := by
  rw [certificateEqualWord, binaryCertificateLE_value, binaryCertificateLE_value,
    andBit_singleton]
  by_cases hxy : Nat.fromBitsLE x ≤ Nat.fromBitsLE y
  · by_cases hyx : Nat.fromBitsLE y ≤ Nat.fromBitsLE x
    · simp [Nat.le_antisymm hxy hyx]
    · have hne : Nat.fromBitsLE x ≠ Nat.fromBitsLE y := by omega
      simp [hxy, hyx, hne]
  · have hne : Nat.fromBitsLE x ≠ Nat.fromBitsLE y := by omega
    simp [hxy, hne]

/-- The two tally scans reconstruct the total decoder's signed payoff. -/
theorem matrixTallyWord_payoff (input : List Bool) (i j : ℕ) :
    decodedPayoff input i j =
      ((matrixTallyWord true ![List.replicate i true, List.replicate j true, input]).count
        true : ℤ) -
      ((matrixTallyWord false ![List.replicate i true, List.replicate j true, input]).count
        true : ℤ) := by
  simp [matrixTallyWord, decodedPayoff, smash_length,
    certificateDimensionWord_length, List.take_take, List.drop_take, List.drop_drop]
  congr 3 <;> congr 1
  all_goals first | omega | (congr 1; ring)

/-- A score scan gives the usual finite sum of weighted tally counts. -/
theorem matrixScoreWord_value (rowWeights positive : Bool) (i : ℕ)
    (input cert : List Bool) :
    Nat.fromBitsLE (matrixScoreWord rowWeights positive
      ![List.replicate i true, input, cert]) =
      ∑ j : Fin (decodeDimension input),
        (matrixTallyWord positive
          ![List.replicate i true, List.replicate j.val true, input]).count true *
        Nat.fromBitsLE (certificateWeightWord rowWeights
          ![List.replicate j.val true, input, cert]) := by
  unfold matrixScoreWord
  rw [certificateDimensionWord_eq, binaryIndexedSum_value]
  change (∑ j ∈ Finset.range (decodeDimension input), Nat.fromBitsLE
    (matrixWeightedTerm rowWeights positive
      ![List.replicate j true, List.replicate i true, input, cert])) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (matrixTallyWord positive ![List.replicate i true, List.replicate j true, input]).count
      true * Nat.fromBitsLE
        (certificateWeightWord rowWeights ![List.replicate j true, input, cert]))]
  apply Finset.sum_congr rfl
  intro j hj
  simp [matrixWeightedTerm, binaryTallySum_value]

/-- The normalization scan sums exactly the fields of the selected distribution. -/
theorem certificateWeightSumWord_value (rowWeights : Bool) (input cert : List Bool) :
    Nat.fromBitsLE (certificateWeightSumWord rowWeights ![input, cert]) =
      ∑ j : Fin (decodeDimension input), Nat.fromBitsLE (certificateWeightWord rowWeights
        ![List.replicate j.val true, input, cert]) := by
  unfold certificateWeightSumWord
  rw [certificateDimensionWord_eq, binaryIndexedSum_value]
  change (∑ j ∈ Finset.range (decodeDimension input), Nat.fromBitsLE
    (certificateWeightWord rowWeights ![List.replicate j true, input, cert])) = _
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => Nat.fromBitsLE
    (certificateWeightWord rowWeights ![List.replicate j true, input, cert])) _).symm

/-- Subtracting the negative score from the positive score gives the decoded integer score. -/
theorem matrixScoreWord_difference (rowWeights : Bool) (i : ℕ)
    (input cert : List Bool) :
    (Nat.fromBitsLE (matrixScoreWord rowWeights true
      ![List.replicate i true, input, cert]) : ℤ) -
      (Nat.fromBitsLE (matrixScoreWord rowWeights false
        ![List.replicate i true, input, cert]) : ℤ) =
      ∑ j : Fin (decodeDimension input), decodedPayoff input i j.val *
        (Nat.fromBitsLE (certificateWeightWord rowWeights
          ![List.replicate j.val true, input, cert]) : ℤ) := by
  rw [matrixScoreWord_value, matrixScoreWord_value]
  simp only [Nat.cast_sum, Nat.cast_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixTallyWord_payoff]
  ring

private theorem certificateAll_flag {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) :
    certificateAll term clock params = [true] ∨
      certificateAll term clock params = [false] := by
  cases clock with
  | nil => exact Or.inl rfl
  | cons b clock =>
    simp only [certificateAll, recNotation_cons, Bool.cond_self, certificateAllStep]
    exact andBit_flag _ _

private theorem certificateAll_eq_true_iff {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (n : ℕ) (params : Fin p → List Bool)
    (hterm : ∀ i, term (Fin.cons (List.replicate i true) params) = [true] ∨
      term (Fin.cons (List.replicate i true) params) = [false]) :
    certificateAll term (List.replicate n true) params = [true] ↔
      ∀ i < n, term (Fin.cons (List.replicate i true) params) = [true] := by
  induction n with
  | zero => simp [certificateAll]
  | succ n ih =>
    change andBit (certificateAll term (List.replicate n true) params)
      (term (Fin.cons (List.replicate n true) params)) = [true] ↔ _
    rw [andBit_eq_true_iff (certificateAll_flag _ _ _) (hterm n), ih]
    constructor
    · rintro ⟨hall, hn⟩ i hi
      by_cases hin : i < n
      · exact hall i hin
      · have hieq : i = n := by omega
        exact hieq ▸ hn
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall n (Nat.lt_succ_self _)⟩

private theorem matrixActionCheck_raw_iff (columnPlayer : Bool) (i : ℕ)
    (input cert : List Bool) :
    let v := ![List.replicate i true, input, cert]
    let pos := Nat.fromBitsLE (matrixScoreWord columnPlayer true v)
    let neg := Nat.fromBitsLE (matrixScoreWord columnPlayer false v)
    let utility := Nat.fromBitsLE (certificateFieldWord
      ![List.replicate (if columnPlayer then 3 else 2) true, input, cert])
    let support := Nat.fromBitsLE (certificateWeightWord (!columnPlayer) v)
    matrixActionCheck columnPlayer v = [true] ↔
      pos ≤ neg + utility ∧ (0 < support → pos = neg + utility) := by
  dsimp only
  unfold matrixActionCheck
  dsimp only
  rw [binaryCertificateLE_value, certificateEqualWord_value, certificateEqualWord_value,
    orBit_singleton, andBit_singleton, binaryCertificateAdd_value]
  simp only [List.cons.injEq, and_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  have hz : Nat.fromBitsLE [] = 0 := rfl
  rw [hz]
  cases columnPlayer <;> simp
  all_goals omega

private theorem score_constraints_iff (pos neg utility support : ℕ) :
    (pos ≤ neg + utility ∧ (0 < support → pos = neg + utility)) ↔
      ((pos : ℤ) - (neg : ℤ) ≤ (utility : ℤ) ∧
        (0 < support → (pos : ℤ) - (neg : ℤ) = (utility : ℤ))) := by omega

/-- One machine action check is the canonical numerator deviation/support constraint. -/
theorem matrixActionCheck_eq_true_iff (columnPlayer : Bool)
    (input cert : List Bool) (i : Fin (decodeDimension input)) :
    let c := decodeNashCertificate (decodeDimension input)
      (certificateWidthWord input).length cert
    let A := fun i j : Fin (decodeDimension input) => decodedPayoff input i.val j.val
    matrixActionCheck columnPlayer ![List.replicate i.val true, input, cert] = [true] ↔
      if columnPlayer then
        NumeratorCertificate.colScore A c i ≤ (c.colUtilityNumerator : ℤ) ∧
          (0 < c.colWeights i →
            NumeratorCertificate.colScore A c i = (c.colUtilityNumerator : ℤ))
      else
        NumeratorCertificate.rowScore A c i ≤ (c.rowUtilityNumerator : ℤ) ∧
          (0 < c.rowWeights i →
            NumeratorCertificate.rowScore A c i = (c.rowUtilityNumerator : ℤ)) := by
  dsimp only
  have hraw := matrixActionCheck_raw_iff columnPlayer i.val input cert
  dsimp only at hraw
  rw [hraw]
  cases columnPlayer
  all_goals
    simp only [certificateWeightWord_eq, certificateFieldWord_eq,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [score_constraints_iff, matrixScoreWord_difference]
    simp only [certificateWeightWord_eq]
    rfl

/-- Checking all indexed actions gives all canonical numerator constraints. -/
theorem matrixAllChecks_eq_true_iff (columnPlayer : Bool) (input cert : List Bool) :
    matrixAllChecks columnPlayer ![input, cert] = [true] ↔
      ∀ i : Fin (decodeDimension input),
        matrixActionCheck columnPlayer ![List.replicate i.val true, input, cert] = [true] := by
  unfold matrixAllChecks
  rw [certificateDimensionWord_eq]
  have hflag (i : ℕ) :
      matrixActionCheck columnPlayer (Fin.cons (List.replicate i true) ![input, cert]) =
          [true] ∨
        matrixActionCheck columnPlayer (Fin.cons (List.replicate i true) ![input, cert]) =
          [false] := andBit_flag _ _
  rw [certificateAll_eq_true_iff _ _ _ hflag]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

private theorem flag_eq_decide (x : List Bool) (P : Prop) [Decidable P]
    (hflag : x = [true] ∨ x = [false]) (hiff : x = [true] ↔ P) :
    x = [decide P] := by
  by_cases hp : P
  · simpa only [hp, decide_true] using hiff.mpr hp
  · rcases hflag with hx | hx
    · exact False.elim (hp (hiff.mp hx))
    · simpa only [hp, decide_false] using hx

private theorem lenEqFlag_value (x y : List Bool) :
    lenEqFlag x y = [decide (x.length = y.length)] :=
  flag_eq_decide _ _ (lenEqFlag_flag _ _) (lenEqFlag_eq_true_iff _ _)

private theorem matrixAllChecks_value (columnPlayer : Bool) (input cert : List Bool) :
    let c := decodeNashCertificate (decodeDimension input)
      (certificateWidthWord input).length cert
    let A := fun i j : Fin (decodeDimension input) => decodedPayoff input i.val j.val
    matrixAllChecks columnPlayer ![input, cert] =
      [decide (∀ i, if columnPlayer then
        NumeratorCertificate.colScore A c i ≤ (c.colUtilityNumerator : ℤ) ∧
          (0 < c.colWeights i →
            NumeratorCertificate.colScore A c i = (c.colUtilityNumerator : ℤ))
        else
        NumeratorCertificate.rowScore A c i ≤ (c.rowUtilityNumerator : ℤ) ∧
          (0 < c.rowWeights i →
            NumeratorCertificate.rowScore A c i = (c.rowUtilityNumerator : ℤ)))] := by
  classical
  apply flag_eq_decide
  · exact certificateAll_flag _ _ _
  · exact (matrixAllChecks_eq_true_iff columnPlayer input cert).trans
      (forall_congr' (fun i => matrixActionCheck_eq_true_iff columnPlayer input cert i))

/-- The actual binary machine accepts exactly an exact-length, valid numerator certificate. -/
theorem binaryCertificateVerifier_eq_true_iff (input cert : List Bool) :
    binaryCertificateVerifier ![input, cert] = [true] ↔
      cert.length = (4 + 2 * decodeDimension input) * (certificateWidthWord input).length ∧
        (decodeNashCertificate (decodeDimension input)
          (certificateWidthWord input).length cert).Valid
            (fun i j => decodedPayoff input i.val j.val) := by
  classical
  have hr := matrixAllChecks_value false input cert
  have hc := matrixAllChecks_value true input cert
  dsimp only at hr hc
  unfold binaryCertificateVerifier
  dsimp only
  rw [hr, hc, lenEqFlag_value]
  simp only [certificateEqualWord_value, binaryCertificateLE_value,
    certificateWeightSumWord_value, certificateWeightWord_eq, certificateFieldWord_eq,
    andBit_singleton, notBit_singleton, List.cons.injEq, and_true, Bool.and_eq_true,
    decide_eq_true_eq,
    decodeNashCertificate, NumeratorCertificate.Valid]
  have hz : Nat.fromBitsLE [] = 0 := rfl
  simp only [hz, smash_length, List.length_append, List.length_replicate,
    certificateDimensionWord_length]
  constructor <;> intro h <;>
    simpa [Nat.pos_iff_ne_zero, Nat.add_comm, Nat.mul_comm, two_mul] using h

end GameTheory.Complexity.Backend
