import GameTheoryComplexity.Backend.GeneralBimatrixVerifier
import GameTheoryComplexity.Backend.BimatrixCertificateVerifierCorrectness

/-! The binary rectangular-game verifier agrees with the canonical signed
integer certificate predicates, including support-sensitive best responses. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite
open scoped BigOperators

private theorem andBit_singleton (a b : Bool) :
    andBit [a] [b] = [a && b] := by cases a <;> cases b <;> rfl
private theorem orBit_singleton (a b : Bool) :
    orBit [a] [b] = [a || b] := by cases a <;> cases b <;> rfl
private theorem notBit_singleton (a : Bool) : notBit [a] = [!a] := by cases a <;> rfl

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

theorem generalCertificateFieldWord_eq (k : ℕ) (input cert : List Bool) :
    generalCertificateFieldWord ![List.replicate k true, input, cert] =
      generalBinaryField (generalCertificateWidth input.length) k cert := by
  simp [generalCertificateFieldWord, generalBinaryField, generalWidthRuler_length]

theorem generalWeightWord_eq (columnWeights : Bool) (k : ℕ) (input cert : List Bool) :
    generalWeightWord columnWeights ![List.replicate k true, input, cert] =
      generalBinaryField (generalCertificateWidth input.length)
        (if columnWeights then 6 + generalRowCount input + k else 6 + k) cert := by
  cases columnWeights <;> simp [generalWeightWord, generalCertificateFieldWord,
    generalBinaryField, generalWidthRuler_length, generalRowCount]
  all_goals (congr 2; ring)

theorem generalPayoffWord_eq (columnPlayer positive : Bool) (i j : ℕ)
    (input : List Bool) :
    generalPayoffWord columnPlayer positive
      ![List.replicate i true, List.replicate j true, input] =
      generalPayoffField columnPlayer positive input i j := by
  cases columnPlayer <;> cases positive <;>
    simp [generalPayoffWord, generalPayoffField, generalBinaryField,
      generalRowCount, generalColCount, generalCoefficientBits, smash_length]
  all_goals (congr 2; ring)

theorem generalScoreWord_value (columnPlayer positive : Bool) (i : ℕ)
    (input cert : List Bool) :
    Nat.fromBitsLE (generalScoreWord columnPlayer positive
      ![List.replicate i true, input, cert]) =
      ∑ j : Fin ((generalActionRuler (!columnPlayer) input).length),
        Nat.fromBitsLE (generalPayoffField columnPlayer positive input
          (if columnPlayer then j.val else i) (if columnPlayer then i else j.val)) *
        Nat.fromBitsLE (generalWeightWord (!columnPlayer)
          ![List.replicate j.val true, input, cert]) := by
  have hr : generalActionRuler (!columnPlayer) input =
      List.replicate (generalActionRuler (!columnPlayer) input).length true := by
    cases columnPlayer <;> simp only [Bool.not_true, Bool.not_false, generalActionRuler]
    · exact generalColRuler_eq input
    · exact generalRowRuler_eq input
  unfold generalScoreWord
  change Nat.fromBitsLE (binaryIndexedSum (generalWeightedTerm columnPlayer positive)
    (generalActionRuler (!columnPlayer) input) ![List.replicate i true, input, cert]) = _
  conv_lhs => rw [hr]
  rw [binaryIndexedSum_value]
  change (∑ j ∈ Finset.range (generalActionRuler (!columnPlayer) input).length,
    Nat.fromBitsLE (generalWeightedTerm columnPlayer positive
      ![List.replicate j true, List.replicate i true, input, cert])) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    Nat.fromBitsLE (generalPayoffField columnPlayer positive input
      (if columnPlayer then j else i) (if columnPlayer then i else j)) *
      Nat.fromBitsLE (generalWeightWord (!columnPlayer)
        ![List.replicate j true, input, cert]))]
  apply Finset.sum_congr rfl
  intro j hj
  cases columnPlayer <;> simp [generalWeightedTerm, binaryWordMul_value,
    generalPayoffWord_eq]

theorem generalWeightSumWord_value (columnWeights : Bool) (input cert : List Bool) :
    Nat.fromBitsLE (generalWeightSumWord columnWeights ![input, cert]) =
      ∑ j : Fin ((generalActionRuler columnWeights input).length),
        Nat.fromBitsLE (generalWeightWord columnWeights
          ![List.replicate j.val true, input, cert]) := by
  have hr : generalActionRuler columnWeights input =
      List.replicate (generalActionRuler columnWeights input).length true := by
    cases columnWeights
    · exact generalRowRuler_eq input
    · exact generalColRuler_eq input
  unfold generalWeightSumWord
  change Nat.fromBitsLE (binaryIndexedSum (generalWeightWord columnWeights)
    (generalActionRuler columnWeights input) ![input, cert]) = _
  conv_lhs => rw [hr]
  rw [binaryIndexedSum_value]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    Nat.fromBitsLE (generalWeightWord columnWeights
      ![List.replicate j true, input, cert])) _).symm

theorem generalScoreWord_difference (columnPlayer : Bool) (i : ℕ)
    (input cert : List Bool) :
    (Nat.fromBitsLE (generalScoreWord columnPlayer true
      ![List.replicate i true, input, cert]) : ℤ) -
      (Nat.fromBitsLE (generalScoreWord columnPlayer false
        ![List.replicate i true, input, cert]) : ℤ) =
      ∑ j : Fin ((generalActionRuler (!columnPlayer) input).length),
        decodeGeneralPayoff columnPlayer input
          (if columnPlayer then j.val else i) (if columnPlayer then i else j.val) *
          (Nat.fromBitsLE (generalWeightWord (!columnPlayer)
            ![List.replicate j.val true, input, cert]) : ℤ) := by
  rw [generalScoreWord_value, generalScoreWord_value]
  simp only [Nat.cast_sum, Nat.cast_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [decodeGeneralPayoff]
  ring

private theorem generalActionCheck_raw_iff (columnPlayer : Bool) (i : ℕ)
    (input cert : List Bool) :
    let v := ![List.replicate i true, input, cert]
    let pos := Nat.fromBitsLE (generalScoreWord columnPlayer true v)
    let neg := Nat.fromBitsLE (generalScoreWord columnPlayer false v)
    let utilityPos := generalNatField (generalCertificateWidth input.length)
      (if columnPlayer then 4 else 2) cert
    let utilityNeg := generalNatField (generalCertificateWidth input.length)
      (if columnPlayer then 5 else 3) cert
    let support := Nat.fromBitsLE (generalWeightWord columnPlayer v)
    generalActionCheck columnPlayer v = [true] ↔
      pos + utilityNeg ≤ neg + utilityPos ∧
        (0 < support → pos + utilityNeg = neg + utilityPos) := by
  dsimp only
  unfold generalActionCheck
  dsimp only
  rw [binaryCertificateLE_value, certificateEqualWord_value, certificateEqualWord_value,
    orBit_singleton, andBit_singleton, binaryCertificateAdd_value,
    binaryCertificateAdd_value]
  simp only [List.cons.injEq, and_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  have hz : Nat.fromBitsLE [] = 0 := rfl
  rw [hz]
  cases columnPlayer <;> simp [generalCertificateFieldWord, generalWidthRuler_length,
    generalBinaryField, generalNatField]
  all_goals omega

private theorem signed_constraints_iff (pos neg up un support : ℕ) :
    (pos + un ≤ neg + up ∧ (0 < support → pos + un = neg + up)) ↔
      ((pos : ℤ) - (neg : ℤ) ≤ (up : ℤ) - (un : ℤ) ∧
        (0 < support → (pos : ℤ) - (neg : ℤ) = (up : ℤ) - (un : ℤ))) := by omega

theorem generalRowActionCheck_eq_true_iff (input cert : List Bool)
    (i : Fin (generalRowCount input)) :
    let c := decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) cert
    let A := fun i j => decodeGeneralPayoff false input i.val j.val
    generalActionCheck false ![List.replicate i.val true, input, cert] = [true] ↔
      BimatrixCertificate.rowScore A c i ≤ c.rowUtilityNumerator ∧
        (0 < c.rowWeights i → BimatrixCertificate.rowScore A c i = c.rowUtilityNumerator) := by
  dsimp only
  have hraw := generalActionCheck_raw_iff false i.val input cert
  dsimp only at hraw
  rw [hraw]
  rw [signed_constraints_iff, generalScoreWord_difference]
  simp only [Bool.not_false, generalActionRuler, Bool.false_eq_true,
    ↓reduceIte, generalWeightWord_eq]
  rfl

theorem generalColActionCheck_eq_true_iff (input cert : List Bool)
    (j : Fin (generalColCount input)) :
    let c := decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) cert
    let B := fun i j => decodeGeneralPayoff true input i.val j.val
    generalActionCheck true ![List.replicate j.val true, input, cert] = [true] ↔
      BimatrixCertificate.colScore B c j ≤ c.colUtilityNumerator ∧
        (0 < c.colWeights j → BimatrixCertificate.colScore B c j = c.colUtilityNumerator) := by
  dsimp only
  have hraw := generalActionCheck_raw_iff true j.val input cert
  dsimp only at hraw
  rw [hraw]
  rw [signed_constraints_iff, generalScoreWord_difference]
  simp only [Bool.not_true, generalActionRuler, Bool.false_eq_true,
    ↓reduceIte, generalWeightWord_eq]
  rfl

theorem generalAllChecks_eq_true_iff (columnPlayer : Bool) (input cert : List Bool) :
    generalAllChecks columnPlayer ![input, cert] = [true] ↔
      ∀ i : Fin (generalActionRuler columnPlayer input).length,
        generalActionCheck columnPlayer ![List.replicate i.val true, input, cert] = [true] := by
  have hr : generalActionRuler columnPlayer input =
      List.replicate (generalActionRuler columnPlayer input).length true := by
    cases columnPlayer
    · exact generalRowRuler_eq input
    · exact generalColRuler_eq input
  unfold generalAllChecks
  change certificateAll (generalActionCheck columnPlayer)
    (generalActionRuler columnPlayer input) ![input, cert] = [true] ↔ _
  conv_lhs => rw [hr]
  have hflag (i : ℕ) :
      generalActionCheck columnPlayer (Fin.cons (List.replicate i true) ![input, cert]) =
        [true] ∨
      generalActionCheck columnPlayer (Fin.cons (List.replicate i true) ![input, cert]) =
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

private theorem eqFlag_value (x y : List Bool) :
    eqFlag x y = [decide (x = y)] :=
  flag_eq_decide _ _ (eqFlag_flag _ _) (eqFlag_eq_true_iff _ _)

private theorem generalRowAllChecks_value (input cert : List Bool) :
    let c := decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) cert
    let A := fun i j => decodeGeneralPayoff false input i.val j.val
    generalAllChecks false ![input, cert] =
      [decide (∀ i, BimatrixCertificate.rowScore A c i ≤ c.rowUtilityNumerator ∧
        (0 < c.rowWeights i →
          BimatrixCertificate.rowScore A c i = c.rowUtilityNumerator))] := by
  apply flag_eq_decide
  · exact certificateAll_flag _ _ _
  · exact (generalAllChecks_eq_true_iff false input cert).trans
      (forall_congr' (fun i => generalRowActionCheck_eq_true_iff input cert i))

private theorem generalColAllChecks_value (input cert : List Bool) :
    let c := decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) cert
    let B := fun i j => decodeGeneralPayoff true input i.val j.val
    generalAllChecks true ![input, cert] =
      [decide (∀ j, BimatrixCertificate.colScore B c j ≤ c.colUtilityNumerator ∧
        (0 < c.colWeights j →
          BimatrixCertificate.colScore B c j = c.colUtilityNumerator))] := by
  apply flag_eq_decide
  · exact certificateAll_flag _ _ _
  · exact (generalAllChecks_eq_true_iff true input cert).trans
      (forall_congr' (fun j => generalColActionCheck_eq_true_iff input cert j))

/-- The actual machine checks exactly the signed integer Nash certificate. -/
theorem generalValidCertificateVerdict_eq_true_iff (input cert : List Bool) :
    generalValidCertificateVerdict ![input, cert] = [true] ↔
      cert.length = (6 + generalRowCount input + generalColCount input) *
        generalCertificateWidth input.length ∧
      (decodeGeneralCertificate (generalRowCount input) (generalColCount input)
        (generalCertificateWidth input.length) cert).Valid
        (fun i j => decodeGeneralPayoff false input i.val j.val)
        (fun i j => decodeGeneralPayoff true input i.val j.val) := by
  have hr := generalRowAllChecks_value input cert
  have hc := generalColAllChecks_value input cert
  dsimp only at hr hc
  unfold generalValidCertificateVerdict
  dsimp only
  rw [hr, hc, lenEqFlag_value]
  simp only [certificateEqualWord_value, generalWeightSumWord_value,
    generalWeightWord_eq, generalCertificateFieldWord, generalWidthRuler_length,
    andBit_singleton, notBit_singleton, List.cons.injEq, and_true, Bool.and_eq_true,
    decide_eq_true_eq, decodeGeneralCertificate, BimatrixCertificate.Valid]
  have hz : Nat.fromBitsLE [] = 0 := rfl
  simp only [hz, smash_length, List.length_append, List.length_replicate,
    generalWidthRuler_length, generalActionRuler, Bool.false_eq_true,
    ↓reduceIte, generalRowCount, generalColCount, generalNatField, generalBinaryField]
  constructor <;> intro h
  all_goals
    simp [Nat.pos_iff_ne_zero, Nat.add_comm, Nat.add_left_comm] at h ⊢
    exact h

theorem generalInstanceFlag_eq_true_iff (input : List Bool) :
    generalInstanceFlag input = [true] ↔ GeneralInstanceValid input := by
  unfold generalInstanceFlag
  rw [eqFlag_value, eqFlag_value, eqFlag_value, lenEqFlag_value]
  simp only [andBit_singleton, notBit_singleton, List.cons.injEq, and_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    generalInstanceLengthRuler, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, smash_length, GeneralInstanceValid,
    generalRowCount, generalColCount, generalCoefficientBits]
  simp only [← List.length_eq_zero_iff, Nat.pos_iff_ne_zero, Nat.add_assoc, Nat.mul_assoc, Nat.zero_add, Nat.reduceAdd]

private theorem generalInstanceFlag_value (input : List Bool) :
    generalInstanceFlag input = [decide (GeneralInstanceValid input)] :=
  flag_eq_decide _ _ (andBit_flag _ _) (generalInstanceFlag_eq_true_iff input)

/-- Valid games use exact certificates; malformed games accept only the empty word. -/
theorem generalBimatrixVerdict_eq_true_iff (input cert : List Bool) :
    generalBimatrixVerdict ![input, cert] = [true] ↔
      (GeneralInstanceValid input ∧
        cert.length = (6 + generalRowCount input + generalColCount input) *
          generalCertificateWidth input.length ∧
        (decodeGeneralCertificate (generalRowCount input) (generalColCount input)
          (generalCertificateWidth input.length) cert).Valid
          (fun i j => decodeGeneralPayoff false input i.val j.val)
          (fun i j => decodeGeneralPayoff true input i.val j.val)) ∨
      (¬ GeneralInstanceValid input ∧ cert = []) := by
  unfold generalBimatrixVerdict
  change orBit (andBit (generalInstanceFlag input) (generalValidCertificateVerdict ![input, cert]))
    (andBit (notBit (generalInstanceFlag input)) (eqFlag cert [])) = [true] ↔ _
  let P := cert.length = (6 + generalRowCount input + generalColCount input) *
    generalCertificateWidth input.length ∧
    (decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) cert).Valid
      (fun i j => decodeGeneralPayoff false input i.val j.val)
      (fun i j => decodeGeneralPayoff true input i.val j.val)
  have hv : generalValidCertificateVerdict ![input, cert] = [decide P] :=
    flag_eq_decide _ _ (andBit_flag _ _) (generalValidCertificateVerdict_eq_true_iff input cert)
  rw [generalInstanceFlag_value, hv, eqFlag_value, notBit_singleton,
    andBit_singleton, andBit_singleton, orBit_singleton]
  simp only [List.cons.injEq, and_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  rfl

end GameTheory.Complexity.Backend
