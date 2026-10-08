import GameTheoryComplexity.Backend.GeneralBimatrixMatrixWord
import GameTheoryComplexity.Backend.GeneralBimatrixVerifier

/-! Binary emission of the certificate at a supplied complementary basis.
The input contains the already computed determinant and packed dictionary.
All loops use explicitly represented dimension and field-width rulers. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open scoped BigOperators

/-- Clamp a signed word to its nonnegative part, retaining a signed header. -/
def endpointPositiveWord (x : List Bool) : List Bool :=
  caseBit₀ (bitAt [] x) [false] ([false] ++ x.tail)

theorem endpointPositiveWord_value (x : List Bool) :
    binarySignedValue (endpointPositiveWord x) = (binarySignedValue x).toNat := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> simp [endpointPositiveWord, bitAt, caseBit₀,
      binarySignedValue, Nat.fromBitsLE, Nat.fromBits]

theorem endpointPositiveWord_cobham :
    Cobham fun v : Fin 1 → List Bool => endpointPositiveWord (v 0) :=
  (Cobham.iteFn (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 0))
    (Cobham.const [false]) (Cobham.appendFn (Cobham.const [false])
      (Cobham.tailFn (.proj 0)))).of_eq fun _ => rfl

/-- A payoff coordinate from the supplied packed dictionary. Arguments are
ambient label ruler, instance, raw membership, determinant, coefficients, width. -/
def generalBimatrixEndpointWeightWord (v : Fin 6 → List Bool) : List Bool :=
  let position := v 0 ++ v 0 ++ [false]
  let ordinal := binarySubsetTally ((v 2).take position.length)
  let stride := generalBimatrixDimensionWord (v 1) ++ [false]
  caseBit₀ (bitAt position (v 2))
    (endpointPositiveWord (binarySignedRowField ![smash ordinal stride, v 5, v 4])) [false]

theorem generalBimatrixEndpointWeightWord_cobham :
    Cobham generalBimatrixEndpointWeightWord := by
  have hp : Cobham fun v : Fin 6 → List Bool => v 0 ++ v 0 ++ [false] :=
    Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [false])
  have ho : Cobham fun v : Fin 6 → List Bool =>
      binarySubsetTally ((v 2).take (v 0 ++ v 0 ++ [false]).length) :=
    Cobham.comp binarySubsetTally_cobham fun _ => Cobham.takeFn hp (.proj 2)
  have hk : Cobham fun v : Fin 6 → List Bool =>
      generalBimatrixDimensionWord (v 1) ++ [false] :=
    Cobham.appendFn (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 1)
      (Cobham.const [false])
  have hf := Cobham.comp₃ binarySignedRowField_cobham
    (Cobham.comp₂ Cobham.smash ho hk) (.proj 5) (.proj 4)
  exact (Cobham.iteFn (Cobham.comp₂ Cobham.bitAtFn hp (.proj 2))
    (Cobham.comp endpointPositiveWord_cobham fun _ => hf) (Cobham.const [false])).of_eq
      fun _ => rfl

theorem generalBimatrixEndpointWeightWord_value (v : Fin 6 → List Bool) :
    binarySignedValue (generalBimatrixEndpointWeightWord v) =
      if ((v 2)[2 * (v 0).length + 1]?).getD false then
        (binarySignedRowValue (v 5) (v 4)
          (((v 2).take (2 * (v 0).length + 1)).count true *
            (generalRowCount (v 1) + generalColCount (v 1) + 1))).toNat
      else 0 := by
  have hget (word : List Bool) (n : ℕ) :
      (word.drop n).headD false = (word[n]?).getD false := by
    induction n generalizing word with
    | zero => cases word <;> rfl
    | succ n ih => cases word with
      | nil => rfl
      | cons a word => exact ih word
  rw [generalBimatrixEndpointWeightWord, bitAt_eq]
  simp only [List.length_append, List.length_singleton, bitOf,
    show (v 0).length + (v 0).length + 1 = 2 * (v 0).length + 1 by omega, hget]
  generalize ((v 2)[2 * (v 0).length + 1]?).getD false = b
  cases b
  · rfl
  · simp only [caseBit₀, Bool.cond_true]
    rw [endpointPositiveWord_value]
    simp only [↓reduceIte, binarySignedRowField,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, smash_length,
      binarySubsetTally_length, generalBimatrixDimensionWord_length, List.length_append,
      List.length_singleton, binarySignedRowValue]
    rfl

/-- Recover one player's indexed probability weight for the mass summation loop. -/
def generalBimatrixEndpointMassTermWord (columnPlayer : Bool) (v : Fin 6 → List Bool) : List Bool :=
  generalBimatrixEndpointWeightWord ![
    (bif columnPlayer then generalRowRuler (v 1) ++ v 0 else v 0),
    v 1, v 2, v 3, v 4, v 5]

private theorem massTerm_cobham (columnPlayer : Bool) : Cobham (generalBimatrixEndpointMassTermWord columnPlayer) := by
  apply Cobham.comp generalBimatrixEndpointWeightWord_cobham
  intro i
  fin_cases i
  · cases columnPlayer
    · exact .proj 0
    · exact Cobham.appendFn (Cobham.comp generalRowRuler_cobham fun _ => .proj 1) (.proj 0)
  · exact .proj 1
  · exact .proj 2
  · exact .proj 3
  · exact .proj 4
  · exact .proj 5

/-- Sum one player's Cramer weights at the supplied arithmetic width.
Arguments are instance, membership, determinant, coefficients and width. -/
def generalBimatrixEndpointMassWord (columnPlayer : Bool) (v : Fin 5 → List Bool) : List Bool :=
  binarySignedSum (generalBimatrixEndpointMassTermWord columnPlayer)
    (generalActionRuler columnPlayer (v 0)) (v 4) v

theorem generalBimatrixEndpointMassWord_cobham (columnPlayer : Bool) :
    Cobham (generalBimatrixEndpointMassWord columnPlayer) := by
  let gs : Fin 7 → (Fin 5 → List Bool) → List Bool := fun i v =>
    ![generalActionRuler columnPlayer (v 0), v 4, v 0, v 1, v 2, v 3, v 4] i
  have hg : ∀ i, Cobham (gs i) := by
    intro i
    fin_cases i
    · cases columnPlayer
      · exact Cobham.comp generalRowRuler_cobham fun _ => .proj 0
      · exact Cobham.comp generalColRuler_cobham fun _ => .proj 0
    · exact .proj 4
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
    · exact .proj 3
    · exact .proj 4
  exact (Cobham.comp (gs := gs) (binarySignedSum_cobham (massTerm_cobham columnPlayer)) hg).of_eq
    fun v => by congr 1; ext i; fin_cases i <;> rfl

/-- Undo the payoff shift using the opposite player's mass. -/
def generalBimatrixEndpointUtilityWord (columnPlayer : Bool) (v : Fin 5 → List Bool) : List Bool :=
  binarySignedFixedSub (v 4) ([false] ++ (v 2).tail)
    (binarySignedMul (generalPositiveShiftWord (v 0))
      (generalBimatrixEndpointMassWord (!columnPlayer) v))

theorem generalBimatrixEndpointUtilityWord_cobham (columnPlayer : Bool) :
    Cobham (generalBimatrixEndpointUtilityWord columnPlayer) :=
  (Cobham.comp₃ binarySignedFixedSub_cobham (.proj 4)
    (Cobham.appendFn (Cobham.const [false]) (Cobham.tailFn (.proj 2)))
    (Cobham.comp₂ binarySignedMul_cobham
      (Cobham.comp generalPositiveShiftWord_cobham fun _ => .proj 0)
      (generalBimatrixEndpointMassWord_cobham (!columnPlayer)))).of_eq fun _ => rfl

private def scalarWord : ℕ → (Fin 5 → List Bool) → List Bool
  | 0, v => generalBimatrixEndpointMassWord false v
  | 1, v => generalBimatrixEndpointMassWord true v
  | 2, v => generalBimatrixEndpointUtilityWord false v
  | 3, v => binarySignedNeg (generalBimatrixEndpointUtilityWord false v)
  | 4, v => generalBimatrixEndpointUtilityWord true v
  | 5, v => binarySignedNeg (generalBimatrixEndpointUtilityWord true v)
  | _, _ => [false]

private theorem scalarWord_cobham (n : ℕ) : Cobham (scalarWord n) := by
  rcases n with _ | n
  · exact generalBimatrixEndpointMassWord_cobham false
  rcases n with _ | n
  · exact generalBimatrixEndpointMassWord_cobham true
  rcases n with _ | n
  · exact generalBimatrixEndpointUtilityWord_cobham false
  rcases n with _ | n
  · exact (Cobham.comp binarySignedNeg_cobham fun _ =>
      generalBimatrixEndpointUtilityWord_cobham false).of_eq fun _ => rfl
  rcases n with _ | n
  · exact generalBimatrixEndpointUtilityWord_cobham true
  rcases n with _ | n
  · exact (Cobham.comp binarySignedNeg_cobham fun _ =>
      generalBimatrixEndpointUtilityWord_cobham true).of_eq fun _ => rfl
  exact Cobham.const [false]

private def fieldSignedWord : ℕ → (Fin 6 → List Bool) → List Bool
  | 0, v => generalBimatrixEndpointWeightWord
      ![(v 0).drop 6, v 1, v 2, v 3, v 4, v 5]
  | n + 1, v => caseBit₀ (lenEqFlag (v 0) (List.replicate n false))
      (scalarWord n (Fin.tail v)) (fieldSignedWord n v)

private theorem fieldSignedWord_cobham (n : ℕ) : Cobham (fieldSignedWord n) := by
  induction n with
  | zero =>
    exact (Cobham.comp generalBimatrixEndpointWeightWord_cobham fun i => by
      fin_cases i
      · exact Cobham.dropFn (Cobham.const (List.replicate 6 false)) (.proj 0)
      · exact .proj 1
      · exact .proj 2
      · exact .proj 3
      · exact .proj 4
      · exact .proj 5).of_eq fun _ => rfl
  | succ n ih =>
    exact (Cobham.iteFn (lenEqFlag_mem (.proj 0) (Cobham.const (List.replicate n false)))
      (Cobham.comp (scalarWord_cobham n) fun i => .proj i.succ) ih).of_eq fun _ => rfl

private def fieldWord (v : Fin 6 → List Bool) : List Bool :=
  padTo (generalWidthRuler (v 1)) (endpointPositiveWord (fieldSignedWord 6 v)).tail

private theorem fieldWord_cobham : Cobham fieldWord :=
  (Cobham.padFn
    (Cobham.comp generalWidthRuler_cobham fun _ => .proj 1)
    (Cobham.tailFn (Cobham.comp endpointPositiveWord_cobham
      fun _ => fieldSignedWord_cobham 6))).of_eq fun _ => rfl

private def emitStep (v : Fin 7 → List Bool) : List Bool :=
  v 1 ++ fieldWord (Fin.cons (v 0) (Fin.tail (Fin.tail v)))

private def emitFields (clock : List Bool) (v : Fin 5 → List Bool) : List Bool :=
  recNotation (fun _ : Fin 5 → List Bool => []) emitStep emitStep clock v

private theorem emitFields_length (clock : List Bool) (v : Fin 5 → List Bool) :
    (emitFields clock v).length = clock.length * (generalWidthRuler (v 0)).length := by
  induction clock with
  | nil => simp [emitFields, recNotation]
  | cons b r ih =>
    simp only [emitFields, recNotation_cons, Bool.cond_self]
    change (emitFields r v ++ fieldWord (Fin.cons r v)).length = _
    rw [List.length_append, ih]
    simp [fieldWord, padTo_length, Nat.add_mul, Nat.add_comm]

/-- Emit the existing certificate layout. Arguments are instance, raw membership,
determinant, row-major dictionary coefficients, and arithmetic field width. -/
def generalBimatrixEndpointMachineWord (v : Fin 5 → List Bool) : List Bool :=
  emitFields (List.replicate 6 false ++ generalBimatrixDimensionWord (v 0)) v

@[simp] theorem generalBimatrixEndpointMachineWord_length (v : Fin 5 → List Bool) :
    (generalBimatrixEndpointMachineWord v).length =
      (6 + generalRowCount (v 0) + generalColCount (v 0)) *
        generalCertificateWidth (v 0).length := by
  rw [generalBimatrixEndpointMachineWord, emitFields_length]
  simp only [List.length_append, List.length_replicate, generalWidthRuler_length,
    generalBimatrixDimensionWord_length]
  congr 1
  omega

theorem generalBimatrixEndpointMachineWord_cobham : Cobham generalBimatrixEndpointMachineWord := by
  have hs : Cobham emitStep := Cobham.appendFn (.proj 1)
    (Cobham.comp fieldWord_cobham fun i =>
      Fin.cases (.proj 0) (fun j => .proj j.succ.succ) i)
  have hb : Cobham fun v : Fin 6 → List Bool => smash (v 0) (generalWidthRuler (v 1)) :=
    Cobham.comp₂ Cobham.smash (.proj 0)
      (Cobham.comp generalWidthRuler_cobham fun _ => .proj 1)
  have he : Cobham fun v : Fin 6 → List Bool => emitFields (v 0) (Fin.tail v) :=
    (Cobham.boundedRec Cobham.empty hs hs hb (fun r v => by
      change (emitFields r v).length ≤ (smash r (generalWidthRuler (v 0))).length
      rw [emitFields_length, smash_length])).of_eq fun _ => rfl
  have hc : Cobham fun v : Fin 5 → List Bool =>
      List.replicate 6 false ++ generalBimatrixDimensionWord (v 0) :=
    Cobham.appendFn (Cobham.const (List.replicate 6 false))
      (Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 0)
  let gs : Fin 6 → (Fin 5 → List Bool) → List Bool := fun i v =>
    ![List.replicate 6 false ++ generalBimatrixDimensionWord (v 0), v 0, v 1, v 2, v 3, v 4] i
  have hg : ∀ i, Cobham (gs i) := by
    intro i
    fin_cases i
    · exact hc
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
    · exact .proj 3
    · exact .proj 4
  exact (Cobham.comp (gs := gs) he hg).of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl

theorem generalBimatrixEndpointMachineWord_mem_FPn : FPn generalBimatrixEndpointMachineWord :=
  cobham_iff_FPn.mp generalBimatrixEndpointMachineWord_cobham

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec GameTheory.Math

theorem generalBimatrixEndpointWeightWord_integer (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width r : List Bool) (label : Fin (generalRowCount input + generalColCount input))
    (hr : r.length = label.val)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i) :
    binarySignedValue (generalBimatrixEndpointWeightWord
      ![r, input, membershipWord basis.basic, det, coeff, width]) =
      basis.cramerWeight (toLex (label, true)) := by
  let v : BimatrixVariable (generalRowCount input) (generalColCount input) := toLex (label, true)
  have hi : (index v).val = 2 * label.val + 1 := rfl
  have hbit : ((membershipWord basis.basic)[(index v).val]?).getD false =
      decide (v ∈ basis.basic) := by
    simp only [membershipWord, List.getElem?_ofFn, (index v).isLt, ↓reduceDIte,
      Option.getD_some]
    have he : (⟨(index v).val, (index v).isLt⟩ : Fin (2 * (generalRowCount input + generalColCount input))) = index v := rfl
    rw [he, variableAt_index]
  rw [generalBimatrixEndpointWeightWord_value]
  change (if ((membershipWord basis.basic)[2 * r.length + 1]?).getD false then
    (binarySignedRowValue width coeff
      (((membershipWord basis.basic).take (2 * r.length + 1)).count true *
        (generalRowCount input + generalColCount input + 1))).toNat else 0 : ℕ) = (basis.cramerWeight (toLex (label, true)) : ℤ)
  norm_cast
  rw [hr, ← hi, hbit]
  by_cases hv : v ∈ basis.basic
  · simp only [hv, decide_true, ↓reduceIte]
    rw [membershipWord_prefix_count,
      FiniteSetRank.rank_eq_index basis.basic basis.cardinality v hv, hf]
    change _ = basis.cramerWeight v
    rw [BimatrixBasis.cramerWeight, dite_eq_left hv]
    rfl
  · change _ = basis.cramerWeight v
    simp [BimatrixBasis.cramerWeight, hv]
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham GameTheory.Finite

/-- Emit one of the six scalar certificate fields at its indexed position. -/
def generalBimatrixEndpointCertificateFieldWord (v : Fin 6 → List Bool) : List Bool :=
  fieldSignedWord 6 v

private theorem positive_magnitude (x : List Bool) :
    Nat.fromBitsLE (endpointPositiveWord x).tail = (binarySignedValue x).toNat := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> simp [endpointPositiveWord, bitAt, caseBit₀,
      binarySignedValue, Nat.fromBitsLE, Nat.fromBits]

private theorem fieldWord_eq_bits (v : Fin 6 → List Bool) (n : ℕ)
    (h : (binarySignedValue (generalBimatrixEndpointCertificateFieldWord v)).toNat = n) :
    fieldWord v = Nat.toBitsLE (generalCertificateWidth (v 1).length) n := by
  apply Nat.fromBitsLE_inj_of_length_eq
  · simp [fieldWord, padTo_length, generalWidthRuler_length]
  · rw [fieldWord, padTo_fromBitsLE, positive_magnitude, ← h,
      Nat.fromBitsLE_toBitsLE_mod, generalWidthRuler_length]
    rfl

private theorem encodeGeneralFields_snoc (W k : ℕ) (f : ℕ → ℕ) :
    encodeGeneralFields W (k + 1) f =
      encodeGeneralFields W k f ++ Nat.toBitsLE W (f k) := by
  induction k generalizing f with
  | zero => simp [encodeGeneralFields]
  | succ k ih =>
    change Nat.toBitsLE W (f 0) ++ encodeGeneralFields W (k + 1) (fun i => f (i + 1)) = _
    rw [ih, encodeGeneralFields]
    simp only [List.append_assoc]

private theorem emitFields_encode (clock : List Bool) (v : Fin 5 → List Bool)
    (f : ℕ → ℕ)
    (hf : ∀ r : List Bool, r.length < clock.length →
      (binarySignedValue (generalBimatrixEndpointCertificateFieldWord (Fin.cons r v))).toNat =
        f r.length) :
    emitFields clock v = encodeGeneralFields (generalCertificateWidth (v 0).length) clock.length f := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [emitFields, recNotation_cons, Bool.cond_self]
    change emitFields r v ++ fieldWord (Fin.cons r v) = _
    rw [ih (fun x hx => hf x (by simp; omega)), fieldWord_eq_bits _ _ (hf r (by simp))]
    exact (encodeGeneralFields_snoc _ _ _).symm

theorem generalBimatrixEndpointMachineWord_eq_encode (v : Fin 5 → List Bool)
    (c : BimatrixCertificate (generalRowCount (v 0)) (generalColCount (v 0)))
    (hf : ∀ r : List Bool, r.length < 6 + generalRowCount (v 0) + generalColCount (v 0) →
      (binarySignedValue (generalBimatrixEndpointCertificateFieldWord (Fin.cons r v))).toNat =
        generalCertificateField c r.length) :
    generalBimatrixEndpointMachineWord v =
      encodeGeneralCertificate (generalCertificateWidth (v 0).length) c := by
  rw [generalBimatrixEndpointMachineWord, emitFields_encode _ v (generalCertificateField c)]
  · simp only [List.length_append, List.length_replicate, generalBimatrixDimensionWord_length,
      encodeGeneralCertificate, Nat.add_assoc]
  · intro r hr
    apply hf r
    simpa only [List.length_append, List.length_replicate, generalBimatrixDimensionWord_length,
      Nat.add_assoc] using hr
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

theorem generalBimatrixEndpointMassWord_value (columnPlayer : Bool) (v : Fin 5 → List Bool)
    (hw : 0 < (v 4).length)
    (hp : ∀ t ≤ (generalActionRuler columnPlayer (v 0)).length,
      (∑ i ∈ Finset.range t, binarySignedValue (generalBimatrixEndpointMassTermWord columnPlayer
        (Fin.cons (List.replicate i false) v))).natAbs < 2 ^ ((v 4).length - 1)) :
    binarySignedValue (generalBimatrixEndpointMassWord columnPlayer v) =
      ∑ i ∈ Finset.range (generalActionRuler columnPlayer (v 0)).length,
        binarySignedValue (generalBimatrixEndpointMassTermWord columnPlayer (Fin.cons (List.replicate i false) v)) := by
  apply binarySignedSum_value _ _ _ _ _ hw _ hp
  intro r
  have hc (x y : List Bool) (hxy : x.length = y.length) :
      binarySignedValue (generalBimatrixEndpointWeightWord
        ![x, v 0, v 1, v 2, v 3, v 4]) =
      binarySignedValue (generalBimatrixEndpointWeightWord
        ![y, v 0, v 1, v 2, v 3, v 4]) := by
    rw [generalBimatrixEndpointWeightWord_value, generalBimatrixEndpointWeightWord_value]
    let f : ℕ → ℕ := fun l => if ((v 1)[2 * l + 1]?).getD false then
      (binarySignedRowValue (v 4) (v 3)
        (((v 1).take (2 * l + 1)).count true *
          (generalRowCount (v 0) + generalColCount (v 0) + 1))).toNat else 0
    change (f x.length : ℤ) = (f y.length : ℤ)
    rw [hxy]
  cases columnPlayer
  · exact hc r (List.replicate r.length false) (List.length_replicate ..).symm
  · apply hc (generalRowRuler (v 0) ++ r)
      (generalRowRuler (v 0) ++ List.replicate r.length false)
    simp only [List.length_append, List.length_replicate]

theorem generalBimatrixEndpointUtilityWord_value (columnPlayer : Bool) (v : Fin 5 → List Bool)
    (hw : 0 < (v 4).length)
    (hp : ((binarySignedValue (v 2)).natAbs -
      ((2 : ℤ) ^ generalCoefficientBits (v 0) + 1) *
        binarySignedValue (generalBimatrixEndpointMassWord (!columnPlayer) v) : ℤ).natAbs <
        2 ^ ((v 4).length - 1)) :
    binarySignedValue (generalBimatrixEndpointUtilityWord columnPlayer v) =
      ((binarySignedValue (v 2)).natAbs : ℤ) -
        ((2 : ℤ) ^ generalCoefficientBits (v 0) + 1) *
          binarySignedValue (generalBimatrixEndpointMassWord (!columnPlayer) v) := by
  have ha : binarySignedValue ([false] ++ (v 2).tail) =
      ((binarySignedValue (v 2)).natAbs : ℤ) := by
    rw [binarySignedValue_natAbs]
    rfl
  have hm := binarySignedMul_value (generalPositiveShiftWord (v 0))
    (generalBimatrixEndpointMassWord (!columnPlayer) v)
  rw [generalPositiveShiftWord_value] at hm
  rw [generalBimatrixEndpointUtilityWord, binarySignedFixedSub_value _ _ _ hw]
  · rw [ha, hm]
  · simpa only [ha, hm] using hp
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham GameTheory.Finite GameTheory.Math
open scoped BigOperators

theorem generalBimatrixEndpointMassWord_integer (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width : List Bool) (player : Bool)
    (hw : 0 < width.length)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i)
    (hp : ∀ t ≤ (generalActionRuler player input).length,
      (∑ i ∈ Finset.range t, binarySignedValue (generalBimatrixEndpointMassTermWord player
        (Fin.cons (List.replicate i false) ![input, BimatrixPathBinaryCodec.membershipWord basis.basic,
          det, coeff, width]))).natAbs < 2 ^ (width.length - 1)) :
    binarySignedValue (generalBimatrixEndpointMassWord player
      ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width]) =
      (bif player then (basis.cramerCertificate 0 0).colDenominator
        else (basis.cramerCertificate 0 0).rowDenominator : ℤ) := by
  rw [generalBimatrixEndpointMassWord_value player _ hw hp]
  cases player
  · change (∑ i ∈ Finset.range (generalRowCount input), binarySignedValue
      (generalBimatrixEndpointMassTermWord false (Fin.cons (List.replicate i false)
        ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width]))) =
      ((∑ i : Fin (generalRowCount input),
        basis.cramerWeight (toLex (finSumFinEquiv (.inl i), true))) : ℕ)
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact generalBimatrixEndpointWeightWord_integer input basis det coeff width
      (List.replicate i.val false) (finSumFinEquiv (.inl i)) (by simp) hf
  · change (∑ i ∈ Finset.range (generalColCount input), binarySignedValue
      (generalBimatrixEndpointMassTermWord true (Fin.cons (List.replicate i false)
        ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width]))) =
      ((∑ i : Fin (generalColCount input),
        basis.cramerWeight (toLex (finSumFinEquiv (.inr i), true))) : ℕ)
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    exact generalBimatrixEndpointWeightWord_integer input basis det coeff width
      (generalRowRuler input ++ List.replicate i.val false) (finSumFinEquiv (.inr i))
      (by rw [List.length_append, List.length_replicate]; rfl) hf
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem lenEqWord (x y : List Bool) :
    lenEqFlag x y = [decide (x.length = y.length)] := by
  rcases lenEqFlag_flag x y with h | h
  · have hh := (lenEqFlag_eq_true_iff x y).mp h
    simp [h, hh]
  · have hh : x.length ≠ y.length := by
      intro hn
      have ht := (lenEqFlag_eq_true_iff x y).mpr hn
      simp [h] at ht
    simp [h, hh]

theorem generalBimatrixEndpointCertificateFieldWord_eq (r : List Bool) (v : Fin 5 → List Bool) :
    generalBimatrixEndpointCertificateFieldWord (Fin.cons r v) =
      if r.length = 5 then binarySignedNeg (generalBimatrixEndpointUtilityWord true v) else
      if r.length = 4 then generalBimatrixEndpointUtilityWord true v else
      if r.length = 3 then binarySignedNeg (generalBimatrixEndpointUtilityWord false v) else
      if r.length = 2 then generalBimatrixEndpointUtilityWord false v else
      if r.length = 1 then generalBimatrixEndpointMassWord true v else
      if r.length = 0 then generalBimatrixEndpointMassWord false v else
      generalBimatrixEndpointWeightWord ![r.drop 6, v 0, v 1, v 2, v 3, v 4] := by
  simp only [generalBimatrixEndpointCertificateFieldWord, fieldSignedWord, Fin.cons_zero,
    lenEqWord, List.length_replicate, Fin.tail_cons, scalarWord]
  split_ifs <;> simp_all [caseBit₀]
  rfl
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open GameTheory.Finite

private theorem cramer_field_weight {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    (basis : BimatrixBasis A B) (a b : ℤ) (label : Fin (m + n)) :
    generalCertificateField (basis.cramerCertificate a b) (6 + label.val) =
      basis.cramerWeight (toLex (label, true)) := by
  unfold generalCertificateField
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · dsimp only [BimatrixBasis.cramerCertificate, BimatrixCertificate.shiftPayoffs,
      complementaryNashCertificate]
    congr 1
    congr 1
    congr 1
    apply Fin.ext
    simp only [finSumFinEquiv_apply_left, Fin.castAdd_mk, Fin.val_mk]
    omega
  · split
    · dsimp only [BimatrixBasis.cramerCertificate, BimatrixCertificate.shiftPayoffs,
        complementaryNashCertificate]
      congr 1
      congr 1
      congr 1
      apply Fin.ext
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
      omega
    · have hi := label.isLt
      omega
end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham GameTheory.Finite GameTheory.Math
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem generalBimatrixEndpointMachineWord_eq_endpoint (input : List Bool) (basis : GeneralBimatrixShiftedBasis input)
    (det coeff width : List Bool) (hw : 0 < width.length)
    (hd : binarySignedValue det = IntegerCramerComputation.determinant basis.integerMatrix)
    (hf : ∀ i, binarySignedRowValue width coeff
      (i.val * (generalRowCount input + generalColCount input + 1)) =
      IntegerCramerComputation.signedNumerator basis.integerMatrix (fun _ => 1) i)
    (hp : ∀ player, ∀ t ≤ (generalActionRuler player input).length,
      (∑ i ∈ Finset.range t, binarySignedValue (generalBimatrixEndpointMassTermWord player
        (Fin.cons (List.replicate i false) ![input, BimatrixPathBinaryCodec.membershipWord basis.basic,
          det, coeff, width]))).natAbs < 2 ^ (width.length - 1))
    (hu : ∀ player,
      ((binarySignedValue det).natAbs - ((2 : ℤ) ^ generalCoefficientBits input + 1) *
        binarySignedValue (generalBimatrixEndpointMassWord (!player)
          ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width]) : ℤ).natAbs <
          2 ^ (width.length - 1)) :
    generalBimatrixEndpointMachineWord
      ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width] =
      generalBimatrixEndpointWord input basis := by
  let v : Fin 5 → List Bool :=
    ![input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width]
  let shift : ℤ := (2 : ℤ) ^ generalCoefficientBits input + 1
  let c := basis.cramerCertificate shift shift
  have hm (player : Bool) : binarySignedValue (generalBimatrixEndpointMassWord player v) =
      (bif player then c.colDenominator else c.rowDenominator : ℤ) :=
    generalBimatrixEndpointMassWord_integer input basis det coeff width player hw hf (hp player)
  have hv (player : Bool) : binarySignedValue (generalBimatrixEndpointUtilityWord player v) =
      (bif player then c.colUtilityNumerator else c.rowUtilityNumerator) := by
    rw [generalBimatrixEndpointUtilityWord_value player v hw (hu player)]
    change ((binarySignedValue det).natAbs : ℤ) - shift *
      binarySignedValue (generalBimatrixEndpointMassWord (!player) v) = _
    rw [hm, hd]
    cases player <;> simp [c, BimatrixBasis.cramerCertificate, complementaryNashCertificate,
      BimatrixCertificate.shiftPayoffs, IntegerCramerComputation.denominator, sub_eq_add_neg]
  apply generalBimatrixEndpointMachineWord_eq_encode v c
  intro r hr
  rw [generalBimatrixEndpointCertificateFieldWord_eq r v]
  by_cases hs : r.length < 6
  · have cases : r.length = 0 ∨ r.length = 1 ∨ r.length = 2 ∨
      r.length = 3 ∨ r.length = 4 ∨ r.length = 5 := by omega
    rcases cases with h | h | h | h | h | h
    all_goals simp only [h]; norm_num only
    all_goals simp [binarySignedNeg_value, hm, hv, generalCertificateField]
  · have h0 : r.length ≠ 0 := by omega
    have h1 : r.length ≠ 1 := by omega
    have h2 : r.length ≠ 2 := by omega
    have h3 : r.length ≠ 3 := by omega
    have h4 : r.length ≠ 4 := by omega
    have h5 : r.length ≠ 5 := by omega
    simp only [h0, h1, h2, h3, h4, h5, ↓reduceIte]
    have hl : r.length - 6 < generalRowCount input + generalColCount input := by
      change r.length < 6 + generalRowCount input + generalColCount input at hr
      omega
    let label : Fin (generalRowCount input + generalColCount input) := ⟨r.length - 6, hl⟩
    have he : r.length = 6 + label.val := by dsimp [label]; omega
    change (binarySignedValue (generalBimatrixEndpointWeightWord
      ![r.drop 6, input, BimatrixPathBinaryCodec.membershipWord basis.basic, det, coeff, width])).toNat =
      generalCertificateField c r.length
    rw [generalBimatrixEndpointWeightWord_integer input basis det coeff width
      (r.drop 6) label (by simp [label]) hf]
    simp only [Int.toNat_natCast]
    rw [he]
    exact (cramer_field_weight basis shift shift label).symm
end GameTheory.Complexity.Backend
