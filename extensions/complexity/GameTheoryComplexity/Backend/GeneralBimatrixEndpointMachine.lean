module

public import GameTheoryComplexity.Backend.GeneralBimatrixMatrixWord
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifier
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
public import GameTheoryComplexity.Backend.GeneralBimatrixSignedInput
public import GameTheoryComplexity.Backend.GeneralBimatrixDictionary
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.BinarySignedFixedWidth

@[expose] public section

/-! Binary emission of the certificate at a supplied complementary basis.
The input contains the already computed determinant and packed dictionary.
All loops use explicitly represented dimension and field-width rulers. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open scoped BigOperators

/-- Clamp a signed word to its nonnegative part, retaining a signed header. -/
def endpointPositiveWord (x : List Bool) : List Bool :=
  if x.headD false then [false] else [false] ++ x.tail

theorem endpointPositiveWord_value (x : List Bool) :
    binarySignedValue (endpointPositiveWord x) = (binarySignedValue x).toNat := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> simp [endpointPositiveWord, binarySignedValue, ofBits]

@[fun_prop] theorem endpointPositiveWord_polyTime :
    ComputableInPolyTime endpointPositiveWord encBits encBits := by
  have hhead : ComputableInPolyTime (fun x : List Bool => x.headD false) encBits encBool :=
    .headD false
  have htail : ComputableInPolyTime (fun x : List Bool => x.tail) encBits encBits :=
    ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail
  exact ComputableInPolyTime.ite_decide hhead (.const [false])
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false) htail)

/-- A payoff coordinate from the supplied packed dictionary. Arguments are
ambient label ruler, instance, raw membership, determinant, coefficients, width. -/
def generalBimatrixEndpointWeightWord (v : Fin 6 → List Bool) : List Bool :=
  let position := v 0 ++ v 0 ++ [false]
  let ordinal := binarySubsetTally ((v 2).take position.length)
  let stride := generalBimatrixDimensionWord (v 1) ++ [false]
  if (v 2)[position.length]?.getD false then
    endpointPositiveWord (binarySignedRowField
      ![List.replicate (ordinal.length * stride.length) true, v 5, v 4])
  else [false]

@[fun_prop] theorem generalBimatrixEndpointWeightWord_polyTime :
    ComputableInPolyTime generalBimatrixEndpointWeightWord (encPi encBits) encBits := by
  have hr := ComputableInPolyTime.pi_apply encBits (0 : Fin 6)
  have hi := ComputableInPolyTime.pi_apply encBits (1 : Fin 6)
  have hm := ComputableInPolyTime.pi_apply encBits (2 : Fin 6)
  have hcoeff := ComputableInPolyTime.pi_apply encBits (4 : Fin 6)
  have hwidth := ComputableInPolyTime.pi_apply encBits (5 : Fin 6)
  have hposition : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => v 0 ++ v 0 ++ [false])
      (encPi encBits) encBits :=
    ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend hr hr) (.const [false])
  have hpositionLen := ComputableInPolyTime.length_bits_comp hposition
  have hprefix := hm.bitsTakeWithInput hpositionLen
  have hord := binarySubsetTally_polyTime hprefix
  have hordLen := ComputableInPolyTime.length_bits_comp hord
  have hdimensionArgs : ComputableInPolyTime (fun v : Fin 6 → List Bool => ![v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact hi
  have hdimension := generalBimatrixDimensionWord_polyTime.comp hdimensionArgs
  have hstride := ComputableInPolyTime.bitsAppend hdimension (.const [false])
  have hstrideLen := ComputableInPolyTime.length_bits_comp hstride
  have hsmashLen := ComputableInPolyTime.unary_mul' hordLen hstrideLen
  have hsmash := ComputableInPolyTime.bitsReplicate true |>.comp hsmashLen
  have hrowArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool =>
        ![List.replicate ((binarySubsetTally ((v 2).take (v 0 ++ v 0 ++ [false]).length)).length *
          (generalBimatrixDimensionWord (v 1) ++ [false]).length) true, v 5, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsmash
    · exact hwidth
    · exact hcoeff
  have hrow := binarySignedRowField_polyTime.comp hrowArgs
  have hpositive := endpointPositiveWord_polyTime.comp hrow
  have hflagWord := indexedFlag_polyTime.comp (hpositionLen.prod hm)
  have hflag : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ((v 2)[(v 0 ++ v 0 ++ [false]).length]?.getD false))
      (encPi encBits) encBool := (ComputableInPolyTime.headD false).comp hflagWord
  exact ComputableInPolyTime.ite_decide hflag hpositive (.const [false])

theorem generalBimatrixEndpointWeightWord_value (v : Fin 6 → List Bool) :
    binarySignedValue (generalBimatrixEndpointWeightWord v) =
      if ((v 2)[2 * (v 0).length + 1]?).getD false then
        (binarySignedRowValue (v 5) (v 4)
          (((v 2).take (2 * (v 0).length + 1)).count true *
            (generalRowCount (v 1) + generalColCount (v 1) + 1))).toNat
      else 0 := by
  change binarySignedValue
      (if (v 2)[(v 0 ++ v 0 ++ [false]).length]?.getD false then
        endpointPositiveWord
          (binarySignedRowField
            ![List.replicate
                ((binarySubsetTally ((v 2).take (v 0 ++ v 0 ++ [false]).length)).length *
                  (generalBimatrixDimensionWord (v 1) ++ [false]).length) true,
              v 5, v 4])
        else [false]) = _
  simp only [List.length_append, List.length_singleton]
  have hpos : (v 0).length + (v 0).length + 1 = 2 * (v 0).length + 1 := by omega
  rw [hpos]
  by_cases hbit : (v 2)[2 * (v 0).length + 1]?.getD false = true
  · simp only [hbit, ite_true]
    rw [endpointPositiveWord_value]
    simp only [binarySignedRowField, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, List.length_replicate, binarySubsetTally_length,
      generalBimatrixDimensionWord_length,
      binarySignedRowValue]
    rfl
  · simp [hbit, binarySignedValue, ofBits]

/-- Recover one player's indexed probability weight for the mass summation loop. -/
def generalBimatrixEndpointMassTermWord (columnPlayer : Bool) (v : Fin 6 → List Bool) : List Bool :=
  generalBimatrixEndpointWeightWord ![
    (bif columnPlayer then generalRowRuler (v 1) ++ v 0 else v 0),
    v 1, v 2, v 3, v 4, v 5]

private theorem massTerm_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalBimatrixEndpointMassTermWord columnPlayer)
      (encPi encBits) encBits := by
  have h0 := ComputableInPolyTime.pi_apply encBits (0 : Fin 6)
  have h1 := ComputableInPolyTime.pi_apply encBits (1 : Fin 6)
  have h2 := ComputableInPolyTime.pi_apply encBits (2 : Fin 6)
  have h3 := ComputableInPolyTime.pi_apply encBits (3 : Fin 6)
  have h4 := ComputableInPolyTime.pi_apply encBits (4 : Fin 6)
  have h5 := ComputableInPolyTime.pi_apply encBits (5 : Fin 6)
  have hfirst : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => bif columnPlayer then
        generalRowRuler (v 1) ++ v 0 else v 0) (encPi encBits) encBits := by
    cases columnPlayer
    · exact h0
    · have hargs : ComputableInPolyTime (fun v : Fin 6 → List Bool => ![v 1])
          (encPi encBits) (encPi encBits) := by
        apply ComputableInPolyTime.pi
        intro i
        fin_cases i
        exact h1
      have hrow := generalRowRuler_polyTime.comp hargs
      exact ComputableInPolyTime.bitsAppend hrow h0
  have hargs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool =>
        ![bif columnPlayer then generalRowRuler (v 1) ++ v 0 else v 0,
          v 1, v 2, v 3, v 4, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hfirst
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  exact generalBimatrixEndpointWeightWord_polyTime.comp hargs

/-- Sum one player's Cramer weights at the supplied arithmetic width.
Arguments are instance, membership, determinant, coefficients and width. -/
def generalBimatrixEndpointMassWord (columnPlayer : Bool) (v : Fin 5 → List Bool) : List Bool :=
  binarySignedSum (generalBimatrixEndpointMassTermWord columnPlayer)
    (generalActionRuler columnPlayer (v 0)) (v 4) v

@[fun_prop] theorem generalBimatrixEndpointMassWord_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalBimatrixEndpointMassWord columnPlayer)
      (encPi encBits) encBits := by
  have hinput := ComputableInPolyTime.pi_apply encBits (0 : Fin 5)
  have hclockArgs : ComputableInPolyTime (fun v : Fin 5 → List Bool => ![v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact hinput
  have hclock := (generalActionRuler_polyTime columnPlayer).comp hclockArgs
  have hwidth := ComputableInPolyTime.pi_apply encBits (4 : Fin 5)
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        ![generalActionRuler columnPlayer (v 0), v 4,
          v 0, v 1, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact hwidth
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
    · exact .pi_apply encBits 4
  have hsum : ComputableInPolyTime
      (fun u : Fin 7 → List Bool =>
        binarySignedSum (generalBimatrixEndpointMassTermWord columnPlayer)
          (u 0) (u 1) (Fin.tail (Fin.tail u)))
      (encPi encBits) encBits :=
    binarySignedSum_polyTime (p := 5)
      (term := generalBimatrixEndpointMassTermWord columnPlayer)
      (massTerm_polyTime columnPlayer)
  have hcert := hsum.comp hargs
  exact hcert.of_enc_eq (fun _ => rfl)

/-- Undo the payoff shift using the opposite player's mass. -/
def generalBimatrixEndpointUtilityWord (columnPlayer : Bool) (v : Fin 5 → List Bool) : List Bool :=
  binarySignedFixedSub (v 4) ([false] ++ (v 2).tail)
    (binarySignedMul (generalPositiveShiftWord (v 0))
      (generalBimatrixEndpointMassWord (!columnPlayer) v))

@[fun_prop] theorem generalBimatrixEndpointUtilityWord_polyTime (columnPlayer : Bool) :
    ComputableInPolyTime (generalBimatrixEndpointUtilityWord columnPlayer)
      (encPi encBits) encBits := by
  have h0 := ComputableInPolyTime.pi_apply encBits (0 : Fin 5)
  have h2 := ComputableInPolyTime.pi_apply encBits (2 : Fin 5)
  have h4 := ComputableInPolyTime.pi_apply encBits (4 : Fin 5)
  have hshiftArgs : ComputableInPolyTime (fun v : Fin 5 → List Bool => ![v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact h0
  have hshift := (generalPositiveShiftWord_polyTime).comp hshiftArgs
  have hmass := generalBimatrixEndpointMassWord_polyTime (!columnPlayer)
  have hproduct := binarySignedMul_polyTime hshift hmass
  have hraw : ComputableInPolyTime (fun v : Fin 5 → List Bool => [false] ++ (v 2).tail)
      (encPi encBits) encBits :=
    ComputableInPolyTime.bitsAppend (.const [false])
      ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp h2)
  exact binarySignedFixedSub_polyTime h4 hraw hproduct

def scalarWord : ℕ → (Fin 5 → List Bool) → List Bool
  | 0, v => generalBimatrixEndpointMassWord false v
  | 1, v => generalBimatrixEndpointMassWord true v
  | 2, v => generalBimatrixEndpointUtilityWord false v
  | 3, v => binarySignedNeg (generalBimatrixEndpointUtilityWord false v)
  | 4, v => generalBimatrixEndpointUtilityWord true v
  | 5, v => binarySignedNeg (generalBimatrixEndpointUtilityWord true v)
  | _, _ => [false]

private theorem scalarWord_polyTime (n : ℕ) :
    ComputableInPolyTime (scalarWord n) (encPi encBits) encBits := by
  rcases n with _ | n
  · exact generalBimatrixEndpointMassWord_polyTime false
  rcases n with _ | n
  · exact generalBimatrixEndpointMassWord_polyTime true
  rcases n with _ | n
  · exact generalBimatrixEndpointUtilityWord_polyTime false
  rcases n with _ | n
  · exact binarySignedNeg_polyTime (generalBimatrixEndpointUtilityWord_polyTime false)
  rcases n with _ | n
  · exact generalBimatrixEndpointUtilityWord_polyTime true
  rcases n with _ | n
  · exact binarySignedNeg_polyTime (generalBimatrixEndpointUtilityWord_polyTime true)
  exact .const [false]

def fieldSignedWord : ℕ → (Fin 6 → List Bool) → List Bool
  | 0, v => generalBimatrixEndpointWeightWord
      ![(v 0).drop 6, v 1, v 2, v 3, v 4, v 5]
  | n + 1, v => if (v 0).length = n then scalarWord n (Fin.tail v) else fieldSignedWord n v

private theorem fieldSignedWord_polyTime (n : ℕ) :
    ComputableInPolyTime (fieldSignedWord n) (encPi encBits) encBits := by
  induction n with
  | zero =>
    have hargs : ComputableInPolyTime
        (fun v : Fin 6 → List Bool =>
          ![(v 0).drop 6, v 1, v 2, v 3, v 4, v 5])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact (ComputableInPolyTime.pi_apply encBits (0 : Fin 6)).bitsDropWithInput (.const 6)
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 2
      · exact .pi_apply encBits 3
      · exact .pi_apply encBits 4
      · exact .pi_apply encBits 5
    exact generalBimatrixEndpointWeightWord_polyTime.comp hargs
  | succ n ih =>
    have hruler := ComputableInPolyTime.pi_apply encBits (0 : Fin 6)
    have hlen := ComputableInPolyTime.length_bits_comp hruler
    have hcondition := ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
        (hlen.tidy.prod (.const n)))
    have htail : ComputableInPolyTime (fun v : Fin 6 → List Bool => Fin.tail v)
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      exact .pi_apply encBits i.succ
    have hscalar := (scalarWord_polyTime n).comp htail
    exact ComputableInPolyTime.of_tidy
      (.ite_decide hcondition.tidy hscalar.tidy ih.tidy)

def fieldWord (v : Fin 6 → List Bool) : List Bool :=
  lowBits (generalWidthRuler (v 1)).length
    (ofBits (endpointPositiveWord (fieldSignedWord 6 v)).tail)

@[simp] private theorem fieldWord_length (v : Fin 6 → List Bool) :
    (fieldWord v).length = (generalWidthRuler (v 1)).length := by
  simp [fieldWord]

private theorem fieldWord_polyTime :
    ComputableInPolyTime fieldWord (encPi encBits) encBits := by
  have hinstance := ComputableInPolyTime.pi_apply encBits (1 : Fin 6)
  have hwidth := generalWidthRuler_polyTime.comp hinstance
  have hwidthLen := ComputableInPolyTime.length_bits_comp hwidth
  have hsigned := fieldSignedWord_polyTime 6
  have hpositive := endpointPositiveWord_polyTime.comp hsigned
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hpositive
  have hvalue := ComputableInPolyTime.bitsToNat.comp htail
  exact ComputableInPolyTime.bitsLow hwidthLen hvalue

private def emitFieldsStep (context : Fin 5 → List Bool) (suffix state : List Bool)
    (_bit : Bool) : List Bool :=
  state ++ fieldWord (Fin.cons suffix context)

def emitFields (clock : List Bool) (v : Fin 5 → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun (context : Fin 5 → List Bool) (suffix state : List Bool) (_bit : Bool) =>
      state ++ fieldWord (Fin.cons suffix context)) v [] clock

private theorem emitFields_length (clock : List Bool) (v : Fin 5 → List Bool) :
    (emitFields clock v).length = clock.length * (generalWidthRuler (v 0)).length := by
  induction clock with
  | nil => simp [emitFields]
  | cons b r ih =>
    rw [emitFields, WordFold.suffixFold_cons]
    change (emitFields r v ++ fieldWord (Fin.cons r v)).length = _
    rw [List.length_append, ih, fieldWord_length]
    simp only [List.length_cons]
    have hfield : (Fin.cons r v : Fin 6 → List Bool) 1 = v 0 := rfl
    rw [hfield]
    rw [Nat.succ_mul]

private theorem emitFieldsStep_polyTime :
    ComputableInPolyTime
      (fun p : ((Fin 5 → List Bool) × (List Bool × List Bool)) × Bool =>
        emitFieldsStep p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let outerEncoding : ((Fin 5 → List Bool) × (List Bool × List Bool)) ↪ List Bool :=
    encPair (encPi encBits) (encPair encBits encBits)
  have houter : ComputableInPolyTime
      (fun p : (((Fin 5 → List Bool) × (List Bool × List Bool)) × Bool) => p.1)
      (encPair outerEncoding encBool) outerEncoding :=
    .fst outerEncoding encBool
  have hcontext :=
    (ComputableInPolyTime.fst (encPi encBits) (encPair encBits encBits)).comp houter
  have hstatePair :=
    (ComputableInPolyTime.snd (encPi encBits) (encPair encBits encBits)).comp houter
  have hsuffix := (ComputableInPolyTime.fst encBits encBits).comp hstatePair
  have hacc := (ComputableInPolyTime.snd encBits encBits).comp hstatePair
  have hfieldArgs : ComputableInPolyTime
      (fun p : ((Fin 5 → List Bool) × (List Bool × List Bool)) × Bool =>
        Fin.cons p.1.2.1 p.1.1)
      (encPair outerEncoding encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsuffix
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hcontext
  exact ComputableInPolyTime.bitsAppend hacc (fieldWord_polyTime.comp hfieldArgs)

private theorem emitFields_polyTime :
    ComputableInPolyTime
      (fun v : Fin 6 → List Bool => emitFields (v 0) (Fin.tail v))
      (encPi encBits) encBits := by
  have hcontext : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => Fin.tail v) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact .pi_apply encBits i.succ
  have hclock : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => v 0) (encPi encBits) encBits :=
    .pi_apply encBits 0
  have hwidth := generalWidthRuler_polyTime.comp (.pi_apply encBits (1 : Fin 6))
  have hbound := hclock.polyBounded_length.mul hwidth.polyBounded_length
  exact WordFold.suffixFold_polyTime hcontext hclock (.const []) emitFieldsStep_polyTime hbound
    (fun v suffix hsuffix => by
      change (emitFields suffix (Fin.tail v)).length ≤
        (v 0).length * (generalWidthRuler ((Fin.tail v) 0)).length
      rw [emitFields_length]
      exact Nat.mul_le_mul_right _ hsuffix.length_le)

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

@[fun_prop] theorem generalBimatrixEndpointMachineWord_polyTime :
    ComputableInPolyTime generalBimatrixEndpointMachineWord (encPi encBits) encBits := by
  have hclock : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        List.replicate 6 false ++ generalBimatrixDimensionWord (v 0))
      (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 5 → List Bool => ![v 0])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      exact .pi_apply encBits (0 : Fin 5)
    exact ComputableInPolyTime.bitsAppend (.const (List.replicate 6 false))
      (generalBimatrixDimensionWord_polyTime.comp hargs)
  have hargs : ComputableInPolyTime
      (fun v : Fin 5 → List Bool =>
        ![List.replicate 6 false ++ generalBimatrixDimensionWord (v 0),
          v 0, v 1, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact .pi_apply encBits (0 : Fin 5)
    · exact .pi_apply encBits (1 : Fin 5)
    · exact .pi_apply encBits (2 : Fin 5)
    · exact .pi_apply encBits (3 : Fin 5)
    · exact .pi_apply encBits (4 : Fin 5)
  have hcert := emitFields_polyTime.comp hargs
  exact hcert.of_enc_eq (fun _ => rfl)

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Finite

/-- Emit one of the six scalar certificate fields at its indexed position. -/
def generalBimatrixEndpointCertificateFieldWord (v : Fin 6 → List Bool) : List Bool :=
  fieldSignedWord 6 v

private theorem positive_magnitude (x : List Bool) :
    ofBits (endpointPositiveWord x).tail = (binarySignedValue x).toNat := by
  rw [← binarySignedValue_natAbs, endpointPositiveWord_value]
  apply Int.ofNat_inj.mp
  simp

private theorem fieldWord_eq_bits (v : Fin 6 → List Bool) (n : ℕ)
    (h : (binarySignedValue (generalBimatrixEndpointCertificateFieldWord v)).toNat = n) :
    fieldWord v = lowBits (generalCertificateWidth (v 1).length) n := by
  rw [fieldWord, positive_magnitude]
  rw [generalBimatrixEndpointCertificateFieldWord] at h
  rw [← h, generalWidthRuler_length]

private theorem encodeGeneralFields_snoc (W k : ℕ) (f : ℕ → ℕ) :
    encodeGeneralFields W (k + 1) f =
      encodeGeneralFields W k f ++ lowBits W (f k) := by
  induction k generalizing f with
  | zero => simp [encodeGeneralFields]
  | succ k ih =>
    change lowBits W (f 0) ++ encodeGeneralFields W (k + 1) (fun i => f (i + 1)) = _
    rw [ih (fun i => f (i + 1)), encodeGeneralFields]
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
    rw [emitFields, WordFold.suffixFold_cons]
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Finite GameTheory.Math
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

theorem generalBimatrixEndpointCertificateFieldWord_eq (r : List Bool) (v : Fin 5 → List Bool) :
    generalBimatrixEndpointCertificateFieldWord (Fin.cons r v) =
      if r.length = 5 then binarySignedNeg (generalBimatrixEndpointUtilityWord true v) else
      if r.length = 4 then generalBimatrixEndpointUtilityWord true v else
      if r.length = 3 then binarySignedNeg (generalBimatrixEndpointUtilityWord false v) else
      if r.length = 2 then generalBimatrixEndpointUtilityWord false v else
      if r.length = 1 then generalBimatrixEndpointMassWord true v else
      if r.length = 0 then generalBimatrixEndpointMassWord false v else
      generalBimatrixEndpointWeightWord ![r.drop 6, v 0, v 1, v 2, v 3, v 4] := by
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
open GameTheory.Finite GameTheory.Math
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
