module

public import GameTheoryComplexity.Backend.BimatrixProgramCorrectness
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierMachine
public import GameTheoryComplexity.Backend.BinaryRatioExtraction
public import GameTheoryComplexity.Backend.BrouwerReduction
public import GameTheory.Math.GridBrouwerBinaryCell
public import GameTheory.Math.ClippedArithmetic

@[expose] public section

/-! Bounded word extraction converts normalized Nash coordinate weights into
an exact dyadic triangle and emits its canonical rational barycenter. -/
namespace GameTheory.Complexity.Backend.BrouwerNashAnswerMachine
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Math GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- The common row denominator, read at the actual emitted-game certificate width. -/
def denominatorWord (tape answer : List Bool) : List Bool :=
  generalCertificateFieldWord ![[], BimatrixProgramMachine.instanceWord tape, answer]

/-- Scaled coordinate numerator for action one or three. -/
def numeratorWord (second : Bool) (tape answer : List Bool) : List Bool :=
  binaryWordMul (binaryLengthWord (BimatrixProgramCodec.dimension tape))
    (generalCertificateFieldWord ![List.replicate (if second then 9 else 7) true,
      BimatrixProgramMachine.instanceWord tape, answer])

/-- Ratio-prefix state, scanned by the source's dyadic precision ruler. -/
def coordinateState (second : Bool) (v : Fin 3 → List Bool) : List Bool :=
  BinaryRatioExtraction.state (numeratorWord second (v 1) (v 2))
    (denominatorWord (v 1) (v 2)) (CircuitWords.first (v 0))

/-- The containing dyadic triangle, including endpoint and rising-diagonal ties. -/
def triangleWord (v : Fin 3 → List Bool) : List Bool :=
  let x := coordinateState false v
  let y := coordinateState true v
  [true] ++ routingLTFlag (CircuitWords.rest x) (CircuitWords.rest y) ++ CircuitWords.first x ++ CircuitWords.first y

/-- Emit a canonical rational barycenter answer to the source Brouwer instance. -/
def answerWord (v : Fin 3 → List Bool) : List Bool :=
  brouwerBarycenter (v 0) (triangleWord v)

/-- Certificate-field extraction charges the full emitted game and supplied answer. -/
@[fun_prop] theorem denominatorWord_polyTime
    {Input : Type} {input : Input ↪ List Bool} {tape answer : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits)
    (ha : ComputableInPolyTime answer input encBits) :
    ComputableInPolyTime (fun a => denominatorWord (tape a) (answer a)) input encBits := by
  have hgame : ComputableInPolyTime
      (fun a => BimatrixProgramMachine.instanceWord (tape a)) input encBits :=
    BimatrixProgramMachine.instanceWord_polyTime ht
  have hargs : ComputableInPolyTime
      (fun a => ![[], BimatrixProgramMachine.instanceWord (tape a), answer a])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · change ComputableInPolyTime (fun _ : Input => ([] : List Bool)) input encBits
      exact .const []
    · change ComputableInPolyTime
        (fun a => BimatrixProgramMachine.instanceWord (tape a)) input encBits
      exact hgame
    · change ComputableInPolyTime answer input encBits
      exact ha
  have hcert := generalCertificateFieldWord_polyTime.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro a
  simp only [denominatorWord, Function.comp_apply]

/-- Scaling the weight field charges the dimension and full certificate producers. -/
@[fun_prop] theorem numeratorWord_polyTime (second : Bool)
    {Input : Type} {input : Input ↪ List Bool} {tape answer : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits)
    (ha : ComputableInPolyTime answer input encBits) :
    ComputableInPolyTime (fun a => numeratorWord second (tape a) (answer a)) input encBits := by
  have hgame := BimatrixProgramMachine.instanceWord_polyTime ht
  have hargs : ComputableInPolyTime
      (fun a => ![List.replicate (if second then 9 else 7) true,
        BimatrixProgramMachine.instanceWord (tape a), answer a])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .const _
    · exact hgame
    · exact ha
  exact binaryWordMul_polyTime
    (binaryLengthWord_polyTime.comp (BimatrixProgramCodec.dimension_polyTime ht))
    (generalCertificateFieldWord_polyTime.comp hargs)

/-- Coordinate extraction charges the instance, answer and every precision bit. -/
@[fun_prop] theorem coordinateState_polyTime (second : Bool) :
    ComputableInPolyTime (coordinateState second) (encPi encBits) encBits := by
  exact BinaryRatioExtraction.state_polyTime
    (numeratorWord_polyTime second (.pi_apply encBits 1) (.pi_apply encBits 2))
    (denominatorWord_polyTime (.pi_apply encBits 1) (.pi_apply encBits 2))
    (CircuitWords.first_polyTime.comp (.pi_apply encBits 0))

/-- Triangle formation compares residual words and retains both full prefix words. -/
@[fun_prop] theorem triangleWord_polyTime :
    ComputableInPolyTime triangleWord (encPi encBits) encBits := by
  have hx := coordinateState_polyTime false
  have hy := coordinateState_polyTime true
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (.const [true])
        (routingLTFlag_polyTime (CircuitWords.rest_polyTime.comp hx)
          (CircuitWords.rest_polyTime.comp hy)))
      (CircuitWords.first_polyTime.comp hx))
    (CircuitWords.first_polyTime.comp hy)

/-- The complete answer decoder has a native polynomial-time machine certificate. -/
@[fun_prop] theorem answerWord_polyTime :
    ComputableInPolyTime answerWord (encPi encBits) encBits :=
  brouwerBarycenter_polyTime (.pi_apply encBits 0) triangleWord_polyTime

/-- The decoded denominator is exactly the canonical certificate's first scalar field. -/
theorem denominatorWord_value (tape answer : List Bool) :
    ofBits (denominatorWord tape answer) =
      generalNatField (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length)
        0 answer := by
  change ofBits (generalCertificateFieldWord
    ![List.replicate 0 true, BimatrixProgramMachine.instanceWord tape, answer]) = _
  rw [generalCertificateFieldWord_eq]
  rfl

/-- The numerator multiplies the actual action-weight field by the program's block count. -/
theorem numeratorWord_value (second : Bool) (tape answer : List Bool) :
    ofBits (numeratorWord second tape answer) =
      (BimatrixProgramCodec.dimension tape).length *
        generalNatField
          (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length)
          (if second then 9 else 7) answer := by
  rw [numeratorWord, binaryWordMul_value, binaryLengthWord_value,
    generalCertificateFieldWord_eq]
  rfl

/-- The clipped scaled coordinate represented by an accepted answer's weight field. -/
def coordinate (second : Bool) (tape answer : List Bool) : ℚ :=
  (min (ofBits (numeratorWord second tape answer))
    (ofBits (denominatorWord tape answer)) : ℕ) /
      (ofBits (denominatorWord tape answer) : ℚ)

/-- The extracted coordinate is the literal clamp of the canonical certificate coordinate. -/
theorem coordinate_eq_clamp (second : Bool) (tape answer : List Bool)
    (hk : 2 ≤ (BimatrixProgramCodec.dimension tape).length)
    (hd : 0 < ofBits (denominatorWord tape answer)) :
    coordinate second tape answer =
      max 0 (min 1 (((BimatrixProgramCodec.dimension tape).length : ℚ) *
        GameTheory.Finite.BimatrixAffineGate.value
          (decodeGeneralCertificate ((BimatrixProgramCodec.dimension tape).length * 2)
            ((BimatrixProgramCodec.dimension tape).length * 2)
            (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length) answer)
          ⟨if second then 1 else 0, by
            cases second <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega⟩)) := by
  rw [coordinate, numeratorWord_value, denominatorWord_value]
  have hD : (0 : ℚ) < generalNatField
      (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length) 0 answer := by
    rw [denominatorWord_value] at hd
    exact_mod_cast hd
  cases second <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      GameTheory.Finite.BimatrixAffineGate.value, decodeGeneralCertificate,
      finProdFinEquiv, Equiv.coe_fn_mk] <;>
    simp only [Fin.val_one, Nat.cast_min, Nat.cast_mul, Nat.reduceAdd, Nat.reduceMul] <;>
    rw [← mul_div_assoc, ← min_div_div_right hD.le] <;>
    rw [div_self hD.ne', min_comm] <;>
    rw [max_eq_right (le_min (by norm_num) (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)) hD.le))]

/-- Both coordinates lie in the closed unit interval whenever the denominator is positive. -/
theorem coordinate_bounds (second : Bool) (tape answer : List Bool)
    (hd : 0 < ofBits (denominatorWord tape answer)) :
    0 ≤ coordinate second tape answer ∧ coordinate second tape answer ≤ 1 := by
  have hdq : (0 : ℚ) < ofBits (denominatorWord tape answer) := by exact_mod_cast hd
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hdq.le
  · apply (div_le_one hdq).mpr
    exact_mod_cast Nat.min_le_right (ofBits (numeratorWord second tape answer))
      (ofBits (denominatorWord tape answer))

/-- The actual word triangle equals the canonical exact binary-cell triangle. -/
theorem triangleWord_eq (source tape answer : List Bool)
    (hd : 0 < ofBits (denominatorWord tape answer)) :
    triangleWord ![source, tape, answer] =
      encodeGridNode (CircuitWords.first source).length (some (binaryGridTriangle (CircuitWords.first source).length
        (coordinate false tape answer) (coordinate true tape answer))) := by
  have hx := BinaryRatioExtraction.value (numeratorWord false tape answer)
    (denominatorWord tape answer) (CircuitWords.first source) hd
  have hy := BinaryRatioExtraction.value (numeratorWord true tape answer)
    (denominatorWord tape answer) (CircuitWords.first source) hd
  have hpx := lowBits_lsbValue
    (BinaryRatioExtraction.prefixWord (numeratorWord false tape answer)
      (denominatorWord tape answer) (CircuitWords.first source))
  have hpy := lowBits_lsbValue
    (BinaryRatioExtraction.prefixWord (numeratorWord true tape answer)
      (denominatorWord tape answer) (CircuitWords.first source))
  rw [lsbValue_eq_foldr_bit, ← ofBits] at hpx hpy
  rw [BinaryRatioExtraction.prefixWord_length, hx.1] at hpx
  rw [BinaryRatioExtraction.prefixWord_length, hy.1] at hpy
  have hdq : (0 : ℚ) < ofBits (denominatorWord tape answer) := by exact_mod_cast hd
  have hlt : (ofBits (BinaryRatioExtraction.remainderWord
        (numeratorWord false tape answer) (denominatorWord tape answer) (CircuitWords.first source)) <
      ofBits (BinaryRatioExtraction.remainderWord
        (numeratorWord true tape answer) (denominatorWord tape answer) (CircuitWords.first source))) ↔
      binaryRemainder (CircuitWords.first source).length (coordinate false tape answer) <
      binaryRemainder (CircuitWords.first source).length (coordinate true tape answer) := by
    unfold coordinate
    rw [← hx.2.1, ← hy.2.1, div_lt_div_iff_of_pos_right hdq]
    exact_mod_cast Iff.rfl
  change [true] ++ routingLTFlag
      (BinaryRatioExtraction.remainderWord _ _ _) (BinaryRatioExtraction.remainderWord _ _ _) ++
      BinaryRatioExtraction.prefixWord _ _ _ ++ BinaryRatioExtraction.prefixWord _ _ _ = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
  rw [routingLTFlag_value]
  rw [lsbValue_eq_foldr_bit, ← ofBits, lsbValue_eq_foldr_bit, ← ofBits]
  rw [← hpx, ← hpy]
  dsimp only [coordinate] at hlt
  simp only [encodeGridNode, binaryGridTriangle, coordinate, hlt]
  rfl

/-- A small canonical-map residual turns every accepted game answer into a Brouwer answer. -/
theorem answerWord_sound (source tape answer : List Bool)
    (hk : 2 ≤ (BimatrixProgramCodec.dimension tape).length)
    (ha : generalBimatrixRelation (BimatrixProgramMachine.instanceWord tape) answer)
    (hx : |(globalGridMap (spernerColor source) (2 ^ (CircuitWords.first source).length)
      ((2 ^ (CircuitWords.first source).length : ℕ) * (coordinate false tape answer : ℝ),
       (2 ^ (CircuitWords.first source).length : ℕ) * (coordinate true tape answer : ℝ))).1 -
      (2 ^ (CircuitWords.first source).length : ℕ) * (coordinate false tape answer : ℝ)| ≤ 1 / 6)
    (hy : |(globalGridMap (spernerColor source) (2 ^ (CircuitWords.first source).length)
      ((2 ^ (CircuitWords.first source).length : ℕ) * (coordinate false tape answer : ℝ),
       (2 ^ (CircuitWords.first source).length : ℕ) * (coordinate true tape answer : ℝ))).2 -
      (2 ^ (CircuitWords.first source).length : ℕ) * (coordinate true tape answer : ℝ)| ≤ 1 / 6) :
    brouwerRelation source (answerWord ![source, tape, answer]) := by
  have hv := BimatrixProgramCorrectness.accepted_valid tape answer (by omega) ha
  have hd : 0 < ofBits (denominatorWord tape answer) := by
    have hf := generalCertificateFieldWord_eq 0 (BimatrixProgramMachine.instanceWord tape) answer
    change ofBits (generalCertificateFieldWord
      ![[], BimatrixProgramMachine.instanceWord tape, answer]) > 0
    rw [show ([] : List Bool) = List.replicate 0 true from rfl, hf]
    exact hv.1
  change brouwerRelation source (brouwerBarycenter source (triangleWord ![source,tape,answer]))
  apply brouwerBarycenter_sound
  rw [triangleWord_eq source tape answer hd]
  refine ⟨binaryGridTriangle (CircuitWords.first source).length
    (coordinate false tape answer) (coordinate true tape answer), ?_, ?_⟩
  · exact decodeGridNode_encode _ _ (fun t he => by
      cases he; exact binaryGridTriangle_valid _ _ _)
  · have hxb := coordinate_bounds false tape answer hd
    have hyb := coordinate_bounds true tape answer hd
    exact binaryGridTriangle_trichromatic _ _ _ _ hxb.1 hxb.2 hyb.1 hyb.2 hx hy

end GameTheory.Complexity.Backend.BrouwerNashAnswerMachine
