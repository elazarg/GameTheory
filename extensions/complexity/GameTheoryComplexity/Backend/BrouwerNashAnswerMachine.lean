import GameTheoryComplexity.Backend.BimatrixProgramCorrectness
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
import GameTheoryComplexity.Backend.BinaryRatioExtraction
import GameTheoryComplexity.Backend.BrouwerReduction
import GameTheory.Math.GridBrouwerBinaryCell
import GameTheory.Math.ClippedArithmetic

/-! Bounded word extraction converts normalized Nash coordinate weights into
an exact dyadic triangle and emits its canonical rational barycenter. -/
namespace GameTheory.Complexity.Backend.BrouwerNashAnswerMachine
open _root_.Complexity _root_.Complexity.Cobham
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
    (denominatorWord (v 1) (v 2)) (pairFst (v 0))

/-- The containing dyadic triangle, including endpoint and rising-diagonal ties. -/
def triangleWord (v : Fin 3 → List Bool) : List Bool :=
  let x := coordinateState false v
  let y := coordinateState true v
  [true] ++ routingLTFlag (pairSnd x) (pairSnd y) ++ pairFst x ++ pairFst y

/-- Emit a canonical rational barycenter answer to the source Brouwer instance. -/
def answerWord (v : Fin 3 → List Bool) : List Bool :=
  brouwerBarycenter (v 0) (triangleWord v)

private theorem game_fn {p : ℕ} {tape : (Fin p → List Bool) → List Bool}
    (ht : Cobham tape) : Cobham fun v => BimatrixProgramMachine.instanceWord (tape v) :=
  by
    have h := Cobham.comp (FP_subset_CobhamFP BimatrixProgramMachine.instanceWord_mem_FP)
      (fun _ : Fin 1 => ht)
    exact h

private theorem denominator_fn {p : ℕ} {tape answer : (Fin p → List Bool) → List Bool}
    (ht : Cobham tape) (ha : Cobham answer) :
    Cobham fun v => denominatorWord (tape v) (answer v) :=
  by
    have h := Cobham.comp₃ generalCertificateFieldWord_cobham (Cobham.const []) (game_fn ht) ha
    exact h

private theorem numerator_fn (second : Bool) {p : ℕ}
    {tape answer : (Fin p → List Bool) → List Bool} (ht : Cobham tape) (ha : Cobham answer) :
    Cobham fun v => numeratorWord second (tape v) (answer v) := by
  have h := Cobham.comp₂ binaryWordMul_cobham
    (Cobham.comp binaryLengthWord_cobham fun _ =>
      Cobham.comp BimatrixProgramCodec.dimension_cobham fun _ => ht)
    (Cobham.comp₃ generalCertificateFieldWord_cobham
      (Cobham.const (List.replicate (if second then 9 else 7) true)) (game_fn ht) ha)
  simpa only [numeratorWord, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ] using h

/-- Coordinate extraction has an actual polynomial-time word certificate. -/
theorem coordinateState_cobham (second : Bool) : Cobham (coordinateState second) := by
  unfold coordinateState
  have h := Cobham.comp₃ BinaryRatioExtraction.state_cobham
    (numerator_fn second (.proj 1) (.proj 2))
    (denominator_fn (.proj 1) (.proj 2))
    (Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) fun _ : Fin 1 =>
      (Cobham.proj 0 : Cobham (fun v : Fin 3 → List Bool => v 0)))
  simpa only [coordinateState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ] using h

/-- Triangle formation compares residual words with their common denominator. -/
theorem triangleWord_cobham : Cobham triangleWord := by
  unfold triangleWord
  have hx := coordinateState_cobham false
  have hy := coordinateState_cobham true
  have fst {f : (Fin 3 → List Bool) → List Bool} (h : Cobham f) :=
    Cobham.comp (FP_subset_CobhamFP pairFst_mem_FP) (fun _ : Fin 1 => h)
  have snd {f : (Fin 3 → List Bool) → List Bool} (h : Cobham f) :=
    Cobham.comp (FP_subset_CobhamFP pairSnd_mem_FP) (fun _ : Fin 1 => h)
  have hlt := FP_subset_CobhamFP (routingLTFlagFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
  have h := appendFn (appendFn (appendFn (Cobham.const [true])
    (Cobham.comp hlt fun _ => Cobham.comp₂ Cobham.pairing (snd hx) (snd hy)))
    (fst hx)) (fst hy)
  simpa only [pairFst_pair, pairSnd_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ] using h

/-- The answer conversion is implemented by a certified polynomial-time machine. -/
theorem answerWord_cobham : Cobham answerWord := by
  unfold answerWord
  have h := Cobham.comp₂ (cobham_iff_FPn.mpr brouwerBarycenter_mem_FPn)
    (Cobham.proj 0 : Cobham (fun v : Fin 3 → List Bool => v 0)) triangleWord_cobham
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem answerWord_mem_FPn : FPn answerWord := cobham_iff_FPn.mp answerWord_cobham

/-- The decoded denominator is exactly the canonical certificate's first scalar field. -/
theorem denominatorWord_value (tape answer : List Bool) :
    Nat.fromBitsLE (denominatorWord tape answer) =
      generalNatField (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length)
        0 answer := by
  change Nat.fromBitsLE (generalCertificateFieldWord
    ![List.replicate 0 true, BimatrixProgramMachine.instanceWord tape, answer]) = _
  rw [generalCertificateFieldWord_eq]
  rfl

/-- The numerator multiplies the actual action-weight field by the program's block count. -/
theorem numeratorWord_value (second : Bool) (tape answer : List Bool) :
    Nat.fromBitsLE (numeratorWord second tape answer) =
      (BimatrixProgramCodec.dimension tape).length *
        generalNatField
          (generalCertificateWidth (BimatrixProgramMachine.instanceWord tape).length)
          (if second then 9 else 7) answer := by
  rw [numeratorWord, binaryWordMul_value, binaryLengthWord_value,
    generalCertificateFieldWord_eq]
  rfl

/-- The clipped scaled coordinate represented by an accepted answer's weight field. -/
def coordinate (second : Bool) (tape answer : List Bool) : ℚ :=
  (min (Nat.fromBitsLE (numeratorWord second tape answer))
    (Nat.fromBitsLE (denominatorWord tape answer)) : ℕ) /
      (Nat.fromBitsLE (denominatorWord tape answer) : ℚ)

/-- The extracted coordinate is the literal clamp of the canonical certificate coordinate. -/
theorem coordinate_eq_clamp (second : Bool) (tape answer : List Bool)
    (hk : 2 ≤ (BimatrixProgramCodec.dimension tape).length)
    (hd : 0 < Nat.fromBitsLE (denominatorWord tape answer)) :
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
    (hd : 0 < Nat.fromBitsLE (denominatorWord tape answer)) :
    0 ≤ coordinate second tape answer ∧ coordinate second tape answer ≤ 1 := by
  have hdq : (0 : ℚ) < Nat.fromBitsLE (denominatorWord tape answer) := by exact_mod_cast hd
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hdq.le
  · apply (div_le_one hdq).mpr
    exact_mod_cast Nat.min_le_right (Nat.fromBitsLE (numeratorWord second tape answer))
      (Nat.fromBitsLE (denominatorWord tape answer))

/-- The actual word triangle equals the canonical exact binary-cell triangle. -/
theorem triangleWord_eq (source tape answer : List Bool)
    (hd : 0 < Nat.fromBitsLE (denominatorWord tape answer)) :
    triangleWord ![source, tape, answer] =
      encodeGridNode (pairFst source).length (some (binaryGridTriangle (pairFst source).length
        (coordinate false tape answer) (coordinate true tape answer))) := by
  have hx := BinaryRatioExtraction.value (numeratorWord false tape answer)
    (denominatorWord tape answer) (pairFst source) hd
  have hy := BinaryRatioExtraction.value (numeratorWord true tape answer)
    (denominatorWord tape answer) (pairFst source) hd
  have hpx := Nat.toBitsLE_fromBitsLE
    (BinaryRatioExtraction.prefixWord (numeratorWord false tape answer)
      (denominatorWord tape answer) (pairFst source))
  have hpy := Nat.toBitsLE_fromBitsLE
    (BinaryRatioExtraction.prefixWord (numeratorWord true tape answer)
      (denominatorWord tape answer) (pairFst source))
  rw [BinaryRatioExtraction.prefixWord_length, hx.1] at hpx
  rw [BinaryRatioExtraction.prefixWord_length, hy.1] at hpy
  have hdq : (0 : ℚ) < Nat.fromBitsLE (denominatorWord tape answer) := by exact_mod_cast hd
  have hlt : (Nat.fromBitsLE (BinaryRatioExtraction.remainderWord
        (numeratorWord false tape answer) (denominatorWord tape answer) (pairFst source)) <
      Nat.fromBitsLE (BinaryRatioExtraction.remainderWord
        (numeratorWord true tape answer) (denominatorWord tape answer) (pairFst source))) ↔
      binaryRemainder (pairFst source).length (coordinate false tape answer) <
      binaryRemainder (pairFst source).length (coordinate true tape answer) := by
    unfold coordinate
    rw [← hx.2.1, ← hy.2.1, div_lt_div_iff_of_pos_right hdq]
    exact_mod_cast Iff.rfl
  change [true] ++ routingLTFlag
      (BinaryRatioExtraction.remainderWord _ _ _) (BinaryRatioExtraction.remainderWord _ _ _) ++
      BinaryRatioExtraction.prefixWord _ _ _ ++ BinaryRatioExtraction.prefixWord _ _ _ = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
  rw [routingLTFlag_value]
  rw [← hpx, ← hpy]
  dsimp only [coordinate] at hlt
  simp only [encodeGridNode, binaryGridTriangle, coordinate, hlt]
  rfl

/-- A small canonical-map residual turns every accepted game answer into a Brouwer answer. -/
theorem answerWord_sound (source tape answer : List Bool)
    (hk : 2 ≤ (BimatrixProgramCodec.dimension tape).length)
    (ha : generalBimatrixRelation (BimatrixProgramMachine.instanceWord tape) answer)
    (hx : |(globalGridMap (spernerColor source) (2 ^ (pairFst source).length)
      ((2 ^ (pairFst source).length : ℕ) * (coordinate false tape answer : ℝ),
       (2 ^ (pairFst source).length : ℕ) * (coordinate true tape answer : ℝ))).1 -
      (2 ^ (pairFst source).length : ℕ) * (coordinate false tape answer : ℝ)| ≤ 1 / 6)
    (hy : |(globalGridMap (spernerColor source) (2 ^ (pairFst source).length)
      ((2 ^ (pairFst source).length : ℕ) * (coordinate false tape answer : ℝ),
       (2 ^ (pairFst source).length : ℕ) * (coordinate true tape answer : ℝ))).2 -
      (2 ^ (pairFst source).length : ℕ) * (coordinate true tape answer : ℝ)| ≤ 1 / 6) :
    brouwerRelation source (answerWord ![source, tape, answer]) := by
  have hv := BimatrixProgramCorrectness.accepted_valid tape answer (by omega) ha
  have hd : 0 < Nat.fromBitsLE (denominatorWord tape answer) := by
    have hf := generalCertificateFieldWord_eq 0 (BimatrixProgramMachine.instanceWord tape) answer
    change Nat.fromBitsLE (generalCertificateFieldWord
      ![[], BimatrixProgramMachine.instanceWord tape, answer]) > 0
    rw [show ([] : List Bool) = List.replicate 0 true from rfl, hf]
    exact hv.1
  change brouwerRelation source (brouwerBarycenter source (triangleWord ![source,tape,answer]))
  apply brouwerBarycenter_sound
  rw [triangleWord_eq source tape answer hd]
  refine ⟨binaryGridTriangle (pairFst source).length
    (coordinate false tape answer) (coordinate true tape answer), ?_, ?_⟩
  · exact decodeGridNode_encode _ _ (fun t he => by
      cases he; exact binaryGridTriangle_valid _ _ _)
  · have hxb := coordinate_bounds false tape answer hd
    have hyb := coordinate_bounds true tape answer hd
    exact binaryGridTriangle_trichromatic _ _ _ _ hxb.1 hxb.2 hyb.1 hyb.2 hx hy

end GameTheory.Complexity.Backend.BrouwerNashAnswerMachine
