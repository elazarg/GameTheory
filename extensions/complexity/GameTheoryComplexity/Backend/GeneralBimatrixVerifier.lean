import GameTheoryComplexity.Backend.GeneralBimatrixCertificateCodec
import GameTheoryComplexity.Backend.GeneralBimatrixCodecMachine
import GameTheoryComplexity.Backend.BinaryWordMultiplication
import GameTheoryComplexity.Backend.BimatrixCertificateVerifier

/-! Binary verification of rectangular, independently signed bimatrix payoffs.
All scan clocks count explicitly represented actions or binary bit positions. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

/-- A quadratic unary ruler for the certificate bit width. -/
def generalWidthRuler (input : List Bool) : List Bool :=
  smash (input ++ input ++ [true, true])
    (smash (List.replicate 8 true) input ++ List.replicate 6 true) ++ [true]

/-- Select the row or column action clock. -/
def generalActionRuler (columnPlayer : Bool) (input : List Bool) : List Bool :=
  bif columnPlayer then generalColRuler input else generalRowRuler input

/-- Select a binary certificate field by its unary field-index ruler. -/
def generalCertificateFieldWord (v : Fin 3 → List Bool) : List Bool :=
  ((v 2).drop ((v 0).length * (generalWidthRuler (v 1)).length)).take
    (generalWidthRuler (v 1)).length

/-- Probability blocks follow the six scalar fields, rows before columns. -/
def generalWeightWord (columnWeights : Bool) (v : Fin 3 → List Bool) : List Bool :=
  generalCertificateFieldWord ![List.replicate 6 true ++
    (bif columnWeights then generalRowRuler (v 1) else []) ++ v 0, v 1, v 2]

/-- Read one sign of one independently represented row-major payoff matrix. -/
def generalPayoffWord (columnPlayer positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let m := generalRowRuler (v 2)
  let n := generalColRuler (v 2)
  let h := generalBitsRuler (v 2)
  let cells := (bif columnPlayer then smash m n else []) ++ smash (v 0) n ++ v 1
  let offset := smash cells (h ++ h) ++ (bif positive then [] else h)
  ((generalPayload (v 2)).drop offset.length).take h.length

/-- A term chooses the correct matrix orientation and opposite-player weight. -/
def generalWeightedTerm (columnPlayer positive : Bool) (v : Fin 4 → List Bool) : List Bool :=
  binaryWordMul
    (generalPayoffWord columnPlayer positive
      ![bif columnPlayer then v 0 else v 1, bif columnPlayer then v 1 else v 0, v 2])
    (generalWeightWord (!columnPlayer) ![v 0, v 2, v 3])

/-- Evaluate a pure-action numerator with an opposite-dimension bounded scan. -/
def generalScoreWord (columnPlayer positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  binaryIndexedSum (generalWeightedTerm columnPlayer positive)
    (generalActionRuler (!columnPlayer) (v 1)) v

/-- Sum a probability numerator block over its explicitly represented actions. -/
def generalWeightSumWord (columnWeights : Bool) (v : Fin 2 → List Bool) : List Bool :=
  binaryIndexedSum (generalWeightWord columnWeights)
    (generalActionRuler columnWeights (v 0)) v

/-- Signed inequalities compare positive score plus negative utility with the converse. -/
def generalActionCheck (columnPlayer : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let utility positive := generalCertificateFieldWord
    ![List.replicate ((bif columnPlayer then 4 else 2) + (bif positive then 0 else 1)) true,
      v 1, v 2]
  let lhs := binaryCertificateAdd ![generalScoreWord columnPlayer true v, utility false]
  let rhs := binaryCertificateAdd ![generalScoreWord columnPlayer false v, utility true]
  andBit (binaryCertificateLE ![lhs, rhs])
    (orBit (certificateEqualWord (generalWeightWord columnPlayer v) [])
      (certificateEqualWord lhs rhs))

/-- Check every pure-action inequality and every occupied support equation. -/
def generalAllChecks (columnPlayer : Bool) (v : Fin 2 → List Bool) : List Bool :=
  certificateAll (generalActionCheck columnPlayer) (generalActionRuler columnPlayer (v 0)) v

/-- Unary ruler for the exact encoded instance length. -/
def generalInstanceLengthRuler (input : List Bool) : List Bool :=
  let m := generalRowRuler input
  let n := generalColRuler input
  let h := generalBitsRuler input
  m ++ n ++ h ++ [true, true, true] ++
    smash (List.replicate 4 true) (smash (smash m n) h)

/-- Check all headers are positive and no matrix payload is missing or trailing. -/
def generalInstanceFlag (input : List Bool) : List Bool :=
  andBit (notBit (eqFlag (generalRowRuler input) []))
    (andBit (notBit (eqFlag (generalColRuler input) []))
    (andBit (notBit (eqFlag (generalBitsRuler input) []))
      (lenEqFlag input (generalInstanceLengthRuler input))))

/-- Check exact certificate size, both normalizations, and all best responses. -/
def generalValidCertificateVerdict (v : Fin 2 → List Bool) : List Bool :=
  let field i := generalCertificateFieldWord ![List.replicate i true, v 0, v 1]
  let ruler := generalRowRuler (v 0) ++ generalColRuler (v 0) ++ List.replicate 6 true
  andBit (lenEqFlag (v 1) (smash ruler (generalWidthRuler (v 0))))
    (andBit (notBit (certificateEqualWord (field 0) []))
    (andBit (notBit (certificateEqualWord (field 1) []))
    (andBit (certificateEqualWord (generalWeightSumWord false v) (field 0))
    (andBit (certificateEqualWord (generalWeightSumWord true v) (field 1))
    (andBit (generalAllChecks false v) (generalAllChecks true v))))))

/-- Malformed games have precisely the empty witness; valid games use exact certificates. -/
def generalBimatrixVerdict (v : Fin 2 → List Bool) : List Bool :=
  orBit (andBit (generalInstanceFlag (v 0)) (generalValidCertificateVerdict v))
    (andBit (notBit (generalInstanceFlag (v 0))) (eqFlag (v 1) []))

theorem generalWidthRuler_length (input : List Bool) :
    (generalWidthRuler input).length = generalCertificateWidth input.length := by
  simp [generalWidthRuler, generalCertificateWidth, smash_length, Nat.mul_comm]
  omega

theorem generalWidthRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalWidthRuler (v 0) :=
  Cobham.appendFn (Cobham.comp₂ Cobham.smash
    (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [true, true]))
    (Cobham.appendFn
      (Cobham.comp₂ Cobham.smash (Cobham.const (List.replicate 8 true)) (.proj 0))
      (Cobham.const (List.replicate 6 true)))) (Cobham.const [true])

theorem generalActionRuler_cobham (columnPlayer : Bool) :
    Cobham fun v : Fin 1 → List Bool => generalActionRuler columnPlayer (v 0) := by
  cases columnPlayer
  · exact generalRowRuler_cobham
  · exact generalColRuler_cobham

theorem generalCertificateFieldWord_cobham : Cobham generalCertificateFieldWord := by
  have hw : Cobham fun v : Fin 3 → List Bool => generalWidthRuler (v 1) :=
    Cobham.comp generalWidthRuler_cobham fun _ => .proj 1
  exact (Cobham.takeFn hw (Cobham.dropFn
    (Cobham.comp₂ Cobham.smash (.proj 0) hw) (.proj 2))).of_eq fun v => by
      simp only [smash_length]
      rfl

theorem generalWeightWord_cobham (columnWeights : Bool) :
    Cobham (generalWeightWord columnWeights) := by
  apply Cobham.comp₃ generalCertificateFieldWord_cobham
    (Cobham.appendFn (Cobham.appendFn (Cobham.const (List.replicate 6 true)) ?_) (.proj 0))
    (.proj 1) (.proj 2)
  cases columnWeights
  · exact Cobham.empty
  · exact Cobham.comp generalRowRuler_cobham fun _ => .proj 1

theorem generalWeightWord_length_le (columnWeights : Bool) (v : Fin 3 → List Bool) :
    (generalWeightWord columnWeights v).length ≤ (generalWidthRuler (v 1)).length :=
  List.length_take_le _ _

theorem generalPayoffWord_cobham (columnPlayer positive : Bool) :
    Cobham (generalPayoffWord columnPlayer positive) := by
  have hm : Cobham fun v : Fin 3 → List Bool => generalRowRuler (v 2) :=
    Cobham.comp generalRowRuler_cobham fun _ => .proj 2
  have hn : Cobham fun v : Fin 3 → List Bool => generalColRuler (v 2) :=
    Cobham.comp generalColRuler_cobham fun _ => .proj 2
  have hh : Cobham fun v : Fin 3 → List Bool => generalBitsRuler (v 2) :=
    Cobham.comp generalBitsRuler_cobham fun _ => .proj 2
  have hp : Cobham fun v : Fin 3 → List Bool => generalPayload (v 2) :=
    Cobham.comp generalPayload_cobham fun _ => .proj 2
  have hb : Cobham fun v : Fin 3 → List Bool =>
      bif columnPlayer then smash (generalRowRuler (v 2)) (generalColRuler (v 2)) else [] := by
    cases columnPlayer
    · exact Cobham.empty
    · exact Cobham.comp₂ Cobham.smash hm hn
  have ho := Cobham.comp₂ Cobham.smash
    (Cobham.appendFn (Cobham.appendFn hb (Cobham.comp₂ Cobham.smash (.proj 0) hn)) (.proj 1))
    (Cobham.appendFn hh hh)
  have hs : Cobham fun v : Fin 3 → List Bool =>
      bif positive then [] else generalBitsRuler (v 2) := by
    cases positive
    · exact hh
    · exact Cobham.empty
  exact (Cobham.takeFn hh (Cobham.dropFn (Cobham.appendFn ho hs) hp)).of_eq fun _ => rfl

theorem generalWeightedTerm_cobham (columnPlayer positive : Bool) :
    Cobham (generalWeightedTerm columnPlayer positive) := by
  apply Cobham.comp₂ binaryWordMul_cobham
  · apply Cobham.comp₃ (generalPayoffWord_cobham columnPlayer positive) ?_ ?_ (.proj 2)
    all_goals cases columnPlayer <;> exact Cobham.proj _
  · exact Cobham.comp₃ (generalWeightWord_cobham (!columnPlayer)) (.proj 0) (.proj 2) (.proj 3)

theorem generalWeightedTerm_length_le (columnPlayer positive : Bool) (v : Fin 4 → List Bool) :
    (generalWeightedTerm columnPlayer positive v).length ≤
      (generalWidthRuler (v 2)).length + 2 * (generalBitsRuler (v 2)).length := by
  have h := binaryWordMul_length
    (generalPayoffWord columnPlayer positive
      ![bif columnPlayer then v 0 else v 1, bif columnPlayer then v 1 else v 0, v 2])
    (generalWeightWord (!columnPlayer) ![v 0, v 2, v 3])
  have hw := generalWeightWord_length_le (!columnPlayer) ![v 0, v 2, v 3]
  have hp : (generalPayoffWord columnPlayer positive
      ![bif columnPlayer then v 0 else v 1, bif columnPlayer then v 1 else v 0, v 2]).length ≤
      (generalBitsRuler (v 2)).length := List.length_take_le _ _
  change (generalWeightedTerm columnPlayer positive v).length ≤ _ at h
  change (generalWeightWord (!columnPlayer) ![v 0, v 2, v 3]).length ≤
    (generalWidthRuler (v 2)).length at hw
  omega

theorem generalScoreWord_cobham (columnPlayer positive : Bool) :
    Cobham (generalScoreWord columnPlayer positive) := by
  let width := fun v : Fin 3 → List Bool =>
    generalWidthRuler (v 1) ++ generalBitsRuler (v 1) ++ generalBitsRuler (v 1)
  have hw : Cobham width := Cobham.appendFn (Cobham.appendFn
    (Cobham.comp generalWidthRuler_cobham fun _ => .proj 1)
    (Cobham.comp generalBitsRuler_cobham fun _ => .proj 1))
    (Cobham.comp generalBitsRuler_cobham fun _ => .proj 1)
  have hf := binaryIndexedSum_cobham (generalWeightedTerm_cobham columnPlayer positive) hw
    (fun r v => by
      have h := generalWeightedTerm_length_le columnPlayer positive (Fin.cons r v)
      change (generalWeightedTerm columnPlayer positive (Fin.cons r v)).length ≤
        (generalWidthRuler (v 1)).length + 2 * (generalBitsRuler (v 1)).length at h
      simpa only [width, List.length_append, two_mul, Nat.add_assoc] using h)
  have hg : ∀ i : Fin 4, Cobham fun v : Fin 3 → List Bool =>
      (Fin.cons (generalActionRuler (!columnPlayer) (v 1)) v : Fin 4 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp (generalActionRuler_cobham (!columnPlayer)) fun _ => .proj 1
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

theorem generalWeightSumWord_cobham (columnWeights : Bool) :
    Cobham (generalWeightSumWord columnWeights) := by
  have hw : Cobham fun v : Fin 2 → List Bool => generalWidthRuler (v 0) :=
    Cobham.comp generalWidthRuler_cobham fun _ => .proj 0
  have hf := binaryIndexedSum_cobham (generalWeightWord_cobham columnWeights) hw
    (fun r v => generalWeightWord_length_le columnWeights (Fin.cons r v))
  have hg : ∀ i : Fin 3, Cobham fun v : Fin 2 → List Bool =>
      (Fin.cons (generalActionRuler columnWeights (v 0)) v : Fin 3 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp (generalActionRuler_cobham columnWeights) fun _ => .proj 0
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

private theorem generalEqual_cobham : Cobham fun v : Fin 2 → List Bool =>
    certificateEqualWord (v 0) (v 1) :=
  Cobham.andFn binaryCertificateLE_cobham
    (Cobham.comp₂ binaryCertificateLE_cobham (.proj 1) (.proj 0))

theorem generalActionCheck_cobham (columnPlayer : Bool) :
    Cobham (generalActionCheck columnPlayer) := by
  have hu (positive : Bool) := Cobham.comp₃ generalCertificateFieldWord_cobham
    (Cobham.const (List.replicate
      ((bif columnPlayer then 4 else 2) + (bif positive then 0 else 1)) true))
    (Cobham.proj (1 : Fin 3)) (Cobham.proj 2)
  have hl := Cobham.comp₂ binaryCertificateAdd_cobham
    (generalScoreWord_cobham columnPlayer true) (hu false)
  have hr := Cobham.comp₂ binaryCertificateAdd_cobham
    (generalScoreWord_cobham columnPlayer false) (hu true)
  exact Cobham.andFn (Cobham.comp₂ binaryCertificateLE_cobham hl hr)
    (Cobham.orFn
      (Cobham.comp₂ generalEqual_cobham (generalWeightWord_cobham columnPlayer) Cobham.empty)
      (Cobham.comp₂ generalEqual_cobham hl hr))

theorem generalAllChecks_cobham (columnPlayer : Bool) : Cobham (generalAllChecks columnPlayer) := by
  have hf := certificateAll_cobham (generalActionCheck_cobham columnPlayer)
  have hg : ∀ i : Fin 3, Cobham fun v : Fin 2 → List Bool =>
      (Fin.cons (generalActionRuler columnPlayer (v 0)) v : Fin 3 → List Bool) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.comp (generalActionRuler_cobham columnPlayer) fun _ => .proj 0
    · exact Cobham.proj j
  exact (Cobham.comp hf hg).of_eq fun _ => rfl

end GameTheory.Complexity.Backend
