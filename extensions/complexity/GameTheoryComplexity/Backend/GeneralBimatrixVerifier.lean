module

public import GameTheoryComplexity.Backend.GeneralBimatrixCertificateCodec
public import GameTheoryComplexity.Backend.GeneralBimatrixCodecMachine
public import GameTheoryComplexity.Backend.BinaryWordMultiplication
public import GameTheoryComplexity.Backend.BimatrixCertificateVerifier
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Binary verification of rectangular games with independently signed payoff matrices.
All scan clocks count explicitly represented actions or binary bit positions. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
open scoped BigOperators

/-- A quadratic unary ruler for the certificate bit width. -/
def generalWidthRuler (input : List Bool) : List Bool :=
  List.replicate ((2 * input.length + 2) * (8 * input.length + 6)) true ++ [true]

/-- Select the row or column action clock. -/
def generalActionRuler (columnPlayer : Bool) (input : List Bool) : List Bool :=
  if columnPlayer then generalColRuler input else generalRowRuler input

/-- Select a binary certificate field by its unary field-index ruler. -/
def generalCertificateFieldWord (v : Fin 3 → List Bool) : List Bool :=
  ((v 2).drop ((v 0).length * (generalWidthRuler (v 1)).length)).take
    (generalWidthRuler (v 1)).length

/-- Probability blocks follow the six scalar fields, rows before columns. -/
def generalWeightWord (columnWeights : Bool) (v : Fin 3 → List Bool) : List Bool :=
  generalCertificateFieldWord ![List.replicate 6 true ++
    (if columnWeights then generalRowRuler (v 1) else []) ++ v 0, v 1, v 2]

/-- Read one sign of one independently represented row-major payoff matrix. -/
def generalPayoffWord (columnPlayer positive : Bool) (v : Fin 3 → List Bool) : List Bool :=
  let m := generalRowRuler (v 2)
  let n := generalColRuler (v 2)
  let h := generalBitsRuler (v 2)
  let cells := (if columnPlayer then List.replicate (m.length * n.length) true else []) ++
    List.replicate ((v 0).length * n.length) true ++ v 1
  let offset := List.replicate (cells.length * (h.length + h.length)) true ++
    (if positive then [] else h)
  ((generalPayload (v 2)).drop offset.length).take h.length

/-- A term chooses the correct matrix orientation and opposite-player weight. -/
def generalWeightedTerm (columnPlayer positive : Bool) (v : Fin 4 → List Bool) : List Bool :=
  binaryWordMul
    (generalPayoffWord columnPlayer positive
      ![if columnPlayer then v 0 else v 1, if columnPlayer then v 1 else v 0, v 2])
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
    ![List.replicate ((if columnPlayer then 4 else 2) + (if positive then 0 else 1)) true,
      v 1, v 2]
  let lhs := binaryCertificateAdd ![generalScoreWord columnPlayer true v, utility false]
  let rhs := binaryCertificateAdd ![generalScoreWord columnPlayer false v, utility true]
  andFlag (binaryCertificateLE ![lhs, rhs])
    (orFlag (certificateEqualWord (generalWeightWord columnPlayer v) [])
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
    List.replicate (4 * (m.length * n.length) * h.length) true

/-- Check all headers are positive and no matrix payload is missing or trailing. -/
def generalInstanceFlag (input : List Bool) : List Bool :=
  andFlag (notFlag (eqFlag (generalRowRuler input) []))
    (andFlag (notFlag (eqFlag (generalColRuler input) []))
    (andFlag (notFlag (eqFlag (generalBitsRuler input) []))
      [decide (input.length = (generalInstanceLengthRuler input).length)]))

/-- Check exact certificate size, both normalizations, and all best responses. -/
def generalValidCertificateVerdict (v : Fin 2 → List Bool) : List Bool :=
  let field i := generalCertificateFieldWord ![List.replicate i true, v 0, v 1]
  let ruler := generalRowRuler (v 0) ++ generalColRuler (v 0) ++ List.replicate 6 true
  andFlag [decide ((v 1).length = (ruler.length * (generalWidthRuler (v 0)).length))]
    (andFlag (notFlag (certificateEqualWord (field 0) []))
    (andFlag (notFlag (certificateEqualWord (field 1) []))
    (andFlag (certificateEqualWord (generalWeightSumWord false v) (field 0))
    (andFlag (certificateEqualWord (generalWeightSumWord true v) (field 1))
    (andFlag (generalAllChecks false v) (generalAllChecks true v))))))

/-- Malformed games have precisely the empty witness; valid games use exact certificates. -/
def generalBimatrixVerdict (v : Fin 2 → List Bool) : List Bool :=
  orFlag (andFlag (generalInstanceFlag (v 0)) (generalValidCertificateVerdict v))
    (andFlag (notFlag (generalInstanceFlag (v 0))) (eqFlag (v 1) []))

theorem generalWidthRuler_length (input : List Bool) :
    (generalWidthRuler input).length = generalCertificateWidth input.length := by
  simp [generalWidthRuler, generalCertificateWidth, List.length_append, List.length_replicate]

theorem generalInstanceLengthRuler_length (input : List Bool) :
    (generalInstanceLengthRuler input).length =
      generalRowCount input + generalColCount input + generalCoefficientBits input + 3 +
        4 * generalRowCount input * generalColCount input * generalCoefficientBits input := by
  simp [generalInstanceLengthRuler, generalRowCount, generalColCount, generalCoefficientBits,
    List.length_append, List.length_replicate]
  ring

theorem generalWeightWord_length_le (columnWeights : Bool) (v : Fin 3 → List Bool) :
    (generalWeightWord columnWeights v).length ≤ (generalWidthRuler (v 1)).length :=
  List.length_take_le _ _

theorem generalWeightedTerm_length_le (columnPlayer positive : Bool) (v : Fin 4 → List Bool) :
    (generalWeightedTerm columnPlayer positive v).length ≤
      (generalWidthRuler (v 2)).length + 2 * (generalBitsRuler (v 2)).length := by
  have h := binaryWordMul_length
    (generalPayoffWord columnPlayer positive
      ![if columnPlayer then v 0 else v 1, if columnPlayer then v 1 else v 0, v 2])
    (generalWeightWord (!columnPlayer) ![v 0, v 2, v 3])
  have hw := generalWeightWord_length_le (!columnPlayer) ![v 0, v 2, v 3]
  have hp : (generalPayoffWord columnPlayer positive
      ![if columnPlayer then v 0 else v 1, if columnPlayer then v 1 else v 0, v 2]).length ≤
      (generalBitsRuler (v 2)).length := List.length_take_le _ _
  change (generalWeightedTerm columnPlayer positive v).length ≤ _ at h
  change (generalWeightWord (!columnPlayer) ![v 0, v 2, v 3]).length ≤
    (generalWidthRuler (v 2)).length at hw
  omega

end GameTheory.Complexity.Backend
