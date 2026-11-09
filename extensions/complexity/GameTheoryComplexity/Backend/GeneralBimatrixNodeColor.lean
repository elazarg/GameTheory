module

public import GameTheoryComplexity.Backend.GeneralBimatrixNodeValidation
public import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
public import GameTheoryComplexity.Backend.BimatrixNodeColor
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Integer orientation and source calibration for serialized bimatrix games.
The calibration uses the same dictionary computation as every other vertex. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- The fixed vertex width, with a positive fallback for malformed games. -/
def generalBimatrixNodeRuler (input : List Bool) : List Bool :=
  let dim := generalBimatrixDimensionWord input
  select (generalInstanceFlag input) (dim ++ dim ++ dim ++ dim) [false]

/-- The all-false source word at the instance's vertex width. -/
def generalBimatrixNodeOrigin (input : List Bool) : List Bool :=
  List.replicate (generalBimatrixNodeRuler input).length false

/-- Compute the determinant orientation of an explicitly supplied path vertex. -/
def generalBimatrixNodeScore (v : Fin 2 → List Bool) : List Bool :=
  bimatrixNodeOrientationWord ![generalBimatrixDimensionWord (v 0), v 1,
    generalBimatrixNodeData v 2,
    generalBimatrixDictionaryDeterminant (generalBimatrixNodeData v)]

/-- Recompute the distinguished source's orientation for calibration. -/
def generalBimatrixSourceScore (input : List Bool) : List Bool :=
  generalBimatrixNodeScore ![input, generalBimatrixNodeOrigin input]

/-- Source-calibrated orientation chooses which involution is outgoing. -/
def generalBimatrixNodeColor (v : Fin 2 → List Bool) : List Bool :=
  binaryScoreColor ![generalBimatrixNodeScore v, generalBimatrixSourceScore (v 0)]

theorem generalBimatrixNodeRuler_length (input : List Bool) (hi : GeneralInstanceValid input) :
    (generalBimatrixNodeRuler input).length =
      4 * (generalRowCount input + generalColCount input) := by
  rw [generalBimatrixNodeRuler, (generalInstanceFlag_eq_true_iff input).mpr hi]
  change (generalBimatrixDimensionWord input ++ generalBimatrixDimensionWord input ++
    generalBimatrixDimensionWord input ++ generalBimatrixDimensionWord input).length = _
  simp only [List.length_append, generalBimatrixDimensionWord_length]
  omega

theorem generalBimatrixNodeRuler_pos (input : List Bool) :
    0 < (generalBimatrixNodeRuler input).length := by
  by_cases hi : GeneralInstanceValid input
  · rw [generalBimatrixNodeRuler_length input hi]
    have hm := hi.1
    omega
  · have hf : generalInstanceFlag input = [false] := by
      obtain ⟨bit, hbit⟩ : ∃ bit : Bool, generalInstanceFlag input = [bit] := ⟨_, rfl⟩
      cases bit
      · exact hbit
      · exact (hi ((generalInstanceFlag_eq_true_iff input).mp hbit)).elim
    rw [generalBimatrixNodeRuler, hf]
    change 0 < 1
    decide

theorem generalBimatrixNodeOrigin_value (input : List Bool) (hi : GeneralInstanceValid input) :
    generalBimatrixNodeOrigin input =
      List.replicate (4 * (generalRowCount input + generalColCount input)) false := by
  rw [generalBimatrixNodeOrigin, generalBimatrixNodeRuler_length input hi]


end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

theorem generalBimatrixNodeScore_encode (input : List Bool)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : BimatrixPathPort
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d) :
    binarySignedValue (generalBimatrixNodeScore ![input, encode port]) =
      port.computedOrientationScore := by
  apply bimatrixNodeOrientationWord_value _ _ _ _
    (generalBimatrixDimensionWord_length input) hd port
    (basic_encode port) (generalBimatrixNodeData_entering input
      (generalBimatrixDimensionWord_length input) hd port)
  have hb := generalBimatrixNodeData_basis input (generalBimatrixDimensionWord_length input) port
  have he : generalBimatrixNodeData ![input, encode port] =
      ![input, membershipWord port.node.basis.basic,
        generalBimatrixNodeData ![input, encode port] 2] := by
    funext i
    fin_cases i
    · rfl
    · exact hb
    · rfl
  rw [he]
  simpa only [GameTheory.Math.IntegerCramerComputation.determinant_eq] using
    generalBimatrixDictionaryDeterminant_value input port.node.basis
      (generalBimatrixNodeData ![input, encode port] 2)

theorem generalBimatrixNodeColor_encode (input : List Bool) (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : BimatrixPathPort
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d) :
    generalBimatrixNodeColor ![input, encode port] = [port.color] := by
  apply binaryScoreColor_eq port _ _ (generalBimatrixNodeScore_encode input hd port)
  have ho : generalBimatrixNodeOrigin input = encode
      (bimatrixSourcePort
        (fun i j => decodeGeneralPayoff false input i.val j.val +
          ((2 : ℤ) ^ generalCoefficientBits input + 1))
        (fun i j => decodeGeneralPayoff true input i.val j.val +
          ((2 : ℤ) ^ generalCoefficientBits input + 1)) d) := by
    rw [generalBimatrixNodeOrigin_value input hi, encode_source]
    rfl
  change binarySignedValue (generalBimatrixNodeScore ![input, generalBimatrixNodeOrigin input]) = _
  rw [ho]
  exact generalBimatrixNodeScore_encode input hd _

@[fun_prop] theorem generalBimatrixNodeRuler_polyTime :
    ComputableInPolyTime generalBimatrixNodeRuler encBits encBits := by
  have hinput : ComputableInPolyTime (fun input : List Bool => ![input]) encBits (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .id'
  have hdim0 := generalBimatrixDimensionWord_polyTime.comp hinput
  have hdim : ComputableInPolyTime generalBimatrixDimensionWord encBits encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hdim0.tidy.of_enc_eq
    intro input
    rfl
  have hquad := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hdim hdim) hdim) hdim
  have h := select_polyTime.comp
    (generalInstanceFlag_polyTime.prod (hquad.prod (ComputableInPolyTime.const [false])))
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeRuler)
  intro input
  rfl

@[fun_prop] theorem generalBimatrixNodeOrigin_polyTime :
    ComputableInPolyTime generalBimatrixNodeOrigin encBits encBits := by
  have h := (ComputableInPolyTime.bitsReplicate false).comp
    (ComputableInPolyTime.length_bits_comp generalBimatrixNodeRuler_polyTime)
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeOrigin)
  intro input
  rfl

@[fun_prop] theorem generalBimatrixNodeScore_polyTime :
    ComputableInPolyTime generalBimatrixNodeScore (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 2 → List Bool => ![v 0])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    exact .pi_apply encBits (0 : Fin 2)
  have hdim0 := generalBimatrixDimensionWord_polyTime.comp hinput
  have hdim : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => generalBimatrixDimensionWord (v 0))
      (encPi encBits) encBits := by
    apply ComputableInPolyTime.of_tidy
    apply hdim0.tidy.of_enc_eq
    intro v
    rfl
  have hentering := (ComputableInPolyTime.pi_apply encBits (2 : Fin 3)).comp
    generalBimatrixNodeData_polyTime
  have hdet := generalBimatrixDictionaryDeterminant_polyTime.comp generalBimatrixNodeData_polyTime
  have hargs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalBimatrixDimensionWord (v 0), v 1,
        generalBimatrixNodeData v 2, generalBimatrixDictionaryDeterminant (generalBimatrixNodeData v)])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdim
    · exact .pi_apply encBits 1
    · exact hentering
    · exact hdet
  have h := bimatrixNodeOrientationWord_polyTime.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeScore)
  intro v
  rfl

@[fun_prop] theorem generalBimatrixSourceScore_polyTime :
    ComputableInPolyTime generalBimatrixSourceScore encBits encBits := by
  have hargs : ComputableInPolyTime
      (fun input : List Bool => ![input, generalBimatrixNodeOrigin input])
      encBits (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .id'
    · exact generalBimatrixNodeOrigin_polyTime
  have h := generalBimatrixNodeScore_polyTime.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixSourceScore)
  intro input
  rfl

@[fun_prop] theorem generalBimatrixNodeColor_polyTime :
    ComputableInPolyTime generalBimatrixNodeColor (encPi encBits) encBits := by
  have hinput : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hsource := generalBimatrixSourceScore_polyTime.comp hinput
  have hargs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![generalBimatrixNodeScore v, generalBimatrixSourceScore (v 0)])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact generalBimatrixNodeScore_polyTime
    · exact hsource
  have h := binaryScoreColor_polyTime.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixNodeColor)
  intro v
  rfl

end GameTheory.Complexity.Backend
