import GameTheoryComplexity.Backend.GeneralBimatrixNodeValidation
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
import GameTheoryComplexity.Backend.BimatrixNodeColor

/-! Integer orientation and source calibration for serialized bimatrix games.
The calibration uses the same dictionary computation as every other vertex. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The fixed vertex width, with a positive fallback for malformed games. -/
def generalBimatrixNodeRuler (input : List Bool) : List Bool :=
  let dim := generalBimatrixDimensionWord input
  caseBit₀ (generalInstanceFlag input) (dim ++ dim ++ dim ++ dim) [false]

theorem generalBimatrixNodeRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalBimatrixNodeRuler (v 0) := by
  have hd := generalBimatrixDimensionWord_cobham
  exact Cobham.iteFn generalInstanceFlag_cobham
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn hd hd) hd) hd)
    (Cobham.const [false])

/-- The all-false source word at the instance's vertex width. -/
def generalBimatrixNodeOrigin (input : List Bool) : List Bool :=
  padTo (generalBimatrixNodeRuler input) []

theorem generalBimatrixNodeOrigin_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalBimatrixNodeOrigin (v 0) :=
  Cobham.padFn generalBimatrixNodeRuler_cobham Cobham.empty

/-- Compute the determinant orientation of an explicitly supplied path vertex. -/
def generalBimatrixNodeScore (v : Fin 2 → List Bool) : List Bool :=
  bimatrixNodeOrientationWord ![generalBimatrixDimensionWord (v 0), v 1,
    generalBimatrixNodeData v 2,
    generalBimatrixDictionaryDeterminant (generalBimatrixNodeData v)]

theorem generalBimatrixNodeScore_cobham : Cobham generalBimatrixNodeScore := by
  apply Cobham.comp bimatrixNodeOrientationWord_cobham
  intro i
  fin_cases i
  · exact Cobham.comp generalBimatrixDimensionWord_cobham fun _ => .proj 0
  · exact .proj 1
  · exact generalBimatrixNodeData_cobham 2
  · exact Cobham.comp generalBimatrixDictionaryDeterminant_cobham generalBimatrixNodeData_cobham

/-- Recompute the distinguished source's orientation for calibration. -/
def generalBimatrixSourceScore (input : List Bool) : List Bool :=
  generalBimatrixNodeScore ![input, generalBimatrixNodeOrigin input]

theorem generalBimatrixSourceScore_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalBimatrixSourceScore (v 0) :=
  Cobham.comp₂ generalBimatrixNodeScore_cobham (.proj 0) generalBimatrixNodeOrigin_cobham

/-- Source-calibrated orientation chooses which involution is outgoing. -/
def generalBimatrixNodeColor (v : Fin 2 → List Bool) : List Bool :=
  binaryScoreColor ![generalBimatrixNodeScore v, generalBimatrixSourceScore (v 0)]

theorem generalBimatrixNodeColor_cobham : Cobham generalBimatrixNodeColor :=
  Cobham.comp₂ binaryScoreColor_cobham generalBimatrixNodeScore_cobham
    ((Cobham.comp generalBimatrixSourceScore_cobham
      (gs := fun _ : Fin 1 => fun v : Fin 2 → List Bool => v 0)
      (fun _ => .proj 0)).of_eq fun _ => rfl)

theorem generalBimatrixNodeColor_mem_FPn : FPn generalBimatrixNodeColor :=
  cobham_iff_FPn.mp generalBimatrixNodeColor_cobham

theorem generalBimatrixNodeRuler_length (input : List Bool) (hi : GeneralInstanceValid input) :
    (generalBimatrixNodeRuler input).length =
      4 * (generalRowCount input + generalColCount input) := by
  rw [generalBimatrixNodeRuler, (generalInstanceFlag_eq_true_iff input).mpr hi]
  simp only [caseBit₀_cons, Bool.cond_true, List.length_append,
    generalBimatrixDimensionWord_length]
  omega

theorem generalBimatrixNodeRuler_pos (input : List Bool) :
    0 < (generalBimatrixNodeRuler input).length := by
  by_cases hi : GeneralInstanceValid input
  · rw [generalBimatrixNodeRuler_length input hi]
    have := hi.1
    omega
  · have hf : generalInstanceFlag input = [false] := by
      rcases andBit_flag _ _ with ht | hf
      · exact (hi ((generalInstanceFlag_eq_true_iff input).mp ht)).elim
      · exact hf
    rw [generalBimatrixNodeRuler, hf]
    change 0 < 1
    decide

theorem generalBimatrixNodeOrigin_value (input : List Bool) (hi : GeneralInstanceValid input) :
    generalBimatrixNodeOrigin input =
      List.replicate (4 * (generalRowCount input + generalColCount input)) false := by
  rw [generalBimatrixNodeOrigin, padTo_eq_append _ _ (by simp)]
  simp only [List.length_nil, Nat.sub_zero, List.nil_append,
    generalBimatrixNodeRuler_length input hi]

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
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

end GameTheory.Complexity.Backend
