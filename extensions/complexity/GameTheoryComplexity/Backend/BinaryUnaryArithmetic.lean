module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! Certified arithmetic on explicit rulers, using their unary lengths. -/
namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

/-- A unary ruler of half the input length, rounded down. -/
def binaryHalfRuler (word : List Bool) : List Bool :=
  List.replicate (word.length / 2) true

theorem binaryHalfRuler_value (word : List Bool) :
    binaryHalfRuler word = List.replicate (word.length / 2) true := rfl

@[simp] theorem binaryHalfRuler_length (word : List Bool) :
    (binaryHalfRuler word).length = word.length / 2 := by simp [binaryHalfRuler]

@[fun_prop] theorem binaryHalfRuler_polyTime :
    ComputableInPolyTime binaryHalfRuler encBits encBits := by
  have hword : ComputableInPolyTime (fun word : List Bool => word) encBits encBits := .id'
  have hlen := ComputableInPolyTime.length_bits_comp hword
  have hhalf := (ComputableInPolyTime.unary_div_const 2).comp hlen
  exact (ComputableInPolyTime.bitsReplicate true).comp hhalf

/-- A singleton flag recording whether a ruler has odd length. -/
def binaryLengthParity (word : List Bool) : List Bool :=
  [decide (word.length % 2 = 1)]

theorem binaryLengthParity_value (word : List Bool) :
    binaryLengthParity word = [decide (word.length % 2 = 1)] := rfl

@[simp] theorem binaryLengthParity_length (word : List Bool) :
    (binaryLengthParity word).length = 1 := rfl

@[fun_prop] theorem binaryLengthParity_polyTime :
    ComputableInPolyTime binaryLengthParity encBits encBits := by
  have hword : ComputableInPolyTime (fun word : List Bool => word) encBits encBits := .id'
  have hlen := ComputableInPolyTime.length_bits_comp hword
  have hmod := ComputableInPolyTime.unary_mod.comp (hlen.prod (.const 2))
  have heq : ComputableInPolyTime (fun word : List Bool =>
      decide (word.length % 2 = 1)) encBits encBool :=
    ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hmod.tidy.prod (.const 1)))
  exact ComputableInPolyTime.bitsCons heq (.const [])

end GameTheory.Complexity.Backend
