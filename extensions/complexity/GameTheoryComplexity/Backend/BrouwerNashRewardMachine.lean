module

public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BinarySignedArithmetic
public import Complexity.Foundations.Data.BitString.Counter
public import GameTheory.Math.GridBrouwerErrorBudget

@[expose] public section

/-! Integer reward words have polynomial bit length in their precision and
dimension rulers. The reward's dyadic exponent is written as explicit zero
padding, while its quadratic factor is computed by binary word arithmetic. -/

namespace GameTheory.Complexity.Backend.BrouwerNashRewardMachine

open Cslib.BitString Turing.MultiTapeTM

/-- The dyadic exponent clock contains one true bit for each padding position. -/
def clock (precision dimension : List Bool) : List Bool :=
  List.replicate (100 * (precision.length + dimension.length + 10)) true

private def factor (dimension : List Bool) : List Bool :=
  binaryCertificateAdd ![binaryWordMul (binaryLengthWord dimension)
    (binaryWordMul (binaryLengthWord dimension) [false, true, true, false, false, true, true]),
      [true]]

/-- Positive signed reward (102 k² + 1) 2^Q retains its full magnitude padding. -/
def reward (precision dimension : List Bool) : List Bool :=
  false :: (List.replicate (clock precision dimension).length false ++
    binaryCertificateAdd ![binaryWordMul (binaryLengthWord dimension)
      (binaryWordMul (binaryLengthWord dimension) [false, true, true, false, false, true, true]),
        [true]])

@[simp] theorem clock_length (precision dimension : List Bool) :
    (clock precision dimension).length = 100 * (precision.length + dimension.length + 10) := by
  simp [clock]

private theorem factor_value (dimension : List Bool) :
    ofBits (factor dimension) = dimension.length * (100 * dimension.length + 2 * dimension.length) + 1 := by
  rw [factor, binaryCertificateAdd_value, binaryWordMul_value, binaryWordMul_value,
    binaryLengthWord_value]
  change dimension.length * (dimension.length * 102) + 1 = _
  ring

/-- The emitted signed word denotes the exact integer reward schedule. -/
theorem reward_value (precision dimension : List Bool) :
    binarySignedValue (reward precision dimension) =
      (dimension.length * (100 * dimension.length + 2 * dimension.length) + 1 : ℤ) *
        2 ^ (100 * (precision.length + dimension.length + 10)) := by
  change (ofBits (List.replicate (clock precision dimension).length false ++ factor dimension) : ℤ) = _
  have hvalue : ofBits (List.replicate (clock precision dimension).length false ++ factor dimension) =
      2 ^ (clock precision dimension).length * ofBits (factor dimension) := by
    unfold ofBits
    rw [← lsbValue_eq_foldr_bit, lsbValue_append, lsbValue_replicate_false,
      List.length_replicate, zero_add, lsbValue_eq_foldr_bit]
  rw [hvalue, factor_value, clock_length]
  push_cast
  exact mul_comm _ _

/-- Matching rewards strictly dominate perturbations, including empty rulers. -/
theorem reward_dominates (precision dimension : List Bool) :
    (dimension.length : ℤ) * (100 * dimension.length + 2 * dimension.length) <
      binarySignedValue (reward precision dimension) := by
  rw [reward_value]
  have hk : (0 : ℤ) ≤ dimension.length := Nat.cast_nonneg _
  have hs : 0 ≤ (dimension.length : ℤ) * (100 * dimension.length + 2 * dimension.length) := by
    nlinarith only [hk]
  have hp : (1 : ℤ) ≤ 2 ^ (100 * (precision.length + dimension.length + 10)) :=
    one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤
    (dimension.length : ℤ) * (100 * dimension.length + 2 * dimension.length) + 1 by omega)
  rw [mul_one] at hh
  omega

/-- Reward words have linear bit length in the two supplied rulers. -/
theorem reward_length (precision dimension : List Bool) :
    (reward precision dimension).length ≤ 100 * (precision.length + dimension.length + 10) +
      4 * dimension.length + 13 := by
  have hn := binaryLengthWord_length dimension
  have hs := binaryWordMul_length (binaryLengthWord dimension)
    [false, true, true, false, false, true, true]
  have hm := binaryWordMul_length (binaryLengthWord dimension)
    (binaryWordMul (binaryLengthWord dimension) [false, true, true, false, false, true, true])
  simp only [List.length_cons, List.length_nil] at hs
  change (false :: (List.replicate (clock precision dimension).length false ++ factor dimension)).length ≤ _
  simp only [ List.length_cons, List.length_append, List.length_replicate,
    clock_length, factor, binaryCertificateAdd_length, List.length_nil]
  omega

/-- The emitted reward schedule bounds the normalized gate error. -/
theorem reward_error_bound (precision dimension : List Bool) (hk : 1 ≤ dimension.length) :
    0 ≤ (dimension.length : ℚ) * (102 * dimension.length) /
      (binarySignedValue (reward precision dimension) : ℚ) ∧
    (dimension.length : ℚ) * (102 * dimension.length) /
      (binarySignedValue (reward precision dimension) : ℚ) ≤
        1 / (2 : ℚ) ^ (100 * (precision.length + dimension.length + 10)) := by
  rw [reward_value]
  exact GameTheory.Math.bimatrix_integer_reward_error_bound dimension.length
    (100 * (precision.length + dimension.length + 10)) hk

/-- Exponent clocks retain the actual encoding of both ruler producers. -/
@[fun_prop] theorem clock_polyTime {Input : Type} {input : Input ↪ List Bool}
    {precision dimension : Input → List Bool}
    (hp : ComputableInPolyTime precision input encBits)
    (hd : ComputableInPolyTime dimension input encBits) :
    ComputableInPolyTime (fun a => clock (precision a) (dimension a)) input encBits := by
  have hsum := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.length_bits_comp hp) (ComputableInPolyTime.length_bits_comp hd)
  have hwidth := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 100)
    (ComputableInPolyTime.unary_add' hsum (ComputableInPolyTime.const 10))
  exact (ComputableInPolyTime.bitsReplicate true).comp hwidth

private theorem factor_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension : Input → List Bool} (hd : ComputableInPolyTime dimension input encBits) :
    ComputableInPolyTime (fun a => factor (dimension a)) input encBits := by
  have hn := binaryLengthWord_polyTime.comp hd
  have hs := binaryWordMul_polyTime hn
    (ComputableInPolyTime.const [false, true, true, false, false, true, true])
  have hm := binaryWordMul_polyTime hn hs
  have hargs : ComputableInPolyTime (fun a : Input =>
      ![binaryWordMul (binaryLengthWord (dimension a))
        (binaryWordMul (binaryLengthWord (dimension a))
          [false, true, true, false, false, true, true]), [true]])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hm
    · exact ComputableInPolyTime.const [true]
  exact binaryCertificateAdd_polyTime.comp hargs

/-- Binary factor arithmetic and explicit dyadic padding have a direct native certificate. -/
@[fun_prop] theorem reward_polyTime {Input : Type} {input : Input ↪ List Bool}
    {precision dimension : Input → List Bool}
    (hp : ComputableInPolyTime precision input encBits)
    (hd : ComputableInPolyTime dimension input encBits) :
    ComputableInPolyTime (fun a => reward (precision a) (dimension a)) input encBits := by
  have hzero := (ComputableInPolyTime.bitsReplicate false).comp
    (ComputableInPolyTime.length_bits_comp (clock_polyTime hp hd))
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
    (ComputableInPolyTime.bitsAppend hzero (factor_polyTime hd))

end GameTheory.Complexity.Backend.BrouwerNashRewardMachine
