module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

@[expose] public section

/-! Unsigned word subtraction saturates at zero. Strict underflow returns the
empty word; all other results retain exactly the greater operand width, including
high zero padding. Binary arithmetic and unary widths have separate certificates. -/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

/-- Subtract unsigned words. Underflow is empty; other results keep the full operand width. -/
def binaryWordSub (x y : List Bool) : List Bool :=
  if ofBits x < ofBits y then []
  else lowBits (max x.length y.length) (ofBits x - ofBits y)

/-- Exact output width distinguishes strict underflow from a padded zero result. -/
theorem binaryWordSub_length_eq (x y : List Bool) :
    (binaryWordSub x y).length = if ofBits x < ofBits y then 0 else max x.length y.length := by
  unfold binaryWordSub
  split <;> simp

/-- The output fits the wider operand, including arbitrary high zero padding. -/
theorem binaryWordSub_length (x y : List Bool) :
    (binaryWordSub x y).length ≤ max x.length y.length := by
  rw [binaryWordSub_length_eq]
  split <;> omega

/-- The decoded result is exact natural-number saturating subtraction. -/
theorem binaryWordSub_value (x y : List Bool) :
    ofBits (binaryWordSub x y) = ofBits x - ofBits y := by
  by_cases h : ofBits x < ofBits y
  · rw [binaryWordSub, ite_eq_left h]
    exact (Nat.sub_eq_zero_of_le h.le).symm
  · rw [binaryWordSub, ite_eq_right h]
    have hx : ofBits x < 2 ^ x.length := Nat.foldr_bit_lt x
    have hdiff : ofBits x - ofBits y < 2 ^ max x.length y.length :=
      (Nat.sub_le _ _).trans_lt
        (hx.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
    exact Nat.foldr_bit_testBit (Nat.size_le.mpr hdiff)

/-- Strict underflow returns exactly the empty word, rather than wrapped low bits. -/
@[simp] theorem binaryWordSub_eq_nil_of_lt (x y : List Bool) (h : ofBits x < ofBits y) :
    binaryWordSub x y = [] := by simp [binaryWordSub, h]

/-- Non-underflow retains every padding bit up to the maximum operand width. -/
theorem binaryWordSub_eq_lowBits_of_le (x y : List Bool) (h : ofBits y ≤ ofBits x) :
    binaryWordSub x y = lowBits (max x.length y.length) (ofBits x - ofBits y) := by
  simp [binaryWordSub, Nat.not_lt.mpr h]

/-- Binary subtraction, the underflow guard, and output writing are all certified uniformly. -/
@[fun_prop] theorem binaryWordSub_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binaryWordSub (x a) (y a)) input encBits := by
  have hlenx := ComputableInPolyTime.length_bits_comp hx
  have hleny := ComputableInPolyTime.length_bits_comp hy
  have hwidth : ComputableInPolyTime (fun a => max (x a).length (y a).length)
      input encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_max.comp (hlenx.tidy.prod hleny.tidy))
  have hvaluex := ComputableInPolyTime.bitsToNat.comp hx
  have hvaluey := ComputableInPolyTime.bitsToNat.comp hy
  have hdifference : ComputableInPolyTime (fun a => ofBits (x a) - ofBits (y a))
      input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_sub.comp (hvaluex.tidy.prod hvaluey.tidy))
  have hguard : ComputableInPolyTime (fun a => decide (ofBits (x a) < ofBits (y a)))
      input encBool :=
    .of_tidy (ComputableTidilyInPolyTime.binary_lt.comp (hvaluex.tidy.prod hvaluey.tidy))
  exact ComputableInPolyTime.ite_decide hguard (.const [])
    (ComputableInPolyTime.bitsLow hwidth hdifference)

end GameTheory.Complexity.Backend
