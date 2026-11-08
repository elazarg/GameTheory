module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Tactic.Ring

@[expose] public section

/-! Unsigned multiplication uses binary natural arithmetic and retains every
padding bit of the word multiplication convention. A unary width fold charges
those bits separately from the potentially exponential operand values. -/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

private def mulWidthStep (operandWidth count : ℕ) (bit : Bool) : ℕ :=
  if bit then max (count + 1) operandWidth + 1 else count + 1

/-- The exact output width of shift-and-add multiplication, including padding. -/
def binaryWordMulWidth (x : List Bool) (operandWidth : ℕ) : ℕ :=
  x.foldr (fun bit count => if bit then max (count + 1) operandWidth + 1 else count + 1) 0

private theorem mulWidth_bound (x : List Bool) (operandWidth : ℕ) :
    binaryWordMulWidth x operandWidth ≤ operandWidth + 2 * x.length := by
  induction x with
  | nil => simp [binaryWordMulWidth]
  | cons bit x ih =>
    cases bit <;> simp [binaryWordMulWidth] at * <;> omega

private theorem wordValue_cons (bit : Bool) (word : List Bool) :
    ofBits (bit :: word) = bit.toNat + 2 * ofBits word := by
  simp only [ofBits, List.foldr_cons, Nat.bit_val]
  omega

private theorem mulWidth_fits (x y : List Bool) :
    ofBits x * ofBits y < 2 ^ binaryWordMulWidth x y.length := by
  induction x with
  | nil => simp [binaryWordMulWidth, ofBits]
  | cons bit x ih =>
    cases bit
    · change ofBits (false :: x) * ofBits y < 2 ^ (binaryWordMulWidth x y.length + 1)
      rw [wordValue_cons, Bool.toNat_false, zero_add, pow_succ]
      have hproduct : (2 * ofBits x) * ofBits y = 2 * (ofBits x * ofBits y) := by ring
      rw [hproduct]
      omega
    · have hdouble : 2 * (ofBits x * ofBits y) < 2 ^ (binaryWordMulWidth x y.length + 1) := by
        rw [pow_succ]
        omega
      have hleft : 2 * (ofBits x * ofBits y) <
          2 ^ max (binaryWordMulWidth x y.length + 1) y.length :=
        hdouble.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      have hy : ofBits y < 2 ^ y.length := Nat.foldr_bit_lt y
      have hright : ofBits y < 2 ^ max (binaryWordMulWidth x y.length + 1) y.length :=
        hy.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
      change ofBits (true :: x) * ofBits y <
        2 ^ (max (binaryWordMulWidth x y.length + 1) y.length + 1)
      rw [wordValue_cons, Bool.toNat_true, pow_succ]
      have hproduct : (1 + 2 * ofBits x) * ofBits y =
          ofBits y + 2 * (ofBits x * ofBits y) := by ring
      rw [hproduct]
      omega

/-- Multiply little-endian words, preserving their bit-recursive output width exactly. -/
def binaryWordMul (x y : List Bool) : List Bool :=
  lowBits (binaryWordMulWidth x y.length) (ofBits x * ofBits y)

@[simp] theorem binaryWordMul_nil (y : List Bool) : binaryWordMul [] y = [] := rfl

/-- Multiplication is exact on empty, padded and unequal-width operands. -/
theorem binaryWordMul_value (x y : List Bool) :
    ofBits (binaryWordMul x y) = ofBits x * ofBits y := by
  exact Nat.foldr_bit_testBit (Nat.size_le.mpr (mulWidth_fits x y))

/-- Every original zero-bit step retains its exact padding byte. -/
@[simp] theorem binaryWordMul_false (x y : List Bool) :
    binaryWordMul (false :: x) y = false :: binaryWordMul x y := by
  apply lsbValue_injective
  · simp [binaryWordMul, binaryWordMulWidth]
  · simp only [lsbValue_eq_foldr_bit]
    change ofBits (binaryWordMul (false :: x) y) = ofBits (false :: binaryWordMul x y)
    simp only [binaryWordMul_value, wordValue_cons, Bool.toNat_false]
    ring

/-- Every original one-bit step retains the exact addition width, including carry padding. -/
@[simp] theorem binaryWordMul_true (x y : List Bool) :
    binaryWordMul (true :: x) y =
      binaryCertificateAdd ![false :: binaryWordMul x y, y] := by
  apply lsbValue_injective
  · simp [binaryWordMul, binaryWordMulWidth, binaryCertificateAdd_length]
  · simp only [lsbValue_eq_foldr_bit]
    change ofBits (binaryWordMul (true :: x) y) =
      ofBits (binaryCertificateAdd ![false :: binaryWordMul x y, y])
    simp only [binaryWordMul_value, binaryCertificateAdd_value, wordValue_cons,
      Bool.toNat_true, Bool.toNat_false]
    ring

/-- The complete multiplication output has length linear in the input word lengths. -/
theorem binaryWordMul_length (x y : List Bool) :
    (binaryWordMul x y).length ≤ y.length + 2 * x.length := by
  simpa only [binaryWordMul, length_lowBits] using mulWidth_bound x y.length

/-- The width fold and binary multiplication compose uniformly over any encoded input. -/
@[fun_prop] theorem binaryWordMul_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binaryWordMul (x a) (y a)) input encBits := by
  have hpar := ComputableInPolyTime.length_bits_comp hy
  have hlist := ComputableInPolyTime.bitsReverse.comp hx
  have hstep : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × Bool => mulWidthStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBool) encUnary := by
    apply ComputableInPolyTime.of_tidy
    unfold mulWidthStep
    fun_prop
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (step := mulWidthStep) hpar hlist (ComputableInPolyTime.const 0) hstep
    (hpar.polyBounded.add (.const 2))
    (fun a count bit _ => by
      simp only [encUnary_apply, List.length_replicate]
      cases bit <;> simp [mulWidthStep]
      all_goals omega)
  have hwidth : ComputableInPolyTime (fun a => binaryWordMulWidth (x a) (y a).length)
      input encUnary := by
    simpa only [Function.comp_def, List.foldl_reverse, binaryWordMulWidth, mulWidthStep] using hfold
  have hvaluex := ComputableInPolyTime.bitsToNat.comp hx
  have hvaluey := ComputableInPolyTime.bitsToNat.comp hy
  have hproduct : ComputableInPolyTime (fun a => ofBits (x a) * ofBits (y a))
      input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_mul.comp (hvaluex.tidy.prod hvaluey.tidy))
  exact ComputableInPolyTime.bitsLow hwidth hproduct

end GameTheory.Complexity.Backend
