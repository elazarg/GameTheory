module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Foundations.Data.Nat.Bits
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Fixed-width little-endian arithmetic has direct polynomial-time machine
certificates. The operands are decoded as binary naturals, so their values may
be exponential in their lengths. Output widths and indexing are computed in
unary, charging for every emitted bit, including padding and the final carry.
-/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

/-- Add two little-endian words, reserving one bit beyond the longer operand. -/
def binaryCertificateAdd (v : Fin 2 → List Bool) : List Bool :=
  lowBits (max (v 0).length (v 1).length + 1) (ofBits (v 0) + ofBits (v 1))

/-- Binary addition charges the encoded operands and the complete padded output. -/
@[fun_prop]
theorem binaryCertificateAdd_polyTime :
    ComputableInPolyTime binaryCertificateAdd (encPi encBits) encBits := by
  have hx : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hy : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hlenx := ComputableInPolyTime.length_bits_comp hx
  have hleny := ComputableInPolyTime.length_bits_comp hy
  have hmax := ComputableTidilyInPolyTime.unary_max.comp (hlenx.tidy.prod hleny.tidy)
  have hwidth : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => max (v 0).length (v 1).length + 1)
      (encPi encBits) encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_add.comp (hmax.prod (.const 1)))
  have hvaluex := ComputableInPolyTime.bitsToNat.comp hx
  have hvaluey := ComputableInPolyTime.bitsToNat.comp hy
  have hsum : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ofBits (v 0) + ofBits (v 1))
      (encPi encBits) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_add.comp (hvaluex.tidy.prod hvaluey.tidy))
  exact ComputableInPolyTime.bitsLow hwidth hsum

/-- The full sum has one more bit than the longer operand, including leading zeros. -/
theorem binaryCertificateAdd_length (x y : List Bool) :
    (binaryCertificateAdd ![x, y]).length = max x.length y.length + 1 := by
  simp [binaryCertificateAdd]

/-- The extra output bit prevents arithmetic overflow. -/
theorem binaryCertificateAdd_value (x y : List Bool) :
    ofBits (binaryCertificateAdd ![x, y]) = ofBits x + ofBits y := by
  have hx : ofBits x < 2 ^ x.length := Nat.foldr_bit_lt x
  have hy : ofBits y < 2 ^ y.length := Nat.foldr_bit_lt y
  have hx' : ofBits x < 2 ^ max x.length y.length :=
    hx.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hy' : ofBits y < 2 ^ max x.length y.length :=
    hy.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  have hsum : ofBits x + ofBits y < 2 ^ (max x.length y.length + 1) := by
    rw [pow_succ]
    omega
  exact Nat.foldr_bit_testBit (Nat.size_le.mpr hsum)

/-- The adder emits exactly the padded low-order digits of the full sum. -/
theorem binaryCertificateAdd_eq_lowBits (x y : List Bool) :
    binaryCertificateAdd ![x, y] =
      lowBits (max x.length y.length + 1) (ofBits x + ofBits y) := rfl

/-- Compare little-endian unsigned words, retaining the singleton flag convention. -/
def binaryCertificateLE (v : Fin 2 → List Bool) : List Bool :=
  [decide (ofBits (v 0) ≤ ofBits (v 1))]

/-- Unsigned comparison uses binary arithmetic and emits exactly one result bit. -/
@[fun_prop]
theorem binaryCertificateLE_polyTime :
    ComputableInPolyTime binaryCertificateLE (encPi encBits) encBits := by
  have hx : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hy : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hvaluex := ComputableInPolyTime.bitsToNat.comp hx
  have hvaluey := ComputableInPolyTime.bitsToNat.comp hy
  have htest : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => decide (ofBits (v 0) ≤ ofBits (v 1)))
      (encPi encBits) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.binary_le.comp (hvaluex.tidy.prod hvaluey.tidy))
  exact ComputableInPolyTime.bitsCons htest (.const [])

/-- Unsigned comparison agrees with the decoded mathematical values. -/
theorem binaryCertificateLE_value (x y : List Bool) :
    binaryCertificateLE ![x, y] = [decide (ofBits x ≤ ofBits y)] := rfl

/-- The comparison output is a Boolean flag. -/
theorem binaryCertificateLE_length (x y : List Bool) :
    (binaryCertificateLE ![x, y]).length = 1 := rfl

/-- The comparison flag accepts exactly unsigned less-than-or-equal. -/
theorem binaryCertificateLE_eq_true_iff (x y : List Bool) :
    binaryCertificateLE ![x, y] = [true] ↔ ofBits x ≤ ofBits y := by
  simp [binaryCertificateLE_value]

end GameTheory.Complexity.Backend
