import GameTheoryComplexity.Backend.BinarySignedArithmetic
import GameTheoryComplexity.Backend.BinaryWordSubtraction

/-! Exact signed addition using bit-length-bounded magnitude arithmetic.
Opposite signs subtract the smaller magnitude from the larger; equal signs
retain the sign and add magnitudes. Padded and negative-zero inputs are accepted.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private def sameSignFlag (x y : List Bool) : List Bool :=
  orBit (andBit (bitAt [] x) (bitAt [] y))
    (andBit (notBit (bitAt [] x)) (notBit (bitAt [] y)))

/-- Add two sign-header, little-endian-magnitude words without numeric-value loops. -/
def binarySignedAdd (x y : List Bool) : List Bool :=
  caseBit₀ (sameSignFlag x y)
    (bitAt [] x ++ binaryCertificateAdd ![x.tail, y.tail])
    (caseBit₀ (binaryCertificateLE ![y.tail, x.tail])
      (bitAt [] x ++ binaryWordSub x.tail y.tail)
      (bitAt [] y ++ binaryWordSub y.tail x.tail))

private theorem headFlag (x : List Bool) : bitAt [] x = [x.headD false] := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

private theorem sameSignFlag_value (x y : List Bool) :
    sameSignFlag x y = [decide (x.headD false = y.headD false)] := by
  rw [sameSignFlag, headFlag, headFlag]
  generalize x.headD false = a
  generalize y.headD false = b
  cases a <;> cases b <;> rfl

/-- Signed addition is exact for arbitrary padding and either representation of zero. -/
theorem binarySignedAdd_value (x y : List Bool) :
    binarySignedValue (binarySignedAdd x y) = binarySignedValue x + binarySignedValue y := by
  rw [binarySignedAdd, sameSignFlag_value, headFlag, headFlag, binaryCertificateLE_value]
  unfold binarySignedValue
  generalize x.headD false = sx
  generalize y.headD false = sy
  cases sx <;> cases sy <;>
    by_cases h : Nat.fromBitsLE y.tail ≤ Nat.fromBitsLE x.tail <;>
    simp [caseBit₀, h, binaryCertificateAdd_value, binaryWordSub_value] <;> omega

/-- The output length is linear in the input word lengths. -/
theorem binarySignedAdd_length (x y : List Bool) :
    (binarySignedAdd x y).length ≤ max x.length y.length + 2 := by
  rw [binarySignedAdd, sameSignFlag_value, headFlag, headFlag, binaryCertificateLE_value]
  have hs := binaryWordSub_length x.tail y.tail
  have ht := binaryWordSub_length y.tail x.tail
  generalize x.headD false = sx
  generalize y.headD false = sy
  cases sx <;> cases sy <;>
    by_cases h : Nat.fromBitsLE y.tail ≤ Nat.fromBitsLE x.tail <;>
    simp [h, caseBit₀, binaryCertificateAdd_length] <;>
    simp only [List.length_tail] at * <;> omega

/-- Signed addition has a compositional Cobham certificate. -/
theorem binarySignedAdd_cobham : Cobham fun v : Fin 2 → List Bool =>
    binarySignedAdd (v 0) (v 1) := by
  have hx : Cobham fun v : Fin 2 → List Bool => bitAt [] (v 0) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 0)
  have hy : Cobham fun v : Fin 2 → List Bool => bitAt [] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1)
  have tx : Cobham fun v : Fin 2 → List Bool => (v 0).tail := Cobham.tailFn (.proj 0)
  have ty : Cobham fun v : Fin 2 → List Bool => (v 1).tail := Cobham.tailFn (.proj 1)
  have hs : Cobham fun v : Fin 2 → List Bool => sameSignFlag (v 0) (v 1) :=
    Cobham.orFn (Cobham.andFn hx hy) (Cobham.andFn (Cobham.notFn hx) (Cobham.notFn hy))
  exact (Cobham.iteFn hs
    (Cobham.appendFn hx (Cobham.comp₂ binaryCertificateAdd_cobham tx ty))
    (Cobham.iteFn (Cobham.comp₂ binaryCertificateLE_cobham ty tx)
      (Cobham.appendFn hx (Cobham.comp₂ binaryWordSub_cobham tx ty))
      (Cobham.appendFn hy (Cobham.comp₂ binaryWordSub_cobham ty tx)))).of_eq fun _ => rfl

/-- Signed addition belongs to polynomial time at arity two. -/
theorem binarySignedAdd_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binarySignedAdd (v 0) (v 1)) :=
  cobham_iff_FPn.mp binarySignedAdd_cobham

/-- Subtract signed words by composing addition and header negation. -/
def binarySignedSub (x y : List Bool) : List Bool := binarySignedAdd x (binarySignedNeg y)

theorem binarySignedSub_value (x y : List Bool) :
    binarySignedValue (binarySignedSub x y) = binarySignedValue x - binarySignedValue y := by
  rw [binarySignedSub, binarySignedAdd_value, binarySignedNeg_value, sub_eq_add_neg]

theorem binarySignedSub_length (x y : List Bool) :
    (binarySignedSub x y).length ≤ max x.length y.length + 3 := by
  have h := binarySignedAdd_length x (binarySignedNeg y)
  have hn := binarySignedNeg_length y
  unfold binarySignedSub
  omega

theorem binarySignedSub_cobham : Cobham fun v : Fin 2 → List Bool =>
    binarySignedSub (v 0) (v 1) := by
  exact (Cobham.comp₂ binarySignedAdd_cobham (.proj 0)
    (Cobham.comp binarySignedNeg_cobham fun _ => Cobham.proj 1)).of_eq fun _ => rfl

theorem binarySignedSub_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binarySignedSub (v 0) (v 1)) :=
  cobham_iff_FPn.mp binarySignedSub_cobham

end GameTheory.Complexity.Backend
