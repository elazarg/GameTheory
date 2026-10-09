import GameTheoryComplexity.Backend.BinaryWordMultiplication

/-! Signed binary multiplication and comparison with explicit sign headers.

The tail is an arbitrary little-endian magnitude. Empty words, sign-only words,
and padded negative zeros all denote zero. Operations use certified word
machines and never iterate the represented integer values.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- A true header denotes a negative little-endian magnitude. -/
def binarySignedValue (x : List Bool) : ℤ :=
  if x.headD false then -(Nat.fromBitsLE x.tail : ℤ) else (Nat.fromBitsLE x.tail : ℤ)

private def signedXor (x y : List Bool) : List Bool :=
  orBit (andBit x (notBit y)) (andBit (notBit x) y)

private theorem headFlag (x : List Bool) : bitAt [] x = [x.headD false] := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

private theorem signedXor_head (x y : List Bool) :
    signedXor (bitAt [] x) (bitAt [] y) = [(x.headD false).xor (y.headD false)] := by
  rw [headFlag, headFlag]
  generalize x.headD false = a
  generalize y.headD false = b
  cases a <;> cases b <;> rfl

/-- Multiply signed words by multiplying their tails and taking the exclusive-or sign. -/
def binarySignedMul (x y : List Bool) : List Bool :=
  signedXor (bitAt [] x) (bitAt [] y) ++ binaryWordMul x.tail y.tail

theorem binarySignedMul_value (x y : List Bool) :
    binarySignedValue (binarySignedMul x y) = binarySignedValue x * binarySignedValue y := by
  rw [binarySignedMul, signedXor_head]
  simp only [List.singleton_append, binarySignedValue, List.headD_cons, List.tail_cons,
    binaryWordMul_value, Nat.cast_mul]
  generalize x.headD false = a
  generalize y.headD false = b
  cases a <;> cases b <;> simp

theorem binarySignedMul_length (x y : List Bool) :
    (binarySignedMul x y).length ≤ 1 + y.length + 2 * x.length := by
  rw [binarySignedMul, signedXor_head]
  simp only [List.length_append, List.length_singleton]
  have h := binaryWordMul_length x.tail y.tail
  simp only [List.length_tail] at h
  omega

private def signedRawLT (x y : List Bool) : List Bool :=
  notBit (binaryCertificateLE ![y, x])

private theorem signedRawLT_value (x y : List Bool) :
    signedRawLT x y = [decide (Nat.fromBitsLE x < Nat.fromBitsLE y)] := by
  by_cases h : Nat.fromBitsLE y ≤ Nat.fromBitsLE x
  · have hn : ¬ Nat.fromBitsLE x < Nat.fromBitsLE y := by omega
    simp [signedRawLT, binaryCertificateLE_value, h, hn, notBit, caseBit₀]
  · have hl : Nat.fromBitsLE x < Nat.fromBitsLE y := by omega
    simp [signedRawLT, binaryCertificateLE_value, h, hl, notBit, caseBit₀]

private def effectiveNegative (x : List Bool) : List Bool :=
  andBit (bitAt [] x) (signedRawLT [] x.tail)

private theorem effectiveNegative_value (x : List Bool) :
    effectiveNegative x = [decide (binarySignedValue x < 0)] := by
  rw [effectiveNegative, headFlag, signedRawLT_value]
  rw [show Nat.fromBitsLE [] = 0 from rfl]
  unfold binarySignedValue
  generalize x.headD false = b
  cases b
  · simp [andBit, caseBit₀]
  · by_cases h : 0 < Nat.fromBitsLE x.tail
    · simp [andBit, caseBit₀, h]
    · have hz : Nat.fromBitsLE x.tail = 0 := by omega
      simp [andBit, caseBit₀, hz]

/-- Compare effective signs first and compare magnitudes in the appropriate direction. -/
def binarySignedLTFlag (x y : List Bool) : List Bool :=
  caseBit₀ (effectiveNegative x)
    (caseBit₀ (effectiveNegative y) (signedRawLT y.tail x.tail) [true])
    (caseBit₀ (effectiveNegative y) [false] (signedRawLT x.tail y.tail))

theorem binarySignedLTFlag_value (x y : List Bool) :
    binarySignedLTFlag x y = [decide (binarySignedValue x < binarySignedValue y)] := by
  rw [binarySignedLTFlag, effectiveNegative_value, effectiveNegative_value,
    signedRawLT_value, signedRawLT_value]
  unfold binarySignedValue
  generalize Nat.fromBitsLE x.tail = a
  generalize Nat.fromBitsLE y.tail = b
  generalize x.headD false = sx
  generalize y.headD false = sy
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  cases sx <;> cases sy <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [ha, hb, caseBit₀, Nat.pos_iff_ne_zero, not_lt_of_ge ha0, not_lt_of_ge hb0];
    omega

@[simp] theorem binarySignedLTFlag_length (x y : List Bool) :
    (binarySignedLTFlag x y).length = 1 := by rw [binarySignedLTFlag_value]; rfl

/-- Negation flips the sign header and preserves all magnitude padding. -/
def binarySignedNeg (x : List Bool) : List Bool := notBit (bitAt [] x) ++ x.tail

theorem binarySignedNeg_value (x : List Bool) :
    binarySignedValue (binarySignedNeg x) = -binarySignedValue x := by
  rw [binarySignedNeg, headFlag]
  unfold binarySignedValue
  generalize x.headD false = b
  cases b <;> simp [notBit, caseBit₀]

theorem binarySignedNeg_length (x : List Bool) : (binarySignedNeg x).length ≤ x.length + 1 := by
  have hf : (notBit (bitAt [] x)).length = 1 := by
    rw [headFlag]
    generalize x.headD false = b
    cases b <;> rfl
  simp only [binarySignedNeg, List.length_append, hf, List.length_tail]
  omega

private theorem headFn_cobham {r : ℕ} {x : (Fin r → List Bool) → List Bool}
    (hx : Cobham x) : Cobham fun v => bitAt [] (x v) :=
  (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) hx).of_eq fun _ => rfl

private theorem signedXorFn_cobham {r : ℕ} {x y : (Fin r → List Bool) → List Bool}
    (hx : Cobham x) (hy : Cobham y) : Cobham fun v => signedXor (x v) (y v) :=
  Cobham.orFn (Cobham.andFn hx (Cobham.notFn hy))
    (Cobham.andFn (Cobham.notFn hx) hy)

theorem binarySignedMul_cobham : Cobham fun v : Fin 2 → List Bool =>
    binarySignedMul (v 0) (v 1) :=
  Cobham.appendFn (signedXorFn_cobham (headFn_cobham (.proj 0)) (headFn_cobham (.proj 1)))
    ((Cobham.comp₂ binaryWordMul_cobham (Cobham.tailFn (.proj 0))
      (Cobham.tailFn (.proj 1))).of_eq fun _ => rfl)

theorem binarySignedMul_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binarySignedMul (v 0) (v 1)) :=
  cobham_iff_FPn.mp binarySignedMul_cobham

private theorem signedRawLTFn_cobham {r : ℕ} {x y : (Fin r → List Bool) → List Bool}
    (hx : Cobham x) (hy : Cobham y) : Cobham fun v => signedRawLT (x v) (y v) :=
  Cobham.notFn ((Cobham.comp₂ binaryCertificateLE_cobham hy hx).of_eq fun _ => rfl)

private theorem effectiveNegativeFn_cobham {r : ℕ} {x : (Fin r → List Bool) → List Bool}
    (hx : Cobham x) : Cobham fun v => effectiveNegative (x v) :=
  Cobham.andFn (headFn_cobham hx)
    (signedRawLTFn_cobham (Cobham.const []) (Cobham.tailFn hx))

theorem binarySignedLTFlag_cobham : Cobham fun v : Fin 2 → List Bool =>
    binarySignedLTFlag (v 0) (v 1) :=
  Cobham.iteFn (effectiveNegativeFn_cobham (.proj 0))
    (Cobham.iteFn (effectiveNegativeFn_cobham (.proj 1))
      (signedRawLTFn_cobham (Cobham.tailFn (.proj 1)) (Cobham.tailFn (.proj 0)))
      (Cobham.const [true]))
    (Cobham.iteFn (effectiveNegativeFn_cobham (.proj 1)) (Cobham.const [false])
      (signedRawLTFn_cobham (Cobham.tailFn (.proj 0)) (Cobham.tailFn (.proj 1))))

theorem binarySignedLTFlag_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binarySignedLTFlag (v 0) (v 1)) :=
  cobham_iff_FPn.mp binarySignedLTFlag_cobham

theorem binarySignedNeg_cobham : Cobham fun v : Fin 1 → List Bool => binarySignedNeg (v 0) :=
  Cobham.appendFn (Cobham.notFn (headFn_cobham (.proj 0))) (Cobham.tailFn (.proj 0))

theorem binarySignedNeg_mem_FPn : FPn (fun v : Fin 1 → List Bool => binarySignedNeg (v 0)) :=
  cobham_iff_FPn.mp binarySignedNeg_cobham

end GameTheory.Complexity.Backend
