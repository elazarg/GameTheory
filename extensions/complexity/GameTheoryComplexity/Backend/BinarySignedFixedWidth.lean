import GameTheoryComplexity.Backend.BinarySignedAddition

/-! Fixed-width signed arithmetic with a length ruler.

Every result is stored in exactly the ruler's width, so repeated arithmetic cannot
accumulate representation padding. Values fitting the magnitude capacity are
preserved; larger magnitudes are truncated explicitly.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem fromBitsLE_take (w : ℕ) (x : List Bool) :
    Nat.fromBitsLE (x.take w) = Nat.fromBitsLE x % 2 ^ w := by
  by_cases hw : w ≤ x.length
  · have hl : (x.take w).length = w := by simp [List.length_take, hw]
    have hb : Nat.fromBitsLE (x.take w) < 2 ^ w := by
      simpa only [hl] using Nat.fromBitsLE_lt_pow_length (x.take w)
    have he : Nat.fromBitsLE x = Nat.fromBitsLE (x.take w) +
        2 ^ w * Nat.fromBitsLE (x.drop w) := by
      simpa only [hl, List.take_append_drop] using fromBitsLE_append (x.take w) (x.drop w)
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
  · have hl : x.length ≤ w := by omega
    have hb : Nat.fromBitsLE x < 2 ^ w :=
      (Nat.fromBitsLE_lt_pow_length x).trans_le (Nat.pow_le_pow_right (by decide) hl)
    simp [List.take_of_length_le hl, Nat.mod_eq_of_lt hb]

private theorem fromBitsLE_zero (w : ℕ) :
    Nat.fromBitsLE (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]

theorem padTo_fromBitsLE (ruler x : List Bool) :
    Nat.fromBitsLE (padTo ruler x) = Nat.fromBitsLE x % 2 ^ ruler.length := by
  rw [padTo, fromBitsLE_take, fromBitsLE_append, fromBitsLE_zero]
  simp

private theorem headFlag (x : List Bool) : bitAt [] x = [x.headD false] := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

/-- Normalize a signed word to exactly the total field width, including its header. -/
def binarySignedFixed (ruler x : List Bool) : List Bool :=
  padTo ruler (bitAt [] x ++ padTo ruler.tail x.tail)

@[simp] theorem binarySignedFixed_length (ruler x : List Bool) :
    (binarySignedFixed ruler x).length = ruler.length := padTo_length _ _

/-- Normalizing an already sized field preserves its bytes, including negative zero. -/
theorem binarySignedFixed_eq_of_length (ruler x : List Bool) (hx : x.length = ruler.length) :
    binarySignedFixed ruler x = x := by
  cases x with
  | nil =>
    have hr : ruler = [] := by simpa using hx.symm
    subst ruler
    rfl
  | cons b x =>
    have ht : x.length = ruler.tail.length := by simp only [List.length_tail]; simp at hx; omega
    have hp : padTo ruler.tail x = x := by
      rw [padTo_eq_append _ _ ht.le, ← ht, Nat.sub_self]
      simp
    rw [binarySignedFixed, headFlag, List.headD_cons, List.singleton_append, List.tail_cons, hp]
    rw [padTo_eq_append _ _ hx.le, ← hx, Nat.sub_self]
    simp

theorem binarySignedValue_natAbs (x : List Bool) :
    (binarySignedValue x).natAbs = Nat.fromBitsLE x.tail := by
  unfold binarySignedValue
  split <;> simp

/-- The stored word preserves exactly the representable magnitude, with the original sign. -/
theorem binarySignedFixed_value (ruler x : List Bool) (hr : 0 < ruler.length)
    (hx : (binarySignedValue x).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixed ruler x) = binarySignedValue x := by
  have hlen : (bitAt [] x ++ padTo ruler.tail x.tail).length = ruler.length := by
    rw [headFlag]
    simp
    omega
  have he : padTo ruler (bitAt [] x ++ padTo ruler.tail x.tail) =
      bitAt [] x ++ padTo ruler.tail x.tail := by
    rw [padTo_eq_append _ _ hlen.le, hlen, Nat.sub_self]
    simp
  rw [binarySignedFixed, he, headFlag]
  simp only [List.singleton_append, binarySignedValue, List.headD_cons, List.tail_cons]
  have hmag : Nat.fromBitsLE x.tail < 2 ^ ruler.tail.length := by
    simpa only [binarySignedValue_natAbs, List.length_tail] using hx
  rw [padTo_fromBitsLE, Nat.mod_eq_of_lt hmag]
  rfl

/-- Fixed-width storage preserves zero, including when its ruler is empty. -/
theorem binarySignedFixed_value_zero (ruler x : List Bool)
    (hx : binarySignedValue x = 0) : binarySignedValue (binarySignedFixed ruler x) = 0 := by
  cases ruler with
  | nil => rfl
  | cons b ruler =>
    rw [binarySignedFixed_value (b :: ruler) x (by simp) (by rw [hx]; simp), hx]

theorem binarySignedFixed_cobham : Cobham fun v : Fin 2 → List Bool =>
    binarySignedFixed (v 0) (v 1) :=
  Cobham.padFn (.proj 0) (Cobham.appendFn
    (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1))
    (Cobham.padFn (Cobham.tailFn (.proj 0)) (Cobham.tailFn (.proj 1))))

theorem binarySignedFixed_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binarySignedFixed (v 0) (v 1)) :=
  cobham_iff_FPn.mp binarySignedFixed_cobham

theorem binarySignedFixed_natAbs_lt (ruler x : List Bool) :
    (binarySignedValue (binarySignedFixed ruler x)).natAbs < 2 ^ (ruler.length - 1) := by
  rw [binarySignedValue_natAbs]
  simpa only [List.length_tail, binarySignedFixed_length] using
    Nat.fromBitsLE_lt_pow_length (binarySignedFixed ruler x).tail

/-- Add and normalize immediately to prevent accumulation of padding. -/
def binarySignedFixedAdd (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedAdd x y)

/-- Subtract and normalize immediately to the supplied field width. -/
def binarySignedFixedSub (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedSub x y)

/-- Multiply and normalize immediately to the supplied field width. -/
def binarySignedFixedMul (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedMul x y)

@[simp] theorem binarySignedFixedAdd_length (ruler x y : List Bool) :
    (binarySignedFixedAdd ruler x y).length = ruler.length := binarySignedFixed_length _ _

@[simp] theorem binarySignedFixedSub_length (ruler x y : List Bool) :
    (binarySignedFixedSub ruler x y).length = ruler.length := binarySignedFixed_length _ _

@[simp] theorem binarySignedFixedMul_length (ruler x y : List Bool) :
    (binarySignedFixedMul ruler x y).length = ruler.length := binarySignedFixed_length _ _

theorem binarySignedFixedAdd_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x + binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedAdd ruler x y) = binarySignedValue x + binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedAdd x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedAdd_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedAdd_value x y)

theorem binarySignedFixedSub_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x - binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedSub ruler x y) = binarySignedValue x - binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedSub x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedSub_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedSub_value x y)

theorem binarySignedFixedMul_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x * binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedMul ruler x y) = binarySignedValue x * binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedMul x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedMul_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedMul_value x y)

theorem binarySignedFixedAdd_cobham : Cobham fun v : Fin 3 → List Bool =>
    binarySignedFixedAdd (v 0) (v 1) (v 2) :=
  (Cobham.comp₂ binarySignedFixed_cobham (.proj 0)
    (Cobham.comp₂ binarySignedAdd_cobham (.proj 1) (.proj 2))).of_eq fun _ => rfl

theorem binarySignedFixedSub_cobham : Cobham fun v : Fin 3 → List Bool =>
    binarySignedFixedSub (v 0) (v 1) (v 2) :=
  (Cobham.comp₂ binarySignedFixed_cobham (.proj 0)
    (Cobham.comp₂ binarySignedSub_cobham (.proj 1) (.proj 2))).of_eq fun _ => rfl

theorem binarySignedFixedMul_cobham : Cobham fun v : Fin 3 → List Bool =>
    binarySignedFixedMul (v 0) (v 1) (v 2) :=
  (Cobham.comp₂ binarySignedFixed_cobham (.proj 0)
    (Cobham.comp₂ binarySignedMul_cobham (.proj 1) (.proj 2))).of_eq fun _ => rfl

theorem binarySignedFixedAdd_mem_FPn :
    FPn (fun v : Fin 3 → List Bool => binarySignedFixedAdd (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp binarySignedFixedAdd_cobham

theorem binarySignedFixedSub_mem_FPn :
    FPn (fun v : Fin 3 → List Bool => binarySignedFixedSub (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp binarySignedFixedSub_cobham

theorem binarySignedFixedMul_mem_FPn :
    FPn (fun v : Fin 3 → List Bool => binarySignedFixedMul (v 0) (v 1) (v 2)) :=
  cobham_iff_FPn.mp binarySignedFixedMul_cobham

end GameTheory.Complexity.Backend
