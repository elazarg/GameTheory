import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Unsigned saturating subtraction scans little-endian bit positions with one
borrow bit. Its loop and output bounds depend on operand lengths, including
padding, rather than on the represented numeric values. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

private def subXor (x y : List Bool) : List Bool :=
  orBit (andBit x (notBit y)) (andBit (notBit x) y)

private theorem subXor_cobham {n : ℕ} {x y : (Fin n → List Bool) → List Bool}
    (hx : Cobham x) (hy : Cobham y) : Cobham fun v => subXor (x v) (y v) :=
  Cobham.orFn (Cobham.andFn hx (Cobham.notFn hy))
    (Cobham.andFn (Cobham.notFn hx) hy)

private def subColumn (v : Fin 4 → List Bool) : List Bool :=
  let x := bitAt (v 0) (v 2)
  let y := bitAt (v 0) (v 3)
  let b := bitAt [] (v 1)
  orBit (andBit (notBit x) y) (andBit b (orBit (notBit x) y)) ++
    (v 1).tail ++ subXor (subXor x y) b

private theorem subColumn_cobham : Cobham subColumn := by
  have hx := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 2)
  have hy := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 3)
  have hb := Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (Cobham.proj (1 : Fin 4))
  exact Cobham.appendFn (Cobham.appendFn
    (Cobham.orFn (Cobham.andFn (Cobham.notFn hx) hy)
      (Cobham.andFn hb (Cobham.orFn (Cobham.notFn hx) hy)))
    (Cobham.tailFn (Cobham.proj 1))) (subXor_cobham (subXor_cobham hx hy) hb)

private def subScan (ruler x y : List Bool) : List Bool :=
  recNotation (fun _ : Fin 2 → List Bool => [false]) subColumn subColumn ruler ![x, y]

private theorem subScan_length (ruler x y : List Bool) :
    (subScan ruler x y).length = ruler.length + 1 := by
  induction ruler with
  | nil => rfl
  | cons b ruler ih =>
    simp only [subScan, recNotation_cons, Bool.cond_self, subColumn,
      Fin.cons_zero, List.length_append, orBit_length]
    change 1 + ((subScan ruler x y).tail).length + (subXor _ _).length = _
    have hxor (u v : List Bool) : (subXor u v).length = 1 := orBit_length _ _
    rw [hxor, List.length_tail, ih]
    simp only [List.length_cons]
    omega

private theorem subScan_cobham : Cobham fun v : Fin 3 → List Bool =>
    subScan (v 0) (v 1) (v 2) := by
  have hj : Cobham fun v : Fin 3 → List Bool => false :: v 0 :=
    (Cobham.comp (.bit false) fun _ => Cobham.proj 0).of_eq fun _ => rfl
  exact (Cobham.boundedRec (Cobham.const [false]) subColumn_cobham subColumn_cobham hj
    (fun r v => by
      have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [hv]
      exact (subScan_length r (v 0) (v 1)).le)).of_eq fun v => by
        congr 1
        ext i
        fin_cases i <;> rfl

private theorem maxRuler_cobham : Cobham fun v : Fin 2 → List Bool =>
    binaryMaxRuler (v 0) (v 1) :=
  Cobham.iteFn (lenLeFlag_mem (.proj 0) (.proj 1)) (.proj 0) (.proj 1)

private theorem maxRuler_length (x y : List Bool) :
    (binaryMaxRuler x y).length = max x.length y.length := by
  rcases lenLeFlag_flag x y with h | h
  · have hle := (lenLeFlag_eq_true_iff x y).mp h
    simp [binaryMaxRuler, h, Nat.max_eq_left hle]
  · have hlt : x.length < y.length := by
      by_contra hn
      have ht := (lenLeFlag_eq_true_iff x y).mpr (by omega)
      simp [h] at ht
    simp [binaryMaxRuler, h, Nat.max_eq_right hlt.le]

/-- Subtract unsigned words, returning zero when the subtrahend is greater. -/
def binaryWordSub (x y : List Bool) : List Bool :=
  let s := subScan (binaryMaxRuler x y) x y
  caseBit₀ (bitAt [] s) [] s.tail

/-- Saturating subtraction belongs to the actual polynomial-time Cobham algebra. -/
theorem binaryWordSub_cobham : Cobham fun v : Fin 2 → List Bool =>
    binaryWordSub (v 0) (v 1) := by
  have hs : Cobham fun v : Fin 2 → List Bool =>
      subScan (binaryMaxRuler (v 0) (v 1)) (v 0) (v 1) :=
    Cobham.comp₃ subScan_cobham maxRuler_cobham (.proj 0) (.proj 1)
  exact Cobham.iteFn (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) hs)
    Cobham.empty (Cobham.tailFn hs)

theorem binaryWordSub_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binaryWordSub (v 0) (v 1)) :=
  cobham_iff_FPn.mp binaryWordSub_cobham

private theorem bitAt_eq (r x : List Bool) :
    bitAt r x = [(x[r.length]?).getD false] := by
  simp only [bitAt]
  induction r generalizing x with
  | nil => cases x with
    | nil => rfl
    | cons b x => cases b <;> rfl
  | cons b r ih =>
    cases x with
    | nil => simp [caseBit₀]
    | cons c x => simpa only [List.length_cons, List.drop_succ_cons,
        List.getElem?_cons_succ] using ih x

private theorem fromBitsLE_append (x y : List Bool) :
    Nat.fromBitsLE (x ++ y) = Nat.fromBitsLE x + 2 ^ x.length * Nat.fromBitsLE y := by
  induction x with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons b x ih =>
    simp only [List.cons_append, Nat.fromBitsLE_cons, List.length_cons, ih, pow_succ]
    ring

private theorem prefix_succ (k : ℕ) (x : List Bool) :
    Nat.fromBitsLE (x.take (k + 1)) = Nat.fromBitsLE (x.take k) +
      2 ^ k * (if (x[k]?).getD false then 1 else 0) := by
  induction k generalizing x with
  | zero => cases x with
    | nil => simp [Nat.fromBitsLE, Nat.fromBits]
    | cons b x => simp [Nat.fromBitsLE, Nat.fromBits]
  | succ k ih =>
    cases x with
    | nil => simp [Nat.fromBitsLE, Nat.fromBits]
    | cons b x =>
      simp only [List.take_succ_cons, Nat.fromBitsLE_cons, List.getElem?_cons_succ, ih, pow_succ]
      ring

private theorem subColumn_eq (r x y out : List Bool) (b : Bool) :
    subColumn ![r, b :: out, x, y] =
      let a := (x[r.length]?).getD false
      let c := (y[r.length]?).getD false
      ((!a && c) || (b && (!a || c))) :: (out ++ [(a.xor c).xor b]) := by
  change orBit (andBit (notBit (bitAt r x)) (bitAt r y))
    (andBit (bitAt [] (b :: out)) (orBit (notBit (bitAt r x)) (bitAt r y))) ++
    out ++ subXor (subXor (bitAt r x) (bitAt r y)) (bitAt [] (b :: out)) = _
  simp only [bitAt_eq, List.length_nil, List.getElem?_cons_zero, Option.getD_some]
  generalize (x[r.length]?).getD false = a
  generalize (y[r.length]?).getD false = c
  cases a <;> cases c <;> cases b <;>
    simp [subXor, orBit, andBit, notBit, caseBit₀]

set_option backward.isDefEq.respectTransparency false in
private theorem subScan_value (r x y : List Bool) :
    Nat.fromBitsLE (subScan r x y).tail + Nat.fromBitsLE (y.take r.length) =
      Nat.fromBitsLE (x.take r.length) +
        2 ^ r.length * (if (subScan r x y).headD false then 1 else 0) := by
  induction r with
  | nil => simp [subScan, Nat.fromBitsLE, Nat.fromBits]
  | cons z r ih =>
    have hlen := subScan_length r x y
    cases hs : subScan r x y with
    | nil => simp [hs] at hlen
    | cons b out =>
      rw [hs] at ih hlen
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.tail_cons, List.headD_cons] at ih
      simp only [subScan, recNotation_cons, Bool.cond_self]
      change Nat.fromBitsLE (subColumn ![r, subScan r x y, x, y]).tail +
        Nat.fromBitsLE (y.take (r.length + 1)) = Nat.fromBitsLE (x.take (r.length + 1)) +
          2 ^ (r.length + 1) *
            (if (subColumn ![r, subScan r x y, x, y]).headD false then 1 else 0)
      rw [hs, subColumn_eq]
      dsimp only
      simp only [List.tail_cons, List.headD_cons]
      rw [fromBitsLE_append, hlen, prefix_succ, prefix_succ]
      have hn : Nat.fromBitsLE [] = 0 := rfl
      simp only [Nat.fromBitsLE_cons, hn, mul_zero, add_zero, pow_succ]
      generalize (x[r.length]?).getD false = a
      generalize (y[r.length]?).getD false = c
      cases a <;> cases c <;> cases b <;> simp_all <;> nlinarith

private theorem word_bound (x : List Bool) : Nat.fromBitsLE x < 2 ^ x.length := by
  induction x with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons b x ih => cases b <;> simp only [Nat.fromBitsLE_cons, List.length_cons, pow_succ] <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The output fits the wider operand, including arbitrary high zero padding. -/
theorem binaryWordSub_length (x y : List Bool) :
    (binaryWordSub x y).length ≤ max x.length y.length := by
  have hl := subScan_length (binaryMaxRuler x y) x y
  unfold binaryWordSub
  cases hs : subScan (binaryMaxRuler x y) x y with
  | nil => simp [hs] at hl
  | cons b out =>
    rw [hs, maxRuler_length] at hl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    cases b
    · change out.length ≤ max x.length y.length
      omega
    · change ([] : List Bool).length ≤ max x.length y.length
      simp

/-- The bit scan implements exact natural-number saturating subtraction. -/
theorem binaryWordSub_value (x y : List Bool) :
    Nat.fromBitsLE (binaryWordSub x y) = Nat.fromBitsLE x - Nat.fromBitsLE y := by
  have hv := subScan_value (binaryMaxRuler x y) x y
  have hl := subScan_length (binaryMaxRuler x y) x y
  have hx : x.length ≤ (binaryMaxRuler x y).length := by
    rw [maxRuler_length]
    exact Nat.le_max_left _ _
  have hy : y.length ≤ (binaryMaxRuler x y).length := by
    rw [maxRuler_length]
    exact Nat.le_max_right _ _
  simp only [List.take_of_length_le hx, List.take_of_length_le hy] at hv
  unfold binaryWordSub
  cases hs : subScan (binaryMaxRuler x y) x y with
  | nil => simp [hs] at hl
  | cons b out =>
    rw [hs] at hv hl
    simp only [List.tail_cons, List.headD_cons, List.length_cons,
      Nat.add_right_cancel_iff] at hv hl
    have ho := word_bound out
    rw [hl] at ho
    cases b
    · change Nat.fromBitsLE out = Nat.fromBitsLE x - Nat.fromBitsLE y
      simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at hv
      omega
    · change Nat.fromBitsLE [] = Nat.fromBitsLE x - Nat.fromBitsLE y
      have hn : Nat.fromBitsLE [] = 0 := rfl
      rw [hn]
      simp only [↓reduceIte, mul_one] at hv
      omega

end GameTheory.Complexity.Backend
