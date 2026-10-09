import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal.StringOps
import Complexitylib.Mathlib.NatBits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Binary certificate arithmetic uses bit positions and bounded word recursion.
The fields may represent exponentially large naturals; no loop counts their values. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

private def flagXor (x y : List Bool) : List Bool :=
  orBit (andBit x (notBit y)) (andBit (notBit x) y)

private theorem flagXor_cobham {n : ℕ} {x y : (Fin n → List Bool) → List Bool}
    (hx : Cobham x) (hy : Cobham y) : Cobham fun v => flagXor (x v) (y v) :=
  Cobham.orFn (Cobham.andFn hx (Cobham.notFn hy))
    (Cobham.andFn (Cobham.notFn hx) hy)

/-- One little-endian column updates the carry header and appends its sum bit. -/
def binaryAddColumn (v : Fin 4 → List Bool) : List Bool :=
  let x := bitAt (v 0) (v 2)
  let y := bitAt (v 0) (v 3)
  let c := bitAt [] (v 1)
  orBit (andBit x y) (andBit c (orBit x y)) ++
    (v 1).tail ++ flagXor (flagXor x y) c

/-- The column operation belongs to Cobham's polynomial-time algebra. -/
theorem binaryAddColumn_cobham : Cobham binaryAddColumn := by
  have hx := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 2)
  have hy := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 3)
  have hc := Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (Cobham.proj (1 : Fin 4))
  exact Cobham.appendFn (Cobham.appendFn
    (Cobham.orFn (Cobham.andFn hx hy) (Cobham.andFn hc (Cobham.orFn hx hy)))
    (Cobham.tailFn (Cobham.proj 1))) (flagXor_cobham (flagXor_cobham hx hy) hc)

/-- Scan exactly the ruler's number of columns, with zero padding on either side. -/
def binaryAddScan (ruler x y : List Bool) : List Bool :=
  recNotation (fun _ : Fin 2 → List Bool => [false])
    binaryAddColumn binaryAddColumn ruler ![x, y]

private theorem flag_length (x y : List Bool) : (flagXor x y).length = 1 := by
  exact orBit_length _ _

private theorem binaryAddScan_length (ruler x y : List Bool) :
    (binaryAddScan ruler x y).length = ruler.length + 1 := by
  induction ruler with
  | nil => rfl
  | cons b ruler ih =>
    simp only [binaryAddScan, recNotation_cons, Bool.cond_self, binaryAddColumn,
      Fin.cons_zero, List.length_append, orBit_length, flag_length]
    change 1 + ((binaryAddScan ruler x y).tail).length + 1 = _
    simp [List.length_tail, ih]
    omega

/-- Choose a width ruler equal to the longer operand. -/
def binaryMaxRuler (x y : List Bool) : List Bool :=
  caseBit₀ (lenLeFlag x y) x y

/-- Add arbitrary little-endian words, retaining the final carry bit. -/
def binaryCertificateAdd (v : Fin 2 → List Bool) : List Bool :=
  let s := binaryAddScan (binaryMaxRuler (v 0) (v 1)) (v 0) (v 1)
  s.tail ++ bitAt [] s

/-- The complete carry scan has a linear output bound and a real Cobham certificate. -/
theorem binaryAddScan_cobham : Cobham fun v : Fin 3 → List Bool =>
    binaryAddScan (v 0) (v 1) (v 2) := by
  have hj : Cobham fun v : Fin 3 → List Bool => false :: v 0 :=
    (Cobham.comp (.bit false) fun _ => Cobham.proj 0).of_eq fun _ => rfl
  exact (Cobham.boundedRec (Cobham.const [false]) binaryAddColumn_cobham
    binaryAddColumn_cobham hj (fun r v => by
      have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [hv]
      exact (binaryAddScan_length r (v 0) (v 1)).le)).of_eq fun v => by
        congr 1
        ext i
        fin_cases i <;> rfl

private theorem binaryMaxRuler_cobham : Cobham fun v : Fin 2 → List Bool =>
    binaryMaxRuler (v 0) (v 1) :=
  Cobham.iteFn (lenLeFlag_mem (.proj 0) (.proj 1)) (.proj 0) (.proj 1)

/-- Addition is computed by an actual polynomial-time string machine. -/
theorem binaryCertificateAdd_cobham : Cobham binaryCertificateAdd := by
  have hs : Cobham fun v : Fin 2 → List Bool =>
      binaryAddScan (binaryMaxRuler (v 0) (v 1)) (v 0) (v 1) :=
    Cobham.comp₃ binaryAddScan_cobham binaryMaxRuler_cobham (.proj 0) (.proj 1)
  exact Cobham.appendFn (Cobham.tailFn hs)
    (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) hs)

/-- The addition certificate concerns binary input length, rather than numeric value. -/
theorem binaryCertificateAdd_mem_FPn : FPn binaryCertificateAdd :=
  cobham_iff_FPn.mp binaryCertificateAdd_cobham

/-- Bit extraction agrees with indexed lookup, defaulting to false out of range. -/
theorem bitAt_getElem? (r x : List Bool) :
    bitAt r x = [x[r.length]?.getD false] := by
  simpa only [bitOf, List.headD_eq_head?_getD, List.head?_eq_getElem?,
    List.getElem?_drop, Nat.add_zero] using _root_.Complexity.bitAt_eq r x

/-- Appending little-endian fields shifts the second field by the first field's width. -/
theorem fromBitsLE_append (x y : List Bool) :
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
      simp only [List.take_succ_cons, Nat.fromBitsLE_cons, List.getElem?_cons_succ,
        ih, pow_succ]
      ring

private theorem binaryAddColumn_eq (r x y out : List Bool) (c : Bool) :
    binaryAddColumn ![r, c :: out, x, y] =
      let a := (x[r.length]?).getD false
      let b := (y[r.length]?).getD false
      ((a && b) || (c && (a || b))) :: (out ++ [(a.xor b).xor c]) := by
  change orBit (andBit (bitAt r x) (bitAt r y))
    (andBit (bitAt [] (c :: out)) (orBit (bitAt r x) (bitAt r y))) ++
    out ++ flagXor (flagXor (bitAt r x) (bitAt r y)) (bitAt [] (c :: out)) = _
  simp only [bitAt_getElem?, List.length_nil, List.getElem?_cons_zero, Option.getD_some]
  generalize (x[r.length]?).getD false = a
  generalize (y[r.length]?).getD false = b
  cases a <;> cases b <;> cases c <;>
    simp [flagXor, orBit, andBit, notBit, caseBit₀]

set_option backward.isDefEq.respectTransparency false in
private theorem binaryAddScan_value (r x y : List Bool) :
    Nat.fromBitsLE (binaryAddScan r x y).tail +
      2 ^ r.length * (if (binaryAddScan r x y).headD false then 1 else 0) =
    Nat.fromBitsLE (x.take r.length) + Nat.fromBitsLE (y.take r.length) := by
  induction r with
  | nil => simp [binaryAddScan, Nat.fromBitsLE, Nat.fromBits]
  | cons z r ih =>
    have hlen := binaryAddScan_length r x y
    cases hs : binaryAddScan r x y with
    | nil => simp [hs] at hlen
    | cons c out =>
      rw [hs] at ih hlen
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.tail_cons, List.headD_cons] at ih
      simp only [binaryAddScan, recNotation_cons, Bool.cond_self]
      change Nat.fromBitsLE (binaryAddColumn ![r, binaryAddScan r x y, x, y]).tail +
        2 ^ (r.length + 1) *
          (if (binaryAddColumn ![r, binaryAddScan r x y, x, y]).headD false then 1 else 0) = _
      rw [hs, binaryAddColumn_eq]
      dsimp only
      simp only [List.tail_cons, List.headD_cons, List.length_cons]
      rw [fromBitsLE_append, hlen, prefix_succ, prefix_succ]
      have hn : Nat.fromBitsLE [] = 0 := rfl
      simp only [Nat.fromBitsLE_cons, hn, mul_zero, add_zero, pow_succ]
      generalize (x[r.length]?).getD false = a
      generalize (y[r.length]?).getD false = b
      cases a <;> cases b <;> cases c <;> simp_all <;> nlinarith

private theorem binaryMaxRuler_length (x y : List Bool) :
    (binaryMaxRuler x y).length = max x.length y.length := by
  rcases lenLeFlag_flag x y with h | h
  · have hle := (lenLeFlag_eq_true_iff x y).mp h
    simp [binaryMaxRuler, h, Nat.max_eq_left hle]
  · have hlt : x.length < y.length := by
      by_contra hn
      have ht := (lenLeFlag_eq_true_iff x y).mpr (by omega)
      simp [h] at ht
    simp [binaryMaxRuler, h, Nat.max_eq_right hlt.le]

/-- Addition always emits exactly one more bit than the longer operand. -/
theorem binaryCertificateAdd_length (x y : List Bool) :
    (binaryCertificateAdd ![x, y]).length = max x.length y.length + 1 := by
  change ((binaryAddScan (binaryMaxRuler x y) x y).tail ++
    bitAt [] (binaryAddScan (binaryMaxRuler x y) x y)).length = _
  rw [List.length_append, bitAt_length, List.length_tail, binaryAddScan_length,
    binaryMaxRuler_length]
  omega

/-- Every word, including noncanonical zero padding, has its exact natural sum. -/
theorem binaryCertificateAdd_value (x y : List Bool) :
    Nat.fromBitsLE (binaryCertificateAdd ![x, y]) =
      Nat.fromBitsLE x + Nat.fromBitsLE y := by
  have hv := binaryAddScan_value (binaryMaxRuler x y) x y
  have hl := binaryAddScan_length (binaryMaxRuler x y) x y
  have hx : x.length ≤ (binaryMaxRuler x y).length := by
    rw [binaryMaxRuler_length]; exact Nat.le_max_left _ _
  have hy : y.length ≤ (binaryMaxRuler x y).length := by
    rw [binaryMaxRuler_length]; exact Nat.le_max_right _ _
  simp only [List.take_of_length_le hx, List.take_of_length_le hy] at hv
  change Nat.fromBitsLE ((binaryAddScan (binaryMaxRuler x y) x y).tail ++
    bitAt [] (binaryAddScan (binaryMaxRuler x y) x y)) = _
  rw [fromBitsLE_append]
  have hb : bitAt [] (binaryAddScan (binaryMaxRuler x y) x y) =
      [(binaryAddScan (binaryMaxRuler x y) x y).headD false] := by
    cases binaryAddScan (binaryMaxRuler x y) x y with
    | nil => rfl
    | cons b t => cases b <;> rfl
  rw [hb, Nat.fromBitsLE_cons]
  have hn : Nat.fromBitsLE [] = 0 := rfl
  simp only [hn, mul_zero, add_zero, List.length_tail, hl, Nat.add_sub_cancel]
  exact hv

/-- A comparison column replaces the flag only when the new, higher bits differ. -/
def binaryLEColumn (v : Fin 4 → List Bool) : List Bool :=
  let x := bitAt (v 0) (v 2)
  let y := bitAt (v 0) (v 3)
  caseBit₀ (flagXor x y) (notBit x) (v 1)

/-- Scan unsigned comparison with zero extension to the ruler width. -/
def binaryLEScan (r x y : List Bool) : List Bool :=
  recNotation (fun _ : Fin 2 → List Bool => [true]) binaryLEColumn binaryLEColumn r ![x, y]

/-- Compare arbitrary little-endian binary fields as unsigned naturals. -/
def binaryCertificateLE (v : Fin 2 → List Bool) : List Bool :=
  binaryLEScan (binaryMaxRuler (v 0) (v 1)) (v 0) (v 1)

private theorem binaryLEColumn_cobham : Cobham binaryLEColumn := by
  have hx := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 2)
  have hy := Cobham.comp₂ Cobham.bitAtFn (Cobham.proj (0 : Fin 4)) (Cobham.proj 3)
  exact Cobham.iteFn (flagXor_cobham hx hy) (Cobham.notFn hx) (Cobham.proj 1)

private theorem binaryLEScan_length (r x y : List Bool) :
    (binaryLEScan r x y).length = 1 := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    simp only [binaryLEScan, recNotation_cons, Bool.cond_self, binaryLEColumn,
      Fin.cons_zero]
    change (caseBit₀ (flagXor (bitAt r x) (bitAt r y))
      (notBit (bitAt r x)) (binaryLEScan r x y)).length = 1
    rw [bitAt_getElem?, bitAt_getElem?]
    generalize hx : (x[r.length]?).getD false = a
    generalize hy : (y[r.length]?).getD false = c
    cases a <;> cases c <;> simp [flagXor, caseBit₀, notBit, orBit, andBit, ih]

/-- The unsigned comparator has an actual polynomial-time machine certificate. -/
theorem binaryCertificateLE_cobham : Cobham binaryCertificateLE := by
  have hr : Cobham fun v : Fin 3 → List Bool => binaryLEScan (v 0) (v 1) (v 2) :=
    (Cobham.boundedRec (Cobham.const [true]) binaryLEColumn_cobham
      binaryLEColumn_cobham (Cobham.const [true]) (fun r v => by
        have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
        rw [hv]
        exact (binaryLEScan_length r (v 0) (v 1)).le)).of_eq fun v => by
          congr 1
          ext i
          fin_cases i <;> rfl
  exact Cobham.comp₃ hr binaryMaxRuler_cobham (.proj 0) (.proj 1)

/-- Unsigned comparison is polynomial in field bit length. -/
theorem binaryCertificateLE_mem_FPn : FPn binaryCertificateLE :=
  cobham_iff_FPn.mp binaryCertificateLE_cobham

private theorem prefix_bound (k : ℕ) (x : List Bool) :
    Nat.fromBitsLE (x.take k) < 2 ^ k := by
  induction k with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | succ k ih =>
    rw [prefix_succ, pow_succ]
    cases (x[k]?).getD false <;> simp only [Bool.false_eq_true, ↓reduceIte,
      mul_zero, mul_one, add_zero] <;> omega

private theorem binaryLEColumn_eq (r x y : List Bool) (previous : Bool) :
    binaryLEColumn ![r, [previous], x, y] =
      [if (x[r.length]?).getD false = (y[r.length]?).getD false then previous
        else !((x[r.length]?).getD false)] := by
  change caseBit₀ (flagXor (bitAt r x) (bitAt r y))
    (notBit (bitAt r x)) [previous] = _
  rw [bitAt_getElem?, bitAt_getElem?]
  generalize (x[r.length]?).getD false = a
  generalize (y[r.length]?).getD false = b
  cases a <;> cases b <;> cases previous <;> rfl

private theorem binaryLEScan_value (r x y : List Bool) :
    binaryLEScan r x y =
      [decide (Nat.fromBitsLE (x.take r.length) ≤ Nat.fromBitsLE (y.take r.length))] := by
  induction r with
  | nil => simp [binaryLEScan, Nat.fromBitsLE, Nat.fromBits]
  | cons z r ih =>
    simp only [binaryLEScan, recNotation_cons, Bool.cond_self]
    change binaryLEColumn ![r, binaryLEScan r x y, x, y] = _
    rw [ih, binaryLEColumn_eq]
    simp only [List.length_cons]
    simp only [prefix_succ]
    have hx := prefix_bound r.length x
    have hy := prefix_bound r.length y
    generalize ha : (x[r.length]?).getD false = a
    generalize hb : (y[r.length]?).getD false = b
    cases a <;> cases b
    · simp
    · have ht : Nat.fromBitsLE (x.take r.length) ≤
          Nat.fromBitsLE (y.take r.length) + 2 ^ r.length := by omega
      simp [ht]
    · have hf : ¬ (Nat.fromBitsLE (x.take r.length) + 2 ^ r.length ≤
          Nat.fromBitsLE (y.take r.length)) := by omega
      simp [hf]
    · simp

/-- Comparison is exact for every word, including unequal widths and high zero padding. -/
theorem binaryCertificateLE_value (x y : List Bool) :
    binaryCertificateLE ![x, y] = [decide (Nat.fromBitsLE x ≤ Nat.fromBitsLE y)] := by
  change binaryLEScan (binaryMaxRuler x y) x y = _
  rw [binaryLEScan_value, binaryMaxRuler_length]
  rw [List.take_of_length_le (Nat.le_max_left _ _),
    List.take_of_length_le (Nat.le_max_right _ _)]

/-- The comparison output is a Boolean flag. -/
theorem binaryCertificateLE_length (x y : List Bool) :
    (binaryCertificateLE ![x, y]).length = 1 :=
  binaryLEScan_length _ _ _

/-- The adder emits the exact padded codec of the full sum, without truncating carry. -/
theorem binaryCertificateAdd_eq_toBitsLE (x y : List Bool) :
    binaryCertificateAdd ![x, y] = Nat.toBitsLE (max x.length y.length + 1)
      (Nat.fromBitsLE x + Nat.fromBitsLE y) := by
  have h := Nat.toBitsLE_fromBitsLE (binaryCertificateAdd ![x, y])
  rw [binaryCertificateAdd_length, binaryCertificateAdd_value] at h
  exact h.symm

/-- The comparison flag accepts exactly unsigned less-than-or-equal. -/
theorem binaryCertificateLE_eq_true_iff (x y : List Bool) :
    binaryCertificateLE ![x, y] = [true] ↔ Nat.fromBitsLE x ≤ Nat.fromBitsLE y := by
  rw [binaryCertificateLE_value]
  simp

end GameTheory.Complexity.Backend
