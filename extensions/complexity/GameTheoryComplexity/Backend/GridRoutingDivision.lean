import Complexitylib.Mathlib.NatBits
import Complexitylib.Classes.P.Cobham
import Mathlib.Tactic.FinCases

/-! Division by three scans binary digits from high to low. A two-bit remainder
header and a growing little-endian quotient form its linearly bounded word state. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

private def divisionStep (b : Bool) (state : List Bool) : List Bool :=
  let header := caseBit₀ state.tail
    (if b then [false, true, true] else [true, false, true])
    (caseBit₀ state
      (if b then [false, false, true] else [false, true, false])
      (if b then [true, false, false] else [false, false, false]))
  header ++ state.tail.tail

private def divisionState : List Bool → List Bool
  | [] => [false, false]
  | b :: bits => divisionStep b (divisionState bits)

/-- The fixed-width little-endian quotient after division by three. -/
def routingDivThreeBits (bits : List Bool) : List Bool := (divisionState bits).tail.tail

/-- Divide by six by removing the low quotient bit after division by three. -/
def routingDivSixBits (bits : List Bool) : List Bool := (routingDivThreeBits bits).tail

/-- The little-endian remainder after division by three, encoded in exactly two bits. -/
def routingModThreeBits (bits : List Bool) : List Bool := (divisionState bits).take 2

private def nextRemainder (b : Bool) (r : Fin 3) : Fin 3 :=
  ⟨(2 * r.val + if b then 1 else 0) % 3, Nat.mod_lt _ (by decide)⟩

private def nextQuotientBit (b : Bool) (r : Fin 3) : Bool :=
  decide (3 ≤ 2 * r.val + if b then 1 else 0)

private theorem divisionStep_encode (b : Bool) (r : Fin 3) (q : List Bool) :
    divisionStep b (Nat.toBitsLE 2 r.val ++ q) =
      Nat.toBitsLE 2 (nextRemainder b r).val ++ nextQuotientBit b r :: q := by
  cases b <;> fin_cases r <;>
    simp [divisionStep, nextRemainder, nextQuotientBit, Nat.toBitsLE, Nat.toBits, caseBit₀]

private theorem next_value (b : Bool) (r : Fin 3) :
    3 * (if nextQuotientBit b r then 1 else 0) + (nextRemainder b r).val =
      2 * r.val + if b then 1 else 0 := by
  cases b <;> fin_cases r <;> decide

private theorem divisionState_invariant (bits : List Bool) :
    ∃ r : Fin 3, ∃ q : List Bool,
      divisionState bits = Nat.toBitsLE 2 r.val ++ q ∧ q.length = bits.length ∧
        Nat.fromBitsLE bits = 3 * Nat.fromBitsLE q + r.val := by
  induction bits with
  | nil => exact ⟨0, [], rfl, rfl, rfl⟩
  | cons b bits ih =>
    obtain ⟨r, q, hs, hlen, hval⟩ := ih
    refine ⟨nextRemainder b r, nextQuotientBit b r :: q, ?_, by simp [hlen], ?_⟩
    · rw [divisionState, hs, divisionStep_encode]
    · have hn := next_value b r
      simp only [Nat.fromBitsLE_cons]
      omega

private theorem divisionState_length (bits : List Bool) :
    (divisionState bits).length = bits.length + 2 := by
  obtain ⟨r, q, hs, hlen, _⟩ := divisionState_invariant bits
  simp [hs, hlen, Nat.add_comm]

/-- Binary division retains exactly the input word's width. -/
@[simp] theorem routingDivThreeBits_length (bits : List Bool) :
    (routingDivThreeBits bits).length = bits.length := by
  simp [routingDivThreeBits, List.length_tail, divisionState_length]

/-- The output decodes to the exact quotient, including on empty or padded words. -/
theorem routingDivThreeBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingDivThreeBits bits) = Nat.fromBitsLE bits / 3 := by
  obtain ⟨r, q, hs, _, hval⟩ := divisionState_invariant bits
  have hq : routingDivThreeBits bits = q := by
    rw [routingDivThreeBits, hs]
    fin_cases r <;> rfl
  rw [hq]
  have hr := r.isLt
  omega

/-- Division by six drops one output position from the division-by-three word. -/
@[simp] theorem routingDivSixBits_length (bits : List Bool) :
    (routingDivSixBits bits).length = bits.length - 1 := by
  simp [routingDivSixBits, List.length_tail]

private theorem fromBitsLE_tail (bits : List Bool) :
    Nat.fromBitsLE bits.tail = Nat.fromBitsLE bits / 2 := by
  cases bits with
  | nil => rfl
  | cons b bits =>
    cases b with
    | false => simp [Nat.fromBitsLE_cons]
    | true => simp only [List.tail_cons, Nat.fromBitsLE_cons, ite_true]; omega

/-- The shortened quotient word decodes to exact division by six. -/
theorem routingDivSixBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingDivSixBits bits) = Nat.fromBitsLE bits / 6 := by
  rw [routingDivSixBits, fromBitsLE_tail, routingDivThreeBits_value,
    Nat.div_div_eq_div_mul]

/-- Remainders use a constant two-bit word independently of the input width. -/
@[simp] theorem routingModThreeBits_length (bits : List Bool) :
    (routingModThreeBits bits).length = 2 := by
  simp [routingModThreeBits, divisionState_length]

/-- The remainder word decodes to the exact residue modulo three. -/
theorem routingModThreeBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingModThreeBits bits) = Nat.fromBitsLE bits % 3 := by
  obtain ⟨r, q, hs, _, hval⟩ := divisionState_invariant bits
  have hr := r.isLt
  have he : routingModThreeBits bits = Nat.toBitsLE 2 r.val := by
    simp [routingModThreeBits, hs]
  rw [he, Nat.fromBitsLE_toBitsLE (by omega)]
  omega

private theorem divisionStep_cobham (b : Bool) :
    Cobham (fun v : Fin 2 → List Bool => divisionStep b (v 1)) := by
  exact Cobham.appendFn
    (Cobham.iteFn (Cobham.tailFn (.proj 1)) (Cobham.const _)
      (Cobham.iteFn (.proj 1) (Cobham.const _) (Cobham.const _)))
    (Cobham.tailFn (Cobham.tailFn (.proj 1)))

private theorem divisionState_rec (bits : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => [false, false])
      (fun w : Fin 2 → List Bool => divisionStep false (w 1))
      (fun w : Fin 2 → List Bool => divisionStep true (w 1)) bits v = divisionState bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [recNotation_cons, divisionState, ih]

private theorem divisionState_cobham :
    Cobham (fun v : Fin 1 → List Bool => divisionState (v 0)) := by
  have hbound : Cobham (fun v : Fin 1 → List Bool => false :: false :: v 0) :=
    Cobham.comp (.bit false) (fun _ =>
      Cobham.comp (.bit false) (fun _ => Cobham.proj (0 : Fin 1)))
  have h := Cobham.boundedRec (n := 0) (Cobham.const [false, false])
    (divisionStep_cobham false) (divisionStep_cobham true) hbound (fun bits v => by
      rw [divisionState_rec, divisionState_length]
      simp)
  exact h.of_eq fun v => divisionState_rec (v 0) (Fin.tail v)

/-- Binary division by three has an actual polynomial-time word-machine certificate. -/
theorem routingDivThreeBits_mem_FP : routingDivThreeBits ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.tailFn (Cobham.tailFn divisionState_cobham)

/-- Division by six composes the binary division scan with one word-tail operation. -/
theorem routingDivSixBits_mem_FP : routingDivSixBits ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.tailFn (Cobham.tailFn (Cobham.tailFn divisionState_cobham))

/-- The remainder is obtained by the same polynomial-time binary scan. -/
theorem routingModThreeBits_mem_FP : routingModThreeBits ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.takeFn (Cobham.const [false, false]) divisionState_cobham

end GameTheory.Complexity.Backend
