import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Certified length arithmetic on explicit rulers.
The machine stores a parity header and a unary half-length tail.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private def halfStep (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (bitAt [] (v 1)) (false :: true :: (v 1).tail) (true :: (v 1).tail)

private def halfState (word : List Bool) : List Bool :=
  recNotation (fun _ : Fin 0 → List Bool => [false]) halfStep halfStep word Fin.elim0

private theorem halfState_value (word : List Bool) :
    halfState word = decide (word.length % 2 = 1) :: List.replicate (word.length / 2) true := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [halfState, recNotation_cons, Bool.cond_self]
    change halfStep ![word, halfState word] = _
    rw [ih]
    have hm : word.length % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases ho : word.length % 2 = 1
    · have hp : (word.length + 1) % 2 ≠ 1 := by omega
      have hh : (word.length + 1) / 2 = word.length / 2 + 1 := by omega
      simp [halfStep, ho, hp, hh, bitAt, caseBit₀, List.replicate_succ]
    · have hp : (word.length + 1) % 2 = 1 := by omega
      have hh : (word.length + 1) / 2 = word.length / 2 := by omega
      simp [halfStep, ho, hp, hh, bitAt, caseBit₀]

private theorem halfState_length (word : List Bool) :
    (halfState word).length = word.length / 2 + 1 := by
  rw [halfState_value]
  simp

private theorem halfState_cobham : Cobham fun v : Fin 1 → List Bool => halfState (v 0) := by
  have ht : Cobham halfStep := Cobham.iteFn
    (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1))
    (Cobham.appendFn (Cobham.const [false, true]) (Cobham.tailFn (.proj 1)))
    (Cobham.appendFn (Cobham.const [true]) (Cobham.tailFn (.proj 1)))
  exact (Cobham.boundedRec (Cobham.const [false]) ht ht
    (Cobham.appendFn (Cobham.const [true]) (.proj 0)) (fun r p => by
      have hp : p = Fin.elim0 := by ext i; exact i.elim0
      rw [hp]
      exact (halfState_length r).le.trans (by
        simp only [List.length_append, List.length_singleton, Fin.cons_zero]
        omega))).of_eq
        fun v => by congr 1; ext i; exact i.elim0

/-- A unary ruler of half the input length, rounded down. -/
def binaryHalfRuler (word : List Bool) : List Bool := (halfState word).tail

theorem binaryHalfRuler_value (word : List Bool) :
    binaryHalfRuler word = List.replicate (word.length / 2) true := by
  simp only [binaryHalfRuler, halfState_value, List.tail_cons]

@[simp] theorem binaryHalfRuler_length (word : List Bool) :
    (binaryHalfRuler word).length = word.length / 2 := by
  rw [binaryHalfRuler_value, List.length_replicate]

theorem binaryHalfRuler_cobham : Cobham fun v : Fin 1 → List Bool => binaryHalfRuler (v 0) :=
  Cobham.tailFn halfState_cobham

theorem binaryHalfRuler_mem_FPn : FPn (fun v : Fin 1 → List Bool => binaryHalfRuler (v 0)) :=
  cobham_iff_FPn.mp binaryHalfRuler_cobham

/-- A singleton flag recording whether a ruler has odd length. -/
def binaryLengthParity (word : List Bool) : List Bool := bitAt [] (halfState word)

theorem binaryLengthParity_value (word : List Bool) :
    binaryLengthParity word = [decide (word.length % 2 = 1)] := by
  rw [binaryLengthParity, halfState_value]
  generalize decide (word.length % 2 = 1) = b
  cases b <;> rfl

@[simp] theorem binaryLengthParity_length (word : List Bool) :
    (binaryLengthParity word).length = 1 := bitAt_length _ _

theorem binaryLengthParity_cobham : Cobham fun v : Fin 1 → List Bool => binaryLengthParity (v 0) :=
  Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) halfState_cobham

theorem binaryLengthParity_mem_FPn : FPn (fun v : Fin 1 → List Bool => binaryLengthParity (v 0)) :=
  cobham_iff_FPn.mp binaryLengthParity_cobham

end GameTheory.Complexity.Backend
