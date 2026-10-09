import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Polynomial-time lexicographic scans of indexed Boolean comparisons.

The two-bit state records whether the prefix is equal and whether it is less.
The clock is a word, so scanning never iterates a binary represented value.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private theorem and_length (x y : List Bool) : (andBit x y).length = 1 := by
  cases x with
  | nil => rfl
  | cons a x =>
    cases a with
    | false => rfl
    | true => cases y with
      | nil => rfl
      | cons b y => cases b <;> rfl

private def indexedLexStep {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 2) → List Bool) : List Bool :=
  let args := Fin.cons (v 0) (Fin.tail (Fin.tail v))
  andBit (bitAt [] (v 1)) (eq args) ++
    orBit (bitAt [false] (v 1)) (andBit (bitAt [] (v 1)) (lt args))

/-- Scan indexed comparisons, retaining the first unequal coordinate. -/
def binaryIndexedLexState {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun _ => [true, false]) (indexedLexStep lt eq) (indexedLexStep lt eq)
    clock params

/-- Return the strict comparison bit from the scan's two-bit state. -/
def binaryIndexedLexLT {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  bitAt [false] (binaryIndexedLexState lt eq clock params)

theorem binaryIndexedLexState_length {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedLexState lt eq clock params).length = 2 := by
  cases clock with
  | nil => rfl
  | cons b clock =>
    simp only [binaryIndexedLexState, recNotation_cons, Bool.cond_self, indexedLexStep,
      List.length_append, and_length, orBit_length]

@[simp] theorem binaryIndexedLexLT_length {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedLexLT lt eq clock params).length = 1 := bitAt_length _ _

/-- A constant-size state makes any two certified indexed comparisons a certified scan. -/
theorem binaryIndexedLexState_cobham {p : ℕ}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    (hlt : Cobham lt) (heq : Cobham eq) :
    Cobham fun v : Fin (p + 1) → List Bool =>
      binaryIndexedLexState lt eq (v 0) (Fin.tail v) := by
  have liftTerm {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
      Cobham fun v : Fin (p + 2) → List Bool =>
        term (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
    apply Cobham.comp ht
    intro i
    exact Fin.cases (.proj 0) (fun j => .proj j.succ.succ) i
  have hhead : Cobham fun v : Fin (p + 2) → List Bool => bitAt [] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1)
  have hless : Cobham fun v : Fin (p + 2) → List Bool => bitAt [false] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const [false]) (.proj 1)
  have hs : Cobham (indexedLexStep lt eq) :=
    Cobham.appendFn (Cobham.andFn hhead (liftTerm heq))
      (Cobham.orFn hless (Cobham.andFn hhead (liftTerm hlt)))
  exact (Cobham.boundedRec (Cobham.const [true, false]) hs hs
    (Cobham.const [false, false]) (fun r v => (binaryIndexedLexState_length lt eq r v).le)).of_eq
      fun _ => rfl

theorem binaryIndexedLexLT_cobham {p : ℕ}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    (hlt : Cobham lt) (heq : Cobham eq) :
    Cobham fun v : Fin (p + 1) → List Bool => binaryIndexedLexLT lt eq (v 0) (Fin.tail v) :=
  Cobham.comp₂ Cobham.bitAtFn (Cobham.const [false]) (binaryIndexedLexState_cobham hlt heq)

theorem binaryIndexedLexLT_mem_FPn {p : ℕ}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    (hlt : Cobham lt) (heq : Cobham eq) :
    FPn (fun v : Fin (p + 1) → List Bool => binaryIndexedLexLT lt eq (v 0) (Fin.tail v)) :=
  cobham_iff_FPn.mp (binaryIndexedLexLT_cobham hlt heq)

private theorem indexedPrefix_succ (E L : ℕ → Bool) (n : ℕ) :
    (∃ i < n + 1, L i = true ∧ ∀ j < i, E j = true) ↔
      (∃ i < n, L i = true ∧ ∀ j < i, E j = true) ∨
        ((∀ j < n, E j = true) ∧ L n = true) := by
  rw [Nat.exists_lt_succ_right]
  exact or_congr Iff.rfl and_comm

/-- The state records prefix equality and the existence of a first strict witness.
Indexed producers may inspect their ruler only through its length. -/
theorem binaryIndexedLexState_value {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (params : Fin p → List Bool) (E L : ℕ → Bool)
    (heq : ∀ r : List Bool, eq (Fin.cons r params) = [E r.length])
    (hlt : ∀ r : List Bool, lt (Fin.cons r params) = [L r.length])
    (clock : List Bool) :
    binaryIndexedLexState lt eq clock params =
      [decide (∀ i < clock.length, E i = true),
       decide (∃ i < clock.length, L i = true ∧ ∀ j < i, E j = true)] := by
  induction clock with
  | nil => simp [binaryIndexedLexState, recNotation]
  | cons b r ih =>
    simp only [binaryIndexedLexState, recNotation_cons, Bool.cond_self]
    change indexedLexStep lt eq (Fin.cons r (Fin.cons (binaryIndexedLexState lt eq r params) params)) = _
    rw [ih]
    simp only [indexedLexStep, Fin.cons_zero, Fin.cons_one, Fin.tail_cons, heq r, hlt r,
      List.length_cons]
    simp only [Nat.forall_lt_succ_right, indexedPrefix_succ, Bool.decide_and, Bool.decide_or]
    generalize decide (∀ i < r.length, E i = true) = e
    generalize decide (∃ i < r.length, L i = true ∧ ∀ j < i, E j = true) = l
    generalize E r.length = a
    generalize L r.length = b
    cases e <;> cases l <;> cases a <;> cases b <;> rfl
/-- The strict flag detects a coordinate whose entire earlier prefix is equal. -/
theorem binaryIndexedLexLT_value {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (params : Fin p → List Bool) (E L : ℕ → Prop) [DecidablePred E] [DecidablePred L]
    (heq : ∀ r : List Bool, eq (Fin.cons r params) = [decide (E r.length)])
    (hlt : ∀ r : List Bool, lt (Fin.cons r params) = [decide (L r.length)])
    (clock : List Bool) :
    binaryIndexedLexLT lt eq clock params =
      [decide (∃ i < clock.length, L i ∧ ∀ j < i, E j)] := by
  rw [binaryIndexedLexLT,
    binaryIndexedLexState_value lt eq params (fun i => decide (E i)) (fun i => decide (L i))
      heq hlt clock]
  simp only [decide_eq_true_eq]
  generalize decide (∀ i < clock.length, E i) = e
  generalize decide (∃ i < clock.length, L i ∧ ∀ j < i, E j) = l
  cases e <;> cases l <;> rfl

end GameTheory.Complexity.Backend
