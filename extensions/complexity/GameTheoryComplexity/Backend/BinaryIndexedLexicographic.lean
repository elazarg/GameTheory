module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Polynomial-time lexicographic scans of indexed Boolean comparisons.

The two-bit state records whether the prefix is equal and whether it is less.
The clock is a word, so scanning never iterates a binary represented value.
-/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Scan indexed comparisons, retaining the first unequal coordinate. -/
def binaryIndexedLexState {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun params suffix state _bit =>
      let args := Fin.cons suffix params
      let prefixEqual := state.headD false
      let prefixLess := state.getD 1 false
      [prefixEqual && (eq args).headD false,
        prefixLess || (prefixEqual && (lt args).headD false)])
    params [true, false] clock

/-- Return the strict comparison bit from the scan's two-bit state. -/
def binaryIndexedLexLT {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  [(binaryIndexedLexState lt eq clock params).getD 1 false]

theorem binaryIndexedLexState_length {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedLexState lt eq clock params).length = 2 := by
  cases clock with
  | nil => rfl
  | cons b clock =>
    rw [binaryIndexedLexState, WordFold.suffixFold_cons]
    simp

@[simp] theorem binaryIndexedLexLT_length {p : ℕ}
    (lt eq : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedLexLT lt eq clock params).length = 1 := rfl

private theorem indexedLexStep_polyTime {p : ℕ}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    (hlt : ComputableInPolyTime lt (encPi encBits) encBits)
    (heq : ComputableInPolyTime eq (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        let args := Fin.cons q.2.1 q.1
        let prefixEqual := q.2.2.headD false
        let prefixLess := q.2.2.getD 1 false
        [prefixEqual && (eq args).headD false,
          prefixLess || (prefixEqual && (lt args).headD false)])
      (encPair (encPi encBits) (encPair encBits encBits)) encBits := by
  let paramsEncoding : (Fin p → List Bool) ↪ List Bool := encPi encBits
  let contextStateEncoding : (Fin p → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair paramsEncoding (encPair encBits encBits)
  have hparams := ComputableInPolyTime.fst paramsEncoding (encPair encBits encBits)
  have hstate := ComputableInPolyTime.snd paramsEncoding (encPair encBits encBits)
  have hsuffix := (ComputableInPolyTime.fst encBits encBits).comp hstate
  have hstates := (ComputableInPolyTime.snd encBits encBits).comp hstate
  have htable : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => Fin.cons q.2.1 q.1)
      contextStateEncoding (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsuffix
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hparams
  have hlt' := hlt.comp htable
  have heq' := heq.comp htable
  have hprefixEqual : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => q.2.2.headD false)
      contextStateEncoding encBool :=
    (ComputableInPolyTime.headD false).comp hstates
  have hprefixLess : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => q.2.2.getD 1 false)
      contextStateEncoding encBool :=
    (ComputableInPolyTime.headD false).comp
      (indexedFlag_polyTime.comp ((ComputableInPolyTime.const (1 : ℕ)).prod hstates))
  have heqBit : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        (eq (Fin.cons q.2.1 q.1)).headD false) contextStateEncoding encBool :=
    (ComputableInPolyTime.headD false).comp heq'
  have hltBit : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        (lt (Fin.cons q.2.1 q.1)).headD false) contextStateEncoding encBool :=
    (ComputableInPolyTime.headD false).comp hlt'
  have hnextEqual : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        q.2.2.headD false && (eq (Fin.cons q.2.1 q.1)).headD false)
      contextStateEncoding encBool :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bool_and.comp (hprefixEqual.tidy.prod heqBit.tidy))
  have hboth : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        q.2.2.headD false && (lt (Fin.cons q.2.1 q.1)).headD false)
      contextStateEncoding encBool :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bool_and.comp (hprefixEqual.tidy.prod hltBit.tidy))
  have hnextLess : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        q.2.2.getD 1 false ||
          (q.2.2.headD false && (lt (Fin.cons q.2.1 q.1)).headD false))
      contextStateEncoding encBool :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bool_or.comp (hprefixLess.tidy.prod hboth.tidy))
  exact ComputableInPolyTime.bitsCons hnextEqual
    (ComputableInPolyTime.bitsCons hnextLess (.const []))

/-- Certified lexicographic state scan for arbitrary encoded producers. -/
@[fun_prop] theorem binaryIndexedLexState_polyTime {p : ℕ} {Input : Type}
    {input : Input ↪ List Bool}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    {clock : Input → List Bool} {params : Input → Fin p → List Bool}
    (hlt : ComputableInPolyTime lt (encPi encBits) encBits)
    (heq : ComputableInPolyTime eq (encPi encBits) encBits)
    (hclock : ComputableInPolyTime clock input encBits)
    (hparams : ComputableInPolyTime params input (encPi encBits)) :
    ComputableInPolyTime
      (fun x => binaryIndexedLexState lt eq (clock x) (params x)) input encBits := by
  have hstep := (indexedLexStep_polyTime hlt heq).comp
    (ComputableInPolyTime.fst
      (encPair (encPi encBits) (encPair encBits encBits)) encBool)
  exact WordFold.suffixFold_polyTime hparams hclock
    (ComputableInPolyTime.const [true, false]) hstep (.const 2)
    (fun (x : Input) (suffix : List Bool) (_hsuffix : suffix <:+ clock x) => by
      simpa [binaryIndexedLexState] using
        (binaryIndexedLexState_length lt eq suffix (params x)).le)

/-- Certified strict result bit from the lexicographic state scan. -/
@[fun_prop] theorem binaryIndexedLexLT_polyTime {p : ℕ} {Input : Type}
    {input : Input ↪ List Bool}
    {lt eq : (Fin (p + 1) → List Bool) → List Bool}
    {clock : Input → List Bool} {params : Input → Fin p → List Bool}
    (hlt : ComputableInPolyTime lt (encPi encBits) encBits)
    (heq : ComputableInPolyTime eq (encPi encBits) encBits)
    (hclock : ComputableInPolyTime clock input encBits)
    (hparams : ComputableInPolyTime params input (encPi encBits)) :
    ComputableInPolyTime
      (fun x => binaryIndexedLexLT lt eq (clock x) (params x)) input encBits := by
  have hstate := binaryIndexedLexState_polyTime hlt heq hclock hparams
  exact indexedFlag_polyTime.comp ((ComputableInPolyTime.const (1 : ℕ)).prod hstate)

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
  | nil => simp [binaryIndexedLexState]
  | cons b r ih =>
    rw [binaryIndexedLexState, WordFold.suffixFold_cons]
    change [
      (binaryIndexedLexState lt eq r params).headD false &&
        (eq (Fin.cons r params)).headD false,
      (binaryIndexedLexState lt eq r params).getD 1 false ||
        ((binaryIndexedLexState lt eq r params).headD false &&
          (lt (Fin.cons r params)).headD false)] = _
    rw [ih]
    simp only [heq r, hlt r, List.headD_cons, List.getD_cons_zero,
      List.getD_cons_succ, List.length_cons]
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
