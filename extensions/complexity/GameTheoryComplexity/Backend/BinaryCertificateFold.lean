module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import GameTheoryComplexity.Backend.WordFold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Bounded sums of binary fields scan polynomial-length clocks and tally blocks. -/
namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM
open scoped BigOperators

private def tallyStep (value _suffix accumulated : List Bool) (bit : Bool) : List Bool :=
  if bit then binaryCertificateAdd ![accumulated, value] else accumulated

/-- Add a preserved binary field once per true tally bit. -/
def binaryTallySum (tally value : List Bool) : List Bool :=
  WordFold.suffixFold
    (fun value _suffix accumulated bit =>
      if bit then binaryCertificateAdd ![accumulated, value] else accumulated)
    value [] tally

/-- The tally product's binary width grows at most once per scanned tally bit. -/
theorem binaryTallySum_length_le (tally value : List Bool) :
    (binaryTallySum tally value).length ≤ value.length + tally.length := by
  induction tally with
  | nil => simp [binaryTallySum]
  | cons bit tally ih =>
    rw [binaryTallySum, WordFold.suffixFold_cons]
    change (if bit then binaryCertificateAdd ![binaryTallySum tally value, value]
      else binaryTallySum tally value).length ≤ value.length + (tally.length + 1)
    cases bit
    · simpa using ih.trans (by omega)
    · simp only [ite_true]
      rw [binaryCertificateAdd_length]
      omega

/-- Tally multiplication counts bits, rather than iterating the binary field's value. -/
theorem binaryTallySum_value (tally value : List Bool) :
    ofBits (binaryTallySum tally value) = tally.count true * ofBits value := by
  induction tally with
  | nil => simp [binaryTallySum, ofBits]
  | cons bit tally ih =>
    rw [binaryTallySum, WordFold.suffixFold_cons]
    change ofBits (if bit then binaryCertificateAdd ![binaryTallySum tally value, value]
      else binaryTallySum tally value) = _
    cases bit
    · simpa [binaryTallySum] using ih
    · simp only [ite_true]
      rw [binaryCertificateAdd_value, ih]
      simp [Nat.add_mul]

private theorem binaryCertificateAdd_comp {Input : Type} {input : Input ↪ List Bool}
    {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binaryCertificateAdd ![x a, y a]) input encBits := by
  have htable : ComputableInPolyTime (fun a : Input => ![x a, y a]) input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hx
    · exact hy
  exact binaryCertificateAdd_polyTime.comp htable

/-- A uniform machine certificate for tally multiplication over any encoded input. -/
@[fun_prop] theorem binaryTallySum_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {tally value : Input → List Bool}
    (htally : ComputableInPolyTime tally input encBits)
    (hvalue : ComputableInPolyTime value input encBits) :
    ComputableInPolyTime (fun x => binaryTallySum (tally x) (value x)) input encBits := by
  let stateEncoding := encPair encBits (encPair encBits encBits)
  let stepInputEncoding := encPair stateEncoding encBool
  have hstep : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × Bool =>
        tallyStep p.1.1 p.1.2.1 p.1.2.2 p.2)
      stepInputEncoding encBits := by
    have hstate := ComputableInPolyTime.fst stateEncoding encBool
    have hvalue' := ComputableInPolyTime.fst encBits (encPair encBits encBits)
    have hvalue' := hvalue'.comp hstate
    have hpair := ComputableInPolyTime.snd encBits (encPair encBits encBits)
    have hpair := hpair.comp hstate
    have hacc := (ComputableInPolyTime.snd encBits encBits).comp hpair
    have hbit := ComputableInPolyTime.snd stateEncoding encBool
    have hadd := binaryCertificateAdd_comp hacc hvalue'
    exact hbit.ite hadd hacc
  have hbound : PolyBounded (fun x => (input x).length)
      (fun x => (value x).length + (tally x).length) :=
    hvalue.polyBounded_length.add htally.polyBounded_length
  exact WordFold.suffixFold_polyTime hvalue htally (.const []) hstep hbound
    (fun x suffix hsuffix => by
      have hlen := binaryTallySum_length_le suffix (value x)
      exact hlen.trans (Nat.add_le_add_left hsuffix.length_le _))

/-- Add an indexed binary term to the accumulated word. -/
def binarySumStep {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 2) → List Bool) : List Bool :=
  binaryCertificateAdd ![v 1, term (Fin.cons (v 0) (Fin.tail (Fin.tail v)))]

private def indexedStep {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (params : Fin p → List Bool) (suffix accumulated : List Bool) (_bit : Bool) : List Bool :=
  binaryCertificateAdd ![accumulated, term (Fin.cons suffix params)]

/-- Sum terms indexed by the successive suffix rulers of a bounded clock. -/
def binaryIndexedSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun params suffix accumulated _bit =>
      binaryCertificateAdd ![accumulated, term (Fin.cons suffix params)])
    params [] clock

/-- Summation adds at most one bit per term beyond the common term-width bound. -/
theorem binaryIndexedSum_length_le {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (width : (Fin p → List Bool) → List Bool)
    (hterm : ∀ r v, (term (Fin.cons r v)).length ≤ (width v).length)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedSum term clock params).length ≤ (width params).length + clock.length := by
  induction clock with
  | nil => simp [binaryIndexedSum]
  | cons bit clock ih =>
    rw [binaryIndexedSum, WordFold.suffixFold_cons]
    change (binaryCertificateAdd ![binaryIndexedSum term clock params,
      term (Fin.cons clock params)]).length ≤ _
    rw [binaryCertificateAdd_length]
    have ht := hterm clock params
    simp only [List.length_cons]
    omega

/-- A unary clock gives the usual finite sum in increasing suffix order. -/
theorem binaryIndexedSum_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (n : ℕ) (params : Fin p → List Bool) :
    ofBits (binaryIndexedSum term (List.replicate n true) params) =
      ∑ i ∈ Finset.range n, ofBits (term (Fin.cons (List.replicate i true) params)) := by
  induction n with
  | zero => simp [binaryIndexedSum, ofBits]
  | succ n ih =>
    simp only [List.replicate_succ]
    rw [binaryIndexedSum, WordFold.suffixFold_cons]
    change ofBits (binaryCertificateAdd ![
      binaryIndexedSum term (List.replicate n true) params,
      term (Fin.cons (List.replicate n true) params)]) = _
    rw [binaryCertificateAdd_value, ih, Finset.sum_range_succ]

private theorem indexedStep_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun q : ((Fin p → List Bool) × (List Bool × List Bool)) × Bool =>
        indexedStep term q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let contextStateEncoding :
      (Fin p → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair (encPi encBits) (encPair encBits encBits)
  have hstate := ComputableInPolyTime.fst contextStateEncoding encBool
  have hparams : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => q.1)
      contextStateEncoding (encPi encBits) :=
    ComputableInPolyTime.fst (encPi encBits) (encPair encBits encBits)
  have hcontextTail : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => q.2)
      contextStateEncoding (encPair encBits encBits) :=
    ComputableInPolyTime.snd (encPi encBits) (encPair encBits encBits)
  have hsuffix := ComputableInPolyTime.fst encBits encBits |>.comp hcontextTail
  have hacc := ComputableInPolyTime.snd encBits encBits |>.comp hcontextTail
  have htable : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) =>
        Fin.cons q.2.1 q.1)
      contextStateEncoding (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsuffix
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hparams
  have hterm' := hterm.comp htable
  have hsumTable : ComputableInPolyTime
      (fun q : (Fin p → List Bool) × (List Bool × List Bool) => ![q.2.2,
        term (Fin.cons q.2.1 q.1)]) contextStateEncoding (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hacc
    · exact hterm'
  exact (binaryCertificateAdd_polyTime.comp hsumTable).comp hstate

/-- A captured term and width bound yield a native certificate for a suffix-indexed sum. -/
@[fun_prop] theorem binaryIndexedSum_polyTime {p : ℕ} {Input : Type}
    {input : Input ↪ List Bool}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    {width : (Fin p → List Bool) → List Bool}
    {clock : Input → List Bool} {params : Input → Fin p → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits)
    (hwidth : ComputableInPolyTime width (encPi encBits) encBits)
    (htermBound : ∀ suffix v, (term (Fin.cons suffix v)).length ≤ (width v).length)
    (hclock : ComputableInPolyTime clock input encBits)
    (hparams : ComputableInPolyTime params input (encPi encBits)) :
    ComputableInPolyTime (fun x => binaryIndexedSum term (clock x) (params x)) input encBits := by
  let bound (x : Input) := (width (params x)).length + (clock x).length
  have hbound : PolyBounded (fun x => (input x).length) bound :=
    (hwidth.comp hparams).polyBounded_length.add hclock.polyBounded_length
  exact WordFold.suffixFold_polyTime hparams hclock (.const [])
    (indexedStep_polyTime hterm) hbound
    (fun x suffix hsuffix => by
      have hlen := binaryIndexedSum_length_le term width htermBound suffix (params x)
      exact hlen.trans (Nat.add_le_add_left hsuffix.length_le _))

end GameTheory.Complexity.Backend
