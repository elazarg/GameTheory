import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Bounded sums of binary fields scan polynomial-length clocks and tally blocks. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

/-- Add a preserved binary field once per true tally bit. -/
def binaryTallySum (tally value : List Bool) : List Bool :=
  recNotation (fun _ : Fin 1 → List Bool => [])
    (fun v : Fin 3 → List Bool => v 1)
    (fun v : Fin 3 → List Bool => binaryCertificateAdd ![v 1, v 2]) tally ![value]

/-- The tally product's binary width grows at most once per scanned tally bit. -/
theorem binaryTallySum_length_le (tally value : List Bool) :
    (binaryTallySum tally value).length ≤ value.length + tally.length := by
  induction tally with
  | nil => simp [binaryTallySum]
  | cons b tally ih =>
    cases b
    · simpa [binaryTallySum] using ih.trans (by omega)
    · change (binaryCertificateAdd ![binaryTallySum tally value, value]).length ≤ _
      rw [binaryCertificateAdd_length]
      simp only [List.length_cons]
      omega

/-- Tally multiplication has an actual polynomial-time binary machine certificate. -/
theorem binaryTallySum_cobham : Cobham fun v : Fin 2 → List Bool =>
    binaryTallySum (v 0) (v 1) := by
  have hs : Cobham fun v : Fin 3 → List Bool => binaryCertificateAdd ![v 1, v 2] :=
    Cobham.comp₂ binaryCertificateAdd_cobham (.proj 1) (.proj 2)
  have hj : Cobham fun v : Fin 2 → List Bool => v 1 ++ v 0 :=
    Cobham.appendFn (.proj 1) (.proj 0)
  exact (Cobham.boundedRec Cobham.empty (.proj 1) hs hj (fun r v => by
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    rw [hv]
    change (binaryTallySum r (v 0)).length ≤ ((v 0) ++ r).length
    rw [List.length_append]
    exact binaryTallySum_length_le r (v 0))).of_eq fun v => by
      congr 1
      ext i
      fin_cases i
      rfl

/-- Tally multiplication counts bits, rather than iterating the binary field's value. -/
theorem binaryTallySum_value (tally value : List Bool) :
    Nat.fromBitsLE (binaryTallySum tally value) = tally.count true * Nat.fromBitsLE value := by
  induction tally with
  | nil => simp [binaryTallySum, Nat.fromBitsLE, Nat.fromBits]
  | cons b tally ih =>
    cases b
    · simpa [binaryTallySum] using ih
    · change Nat.fromBitsLE (binaryCertificateAdd ![binaryTallySum tally value, value]) = _
      rw [binaryCertificateAdd_value, ih]
      simp [Nat.add_mul]

/-- Add an indexed binary term to the accumulated word. -/
def binarySumStep {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 2) → List Bool) : List Bool :=
  binaryCertificateAdd ![v 1, term (Fin.cons (v 0) (Fin.tail (Fin.tail v)))]

/-- Sum terms indexed by the successive suffix rulers of a bounded clock. -/
def binaryIndexedSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun _ => []) (binarySumStep term) (binarySumStep term) clock params

/-- Summation adds at most one bit per term beyond the common term-width bound. -/
theorem binaryIndexedSum_length_le {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (width : (Fin p → List Bool) → List Bool)
    (hterm : ∀ r v, (term (Fin.cons r v)).length ≤ (width v).length)
    (clock : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedSum term clock params).length ≤ (width params).length + clock.length := by
  induction clock with
  | nil => simp [binaryIndexedSum]
  | cons b clock ih =>
    simp only [binaryIndexedSum, recNotation_cons, Bool.cond_self]
    change (binaryCertificateAdd ![binaryIndexedSum term clock params,
      term (Fin.cons clock params)]).length ≤ _
    rw [binaryCertificateAdd_length]
    have ht := hterm clock params
    simp only [List.length_cons]
    omega

/-- Bounded indexed sums preserve genuine Cobham machine certificates. -/
theorem binaryIndexedSum_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    {width : (Fin p → List Bool) → List Bool}
    (ht : Cobham term) (hw : Cobham width)
    (hterm : ∀ r v, (term (Fin.cons r v)).length ≤ (width v).length) :
    Cobham fun v : Fin (p + 1) → List Bool => binaryIndexedSum term (v 0) (Fin.tail v) := by
  have hs : Cobham (binarySumStep term) := by
    apply Cobham.comp₂ binaryCertificateAdd_cobham (.proj 1)
    apply Cobham.comp ht
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Cobham.proj 0
    · exact Cobham.proj j.succ.succ
  have hj : Cobham fun v : Fin (p + 1) → List Bool => width (Fin.tail v) ++ v 0 :=
    Cobham.appendFn (Cobham.comp hw fun i => .proj i.succ) (.proj 0)
  exact (Cobham.boundedRec Cobham.empty hs hs hj (fun r v => by
    change (binaryIndexedSum term r v).length ≤ (width v ++ r).length
    rw [List.length_append]
    exact binaryIndexedSum_length_le term width hterm r v)).of_eq fun _ => rfl

/-- A unary clock gives the usual finite sum in increasing index order. -/
theorem binaryIndexedSum_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (n : ℕ) (params : Fin p → List Bool) :
    Nat.fromBitsLE (binaryIndexedSum term (List.replicate n true) params) =
      ∑ i ∈ Finset.range n, Nat.fromBitsLE (term (Fin.cons (List.replicate i true) params)) := by
  induction n with
  | zero => simp [binaryIndexedSum, Nat.fromBitsLE, Nat.fromBits]
  | succ n ih =>
    change Nat.fromBitsLE (binaryCertificateAdd ![
      binaryIndexedSum term (List.replicate n true) params,
      term (Fin.cons (List.replicate n true) params)]) = _
    rw [binaryCertificateAdd_value, ih, Finset.sum_range_succ]

end GameTheory.Complexity.Backend
