import GameTheoryComplexity.Backend.BinarySignedFixedWidth
import GameTheoryComplexity.Backend.BinarySignedRowComparison

/-! Fixed-width accumulation and packed-row dot products.

Clocks and field widths are length rulers. Every stored accumulator is normalized
immediately; correctness requires the mathematical prefix sums to fit the supplied
field. The machine remains total when that bound is not satisfied.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

private def signedSumStep {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 3) → List Bool) : List Bool :=
  binarySignedFixedAdd (v 2) (v 1)
    (term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))))

/-- Accumulate indexed signed terms, storing exactly one fixed-width signed field. -/
def binarySignedSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun v : Fin (p + 1) → List Bool => binarySignedFixed (v 0) [])
    (signedSumStep term) (signedSumStep term) clock (Fin.cons width params)

@[simp] theorem binarySignedSum_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    (binarySignedSum term clock width params).length = width.length := by
  cases clock with
  | nil => exact binarySignedFixed_length _ _
  | cons b r =>
    simp only [binarySignedSum, recNotation_cons, Bool.cond_self, signedSumStep,
      Fin.cons_one, Fin.cons_zero, binarySignedFixedAdd_length]
    rfl

theorem binarySignedSum_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (width : List Bool) (params : Fin p → List Bool) (f : ℕ → ℤ)
    (hterm : ∀ r : List Bool, binarySignedValue (term (Fin.cons r params)) = f r.length)
    (hr : 0 < width.length) (clock : List Bool)
    (hbound : ∀ t ≤ clock.length, (∑ i ∈ Finset.range t, f i).natAbs < 2 ^ (width.length - 1)) :
    binarySignedValue (binarySignedSum term clock width params) =
      ∑ i ∈ Finset.range clock.length, f i := by
  induction clock with
  | nil =>
    change binarySignedValue (binarySignedFixed width []) = _
    rw [binarySignedFixed_value width [] hr (by simp [binarySignedValue, Nat.fromBitsLE, Nat.fromBits])]
    simp [binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  | cons b r ih =>
    have hp : ∀ t ≤ r.length, (∑ i ∈ Finset.range t, f i).natAbs < 2 ^ (width.length - 1) := by
      intro t ht
      exact hbound t (ht.trans (by simp))
    have hv := ih hp
    simp only [binarySignedSum, recNotation_cons, Bool.cond_self]
    change binarySignedValue (binarySignedFixedAdd width
      (binarySignedSum term r width params) (term (Fin.cons r params))) = _
    have hh : (binarySignedValue (binarySignedSum term r width params) +
        binarySignedValue (term (Fin.cons r params))).natAbs < 2 ^ (width.length - 1) := by
      rw [hv, hterm r, ← Finset.sum_range_succ]
      exact hbound (r.length + 1) (by simp)
    rw [binarySignedFixedAdd_value _ _ _ hr hh, hv, hterm r]
    simp only [List.length_cons, Finset.sum_range_succ]

theorem binarySignedSum_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    Cobham fun v : Fin (p + 2) → List Bool =>
      binarySignedSum term (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  have hg : Cobham fun v : Fin (p + 1) → List Bool => binarySignedFixed (v 0) [] :=
    (Cobham.comp₂ binarySignedFixed_cobham (.proj 0) (Cobham.const [])).of_eq fun _ => rfl
  have hterm : Cobham fun v : Fin (p + 3) → List Bool =>
      term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))) := by
    apply Cobham.comp ht
    intro i
    exact Fin.cases (.proj 0) (fun j => .proj j.succ.succ.succ) i
  have hs : Cobham (signedSumStep term) :=
    (Cobham.comp₃ binarySignedFixedAdd_cobham (.proj 2) (.proj 1) hterm).of_eq fun _ => rfl
  exact (Cobham.boundedRec hg hs hs (.proj 1) (fun r v => by
    have hv : v = Fin.cons (v 0) (Fin.tail v) := by
      ext i
      cases i using Fin.cases <;> rfl
    rw [hv]
    change (binarySignedSum term r (v 0) (Fin.tail v)).length ≤ (v 0).length
    exact (binarySignedSum_length _ _ _ _).le)).of_eq fun v => by
      congr 1
      ext i
      cases i using Fin.cases <;> rfl

theorem binarySignedSum_mem_FPn {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    FPn (fun v : Fin (p + 2) → List Bool =>
      binarySignedSum term (v 0) (v 1) (Fin.tail (Fin.tail v))) :=
  cobham_iff_FPn.mp (binarySignedSum_cobham ht)

private def signedDotTerm (v : Fin 4 → List Bool) : List Bool :=
  binarySignedMul (binarySignedRowField ![v 0, v 1, v 2])
    (binarySignedRowField ![v 0, v 1, v 3])

/-- Dot product of two packed signed rows, with fixed-width prefix accumulators. -/
def binarySignedDot (clock width x y : List Bool) : List Bool :=
  binarySignedSum signedDotTerm clock width ![width, x, y]

@[simp] theorem binarySignedDot_length (clock width x y : List Bool) :
    (binarySignedDot clock width x y).length = width.length := binarySignedSum_length _ _ _ _

theorem binarySignedDot_value (clock width x y : List Bool) (hr : 0 < width.length)
    (hbound : ∀ t ≤ clock.length,
      (∑ i ∈ Finset.range t, binarySignedRowValue width x i * binarySignedRowValue width y i).natAbs <
        2 ^ (width.length - 1)) :
    binarySignedValue (binarySignedDot clock width x y) =
      ∑ i ∈ Finset.range clock.length, binarySignedRowValue width x i * binarySignedRowValue width y i := by
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binarySignedMul_value _ _

theorem binarySignedDot_cobham : Cobham fun v : Fin 4 → List Bool =>
    binarySignedDot (v 0) (v 1) (v 2) (v 3) := by
  have ht : Cobham signedDotTerm :=
    (Cobham.comp₂ binarySignedMul_cobham
      (Cobham.comp₃ binarySignedRowField_cobham (.proj 0) (.proj 1) (.proj 2))
      (Cobham.comp₃ binarySignedRowField_cobham (.proj 0) (.proj 1) (.proj 3))).of_eq fun _ => rfl
  have h := Cobham.comp (binarySignedSum_cobham ht)
    (fun i : Fin 5 => (Cobham.proj (![0, 1, 1, 2, 3] i) : Cobham fun v : Fin 4 → List Bool =>
      v (![0, 1, 1, 2, 3] i)))
  exact h.of_eq fun v => by
    change binarySignedSum signedDotTerm (v 0) (v 1) _ =
      binarySignedSum signedDotTerm (v 0) (v 1) ![v 1, v 2, v 3]
    congr 1
    ext i
    fin_cases i <;> rfl

theorem binarySignedDot_mem_FPn :
    FPn (fun v : Fin 4 → List Bool => binarySignedDot (v 0) (v 1) (v 2) (v 3)) :=
  cobham_iff_FPn.mp binarySignedDot_cobham

private def signedTableStep {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 3) → List Bool) : List Bool :=
  v 1 ++ binarySignedFixed (v 2)
    (term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))))

/-- Materialize indexed entries as a packed table of fixed-width signed fields. -/
def binarySignedTable {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun _ : Fin (p + 1) → List Bool => [])
    (signedTableStep term) (signedTableStep term) clock (Fin.cons width params)

@[simp] theorem binarySignedTable_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    (binarySignedTable term clock width params).length = clock.length * width.length := by
  induction clock with
  | nil => simp [binarySignedTable]
  | cons b r ih =>
    simp only [binarySignedTable, recNotation_cons, Bool.cond_self]
    change (binarySignedTable term r width params ++
      binarySignedFixed width (term (Fin.cons r params))).length = _
    rw [List.length_append, ih, binarySignedFixed_length, List.length_cons, Nat.succ_mul]

theorem binarySignedTable_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    Cobham fun v : Fin (p + 2) → List Bool =>
      binarySignedTable term (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  have hterm : Cobham fun v : Fin (p + 3) → List Bool =>
      term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))) := by
    apply Cobham.comp ht
    intro i
    exact Fin.cases (.proj 0) (fun j => .proj j.succ.succ.succ) i
  have hs : Cobham (signedTableStep term) :=
    Cobham.appendFn (.proj 1) (Cobham.comp₂ binarySignedFixed_cobham (.proj 2) hterm)
  exact (Cobham.boundedRec Cobham.empty hs hs
    (Cobham.comp₂ Cobham.smash (.proj 0) (.proj 1)) (fun r v => by
      have hv : v = Fin.cons (v 0) (Fin.tail v) := by
        ext i
        cases i using Fin.cases <;> rfl
      rw [hv]
      change (binarySignedTable term r (v 0) (Fin.tail v)).length ≤ _
      rw [binarySignedTable_length, smash_length]
      exact le_rfl)).of_eq fun v => by
        congr 1
        ext i
        cases i using Fin.cases <;> rfl

theorem binarySignedTable_mem_FPn {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    FPn (fun v : Fin (p + 2) → List Bool =>
      binarySignedTable term (v 0) (v 1) (Fin.tail (Fin.tail v))) :=
  cobham_iff_FPn.mp (binarySignedTable_cobham ht)

theorem rowValue_append_left (width x y : List Bool) (i : ℕ)
    (h : (i + 1) * width.length ≤ x.length) :
    binarySignedRowValue width (x ++ y) i = binarySignedRowValue width x i := by
  have ho : i * width.length ≤ x.length := by nlinarith
  have ht : width.length ≤ (x.drop (i * width.length)).length := by
    rw [List.length_drop]
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  unfold binarySignedRowValue
  rw [List.drop_append_of_le_length ho, List.take_append_of_le_length ht]

/-- Every stored table field retains the supplied term's value when it fits the width. -/
theorem binarySignedTable_value {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (width : List Bool) (params : Fin p → List Bool) (f : ℕ → ℤ)
    (hterm : ∀ r : List Bool, binarySignedValue (term (Fin.cons r params)) = f r.length)
    (hr : 0 < width.length) (clock : List Bool)
    (hbound : ∀ i < clock.length, (f i).natAbs < 2 ^ (width.length - 1))
    (i : ℕ) (hi : i < clock.length) :
    binarySignedRowValue width (binarySignedTable term clock width params) i = f i := by
  induction clock generalizing i with
  | nil => simp at hi
  | cons b r ih =>
    simp only [binarySignedTable, recNotation_cons, Bool.cond_self]
    change binarySignedRowValue width (binarySignedTable term r width params ++
      binarySignedFixed width (term (Fin.cons r params))) i = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [rowValue_append_left]
      · exact ih (fun j hj => hbound j (Nat.lt_succ_of_lt hj)) i hi
      · rw [binarySignedTable_length]
        exact Nat.mul_le_mul_right width.length (Nat.succ_le_of_lt hi)
    · unfold binarySignedRowValue
      rw [← binarySignedTable_length term r width params, List.drop_append_length,
        List.take_of_length_le (binarySignedFixed_length _ _).le]
      have hb : (binarySignedValue (term (Fin.cons r params))).natAbs < 2 ^ (width.length - 1) := by
        rw [hterm r]
        exact hbound r.length (by simp)
      exact (binarySignedFixed_value _ _ hr hb).trans (hterm r)

theorem binarySignedTable_field {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) (i : ℕ) (hi : i < clock.length) :
    ((binarySignedTable term clock width params).drop (i * width.length)).take width.length =
      binarySignedFixed width (term (Fin.cons (clock.drop (clock.length - i)) params)) := by
  induction clock generalizing i with
  | nil => simp at hi
  | cons b r ih =>
    simp only [binarySignedTable, recNotation_cons, Bool.cond_self]
    change ((binarySignedTable term r width params ++
      binarySignedFixed width (term (Fin.cons r params))).drop (i * width.length)).take width.length = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have ho : i * width.length ≤ (binarySignedTable term r width params).length := by
        rw [binarySignedTable_length]
        exact Nat.mul_le_mul_right _ (Nat.le_of_lt hi)
      have ht : width.length ≤ ((binarySignedTable term r width params).drop (i * width.length)).length := by
        rw [List.length_drop, binarySignedTable_length]
        have h := Nat.mul_le_mul_right width.length (Nat.succ_le_of_lt hi)
        rw [Nat.succ_mul] at h
        omega
      rw [List.drop_append_of_le_length ho, List.take_append_of_le_length ht, ih i hi]
      congr 3
      have he : (b :: r).length - i = (r.length - i) + 1 := by simp only [List.length_cons]; omega
      rw [he, List.drop_succ_cons]
    · rw [← binarySignedTable_length term r width params, List.drop_append_length,
        List.take_of_length_le (binarySignedFixed_length _ _).le]
      simp
/-- Materializing singleton flags preserves their bytes, including true sign-only fields. -/
theorem binarySignedTable_flags {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (params : Fin p → List Bool)
    (f : ℕ → Bool) (ht : ∀ r, term (Fin.cons r params) = [f r.length]) (clock : List Bool) :
    binarySignedTable term clock [false] params = (List.range clock.length).map f := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [binarySignedTable, recNotation_cons, Bool.cond_self]
    change binarySignedTable term r [false] params ++
      binarySignedFixed [false] (term (Fin.cons r params)) = _
    rw [ih, ht, binarySignedFixed_eq_of_length [false] [f r.length] rfl]
    simp [List.range_succ]

end GameTheory.Complexity.Backend
