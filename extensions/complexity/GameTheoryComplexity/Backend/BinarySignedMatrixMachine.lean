module

public import GameTheory.Math.FixedBlockList
public import GameTheoryComplexity.Backend.BinarySignedFixedWidth
public import GameTheoryComplexity.Backend.BinarySignedRowComparison
public import GameTheoryComplexity.Backend.WordFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! Fixed-width accumulation and packed-row dot products.

Clocks and field widths are length rulers. Every stored accumulator is normalized
immediately; correctness requires the mathematical prefix sums to fit the supplied
field. The machine remains total when that bound is not satisfied.
-/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open scoped BigOperators

private def signedSumStep {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (context : Fin (p + 1) → List Bool) (suffix state : List Bool) (_bit : Bool) : List Bool :=
  binarySignedFixedAdd (context 0) state
    (term (Fin.cons suffix (Fin.tail context)))

/-- Accumulate indexed signed terms, storing exactly one fixed-width signed field. -/
def binarySignedSum {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun (context : Fin (p + 1) → List Bool) suffix state _bit =>
      binarySignedFixedAdd (context 0) state (term (Fin.cons suffix (Fin.tail context))))
    (Fin.cons width params : Fin (p + 1) → List Bool)
    (binarySignedFixed width []) clock

@[simp] theorem binarySignedSum_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    (binarySignedSum term clock width params).length = width.length := by
  cases clock with
  | nil => exact binarySignedFixed_length _ _
  | cons b r =>
    rw [binarySignedSum, WordFold.suffixFold_cons]
    change (binarySignedFixedAdd width (binarySignedSum term r width params)
      (term (Fin.cons r params))).length = width.length
    exact binarySignedFixedAdd_length _ _ _

private theorem signedSumStep_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        signedSumStep term q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let encContext : (Fin (p + 1) → List Bool) ↪ List Bool := encPi encBits
  let encMiddle : (Fin (p + 1) → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair encContext (encPair encBits encBits)
  have hmiddle : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1)
      (encPair encMiddle encBool) encMiddle := ComputableInPolyTime.fst encMiddle encBool
  have hcontext : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) encContext :=
    (ComputableInPolyTime.fst encContext (encPair encBits encBits)).comp hmiddle
  have hcontext' : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    simpa [encContext] using hcontext
  have htail : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.1)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hstate : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.2)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hparams : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        Fin.tail q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    exact (ComputableInPolyTime.pi_apply encBits (Fin.succ j)).comp hcontext'
  have htable : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        (Fin.cons q.1.2.1 (Fin.tail q.1.1) : Fin (p + 1) → List Bool))
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact htail
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hparams
  exact binarySignedFixedAdd_polyTime
    ((ComputableInPolyTime.pi_apply encBits 0).comp hcontext)
    hstate (hterm.comp htable)

@[fun_prop] theorem binarySignedSum_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool =>
        binarySignedSum term (v 0) (v 1) (Fin.tail (Fin.tail v)))
      (encPi encBits) encBits := by
  have hclock : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool => v 0) (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool => v 1) (encPi encBits) encBits := .pi_apply encBits 1
  have hparams : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool =>
        (Fin.cons (v 1) (Fin.tail (Fin.tail v)) : Fin (p + 1) → List Bool))
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwidth
    · exact .pi_apply encBits (Fin.succ (Fin.succ j))
  have hinitial : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool => binarySignedFixed (v 1) [])
      (encPi encBits) encBits :=
    binarySignedFixed_polyTime hwidth (.const [])
  exact WordFold.suffixFold_polyTime hparams hclock hinitial
    (signedSumStep_polyTime hterm) hwidth.polyBounded_length
    (fun v suffix _ => by
      simpa [binarySignedSum] using
        (binarySignedSum_length term suffix (v 1) (Fin.tail (Fin.tail v))).le)

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
    have hz : (binarySignedValue ([] : List Bool)).natAbs = 0 := by
      rw [binarySignedValue_natAbs]
      rfl
    rw [binarySignedFixed_value width [] hr (by rw [hz]; exact Nat.pow_pos (by decide))]
    simp [binarySignedValue, ofBits]
  | cons b r ih =>
    have hp : ∀ t ≤ r.length, (∑ i ∈ Finset.range t, f i).natAbs < 2 ^ (width.length - 1) := by
      intro t ht
      exact hbound t (ht.trans (by simp))
    have hv := ih hp
    simp only [binarySignedSum, WordFold.suffixFold_cons]
    change binarySignedValue (binarySignedFixedAdd width
      (binarySignedSum term r width params) (term (Fin.cons r params))) = _
    have hh : (binarySignedValue (binarySignedSum term r width params) +
        binarySignedValue (term (Fin.cons r params))).natAbs < 2 ^ (width.length - 1) := by
      rw [hv, hterm r, ← Finset.sum_range_succ]
      exact hbound (r.length + 1) (by simp)
    rw [binarySignedFixedAdd_value _ _ _ hr hh, hv, hterm r]
    simp only [List.length_cons, Finset.sum_range_succ]

private def signedDotTerm (v : Fin 4 → List Bool) : List Bool :=
  binarySignedMul (binarySignedRowField ![v 0, v 1, v 2])
    (binarySignedRowField ![v 0, v 1, v 3])

/-- Dot product of two packed signed rows, with fixed-width prefix accumulators. -/
def binarySignedDot (clock width x y : List Bool) : List Bool :=
  let term : (Fin 4 → List Bool) → List Bool := fun (v : Fin 4 → List Bool) =>
    binarySignedMul (binarySignedRowField ![v 0, v 1, v 2])
      (binarySignedRowField ![v 0, v 1, v 3])
  binarySignedSum term clock width ![width, x, y]

@[simp] theorem binarySignedDot_length (clock width x y : List Bool) :
    (binarySignedDot clock width x y).length = width.length := by
  change (binarySignedSum signedDotTerm clock width ![width, x, y]).length = width.length
  exact binarySignedSum_length _ _ _ _

theorem binarySignedDot_value (clock width x y : List Bool) (hr : 0 < width.length)
    (hbound : ∀ t ≤ clock.length,
      (∑ i ∈ Finset.range t, binarySignedRowValue width x i * binarySignedRowValue width y i).natAbs <
        2 ^ (width.length - 1)) :
    binarySignedValue (binarySignedDot clock width x y) =
      ∑ i ∈ Finset.range clock.length, binarySignedRowValue width x i * binarySignedRowValue width y i := by
  change binarySignedValue (binarySignedSum signedDotTerm clock width ![width, x, y]) = _
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binarySignedMul_value _ _

private theorem signedDotTerm_polyTime :
    ComputableInPolyTime signedDotTerm (encPi encBits) encBits := by
  have hleft : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 2]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
        ![v 0, v 1, v 2]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 2
    exact binarySignedRowField_polyTime.comp hargs
  have hright : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
      binarySignedRowField ![v 0, v 1, v 3]) (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
        ![v 0, v 1, v 3]) (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
      · exact .pi_apply encBits 3
    exact binarySignedRowField_polyTime.comp hargs
  exact binarySignedMul_polyTime hleft hright

@[fun_prop] theorem binarySignedDot_polyTime :
    ComputableInPolyTime (fun v : Fin 4 → List Bool =>
      binarySignedDot (v 0) (v 1) (v 2) (v 3)) (encPi encBits) encBits := by
  change ComputableInPolyTime
    (fun v : Fin 4 → List Bool =>
      binarySignedSum signedDotTerm (v 0) (v 1) ![v 1, v 2, v 3])
    (encPi encBits) encBits
  have hargs : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
      ![v 0, v 1, v 1, v 2, v 3]) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 1
    · exact .pi_apply encBits 2
    · exact .pi_apply encBits 3
  simpa [Function.comp_def, Fin.tail] using
    (binarySignedSum_polyTime signedDotTerm_polyTime).comp hargs

private def signedTableStep {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (context : Fin (p + 1) → List Bool) (suffix state : List Bool) (_bit : Bool) : List Bool :=
  state ++ binarySignedFixed (context 0) (term (Fin.cons suffix (Fin.tail context)))

/-- Materialize indexed entries as a packed table of fixed-width signed fields. -/
def binarySignedTable {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) : List Bool :=
  WordFold.suffixFold
    (fun (context : Fin (p + 1) → List Bool) suffix state _bit =>
      state ++ binarySignedFixed (context 0) (term (Fin.cons suffix (Fin.tail context))))
    (Fin.cons width params : Fin (p + 1) → List Bool) [] clock

private theorem signedTableStep_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        signedTableStep term q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let encContext : (Fin (p + 1) → List Bool) ↪ List Bool := encPi encBits
  let encMiddle : (Fin (p + 1) → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair encContext (encPair encBits encBits)
  have hmiddle : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1)
      (encPair encMiddle encBool) encMiddle := ComputableInPolyTime.fst encMiddle encBool
  have hcontext : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) encContext :=
    (ComputableInPolyTime.fst encContext (encPair encBits encBits)).comp hmiddle
  have hcontext' : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    simpa [encContext] using hcontext
  have htail : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.1)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hstate : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.2)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hparams : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        Fin.tail q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro j
    exact (ComputableInPolyTime.pi_apply encBits (Fin.succ j)).comp hcontext'
  have htable : ComputableInPolyTime
      (fun q : ((Fin (p + 1) → List Bool) × (List Bool × List Bool)) × Bool =>
        (Fin.cons q.1.2.1 (Fin.tail q.1.1) : Fin (p + 1) → List Bool))
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact htail
    · exact (ComputableInPolyTime.pi_apply encBits j).comp hparams
  have hfield := binarySignedFixed_polyTime
    ((ComputableInPolyTime.pi_apply encBits 0).comp hcontext) (hterm.comp htable)
  exact ComputableInPolyTime.bitsAppend hstate hfield

@[simp] theorem binarySignedTable_length {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    (binarySignedTable term clock width params).length = clock.length * width.length := by
  induction clock with
  | nil => simp [binarySignedTable]
  | cons b r ih =>
    simp only [binarySignedTable, WordFold.suffixFold_cons]
    change (binarySignedTable term r width params ++
      binarySignedFixed width (term (Fin.cons r params))).length = _
    rw [List.length_append, ih, binarySignedFixed_length, List.length_cons, Nat.succ_mul]

@[fun_prop] theorem binarySignedTable_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool =>
        binarySignedTable term (v 0) (v 1) (Fin.tail (Fin.tail v)))
      (encPi encBits) encBits := by
  have hclock : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool => v 0) (encPi encBits) encBits := .pi_apply encBits 0
  have hwidth : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool => v 1) (encPi encBits) encBits := .pi_apply encBits 1
  have hparams : ComputableInPolyTime
      (fun v : Fin (p + 2) → List Bool =>
        (Fin.cons (v 1) (Fin.tail (Fin.tail v)) : Fin (p + 1) → List Bool))
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwidth
    · exact .pi_apply encBits (Fin.succ (Fin.succ j))
  have hbound : PolyBounded (fun v : Fin (p + 2) → List Bool => (encPi encBits v).length)
      (fun v => (v 0).length * (v 1).length) := by
    exact (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.length_bits_comp hclock)
      (ComputableInPolyTime.length_bits_comp hwidth)).polyBounded
  exact WordFold.suffixFold_polyTime hparams hclock (.const [])
    (signedTableStep_polyTime hterm) hbound
    (fun v suffix hsub => by
      have hlength :
          (WordFold.suffixFold
            (fun (context : Fin (p + 1) → List Bool) suffix state _bit =>
              state ++ binarySignedFixed (context 0)
                (term (Fin.cons suffix (Fin.tail context))))
            (Fin.cons (v 1) (Fin.tail (Fin.tail v))) [] suffix).length =
            suffix.length * (v 1).length := by
        simpa [binarySignedTable] using
          (binarySignedTable_length term suffix (v 1) (Fin.tail (Fin.tail v)))
      have hmul := Nat.mul_le_mul_right (v 1).length hsub.length_le
      rw [hlength]
      exact hmul)

/-- The materialized table concatenates its fixed-width fields in increasing index order. -/
theorem binarySignedTable_eq_flatMap {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    binarySignedTable term clock width params = (List.range clock.length).flatMap
      (fun i => binarySignedFixed width (term (Fin.cons (clock.drop (clock.length - i)) params))) := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [binarySignedTable, WordFold.suffixFold_cons]
    change binarySignedTable term r width params ++
      binarySignedFixed width (term (Fin.cons r params)) = _
    rw [ih, List.length_cons, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    · simp only [List.flatMap_def]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro i hi
      have hi : i < r.length := List.mem_range.mp hi
      have he : r.length + 1 - i = (r.length - i) + 1 := by omega
      rw [he, List.drop_succ_cons]
    · simp

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
    simp only [binarySignedTable, WordFold.suffixFold_cons]
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
  rw [binarySignedTable_eq_flatMap]
  have h := GameTheory.Math.FixedBlockList.block_flatMap_fixed (List.range clock.length)
    (fun j => binarySignedFixed width (term (Fin.cons (clock.drop (clock.length - j)) params)))
    width.length (fun _ _ => binarySignedFixed_length _ _) i (by simpa using hi)
  simpa using h

/-- Materializing singleton flags preserves their bytes, including true sign-only fields. -/
theorem binarySignedTable_flags {p : ℕ}
    (term : (Fin (p + 1) → List Bool) → List Bool) (params : Fin p → List Bool)
    (f : ℕ → Bool) (ht : ∀ r, term (Fin.cons r params) = [f r.length]) (clock : List Bool) :
    binarySignedTable term clock [false] params = (List.range clock.length).map f := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [binarySignedTable, WordFold.suffixFold_cons]
    change binarySignedTable term r [false] params ++
      binarySignedFixed [false] (term (Fin.cons r params)) = _
    rw [ih, ht, binarySignedFixed_eq_of_length [false] [f r.length] rfl]
    simp [List.range_succ]

end GameTheory.Complexity.Backend
