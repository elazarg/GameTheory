import GameTheoryComplexity.Backend.BinarySignedRowComparison
import GameTheory.Math.FiniteMinimumScan

/-! Bounded scans selecting the earliest eligible minimum of packed signed rows. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Extract a packed row using row-index, coefficient-count, and field-width rulers. -/
def binarySignedRowBlock (v : Fin 4 → List Bool) : List Bool :=
  ((v 3).drop ((v 0).length * (v 1).length * (v 2).length)).take
    ((v 1).length * (v 2).length)

theorem binarySignedRowBlock_cobham : Cobham binarySignedRowBlock :=
  (Cobham.takeFn (Cobham.comp₂ Cobham.smash (.proj 1) (.proj 2))
    (Cobham.dropFn (Cobham.comp₂ Cobham.smash
      (Cobham.comp₂ Cobham.smash (.proj 0) (.proj 1)) (.proj 2)) (.proj 3))).of_eq
        fun v => by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smash_length]
          rfl

/-- Decode one coefficient from a bounded packed row. -/
def binarySignedMatrixValue (count width coefficients : List Bool) (i j : ℕ) : ℤ :=
  binarySignedRowValue width
    ((coefficients.drop (i * count.length * width.length)).take (count.length * width.length)) j

/-- A coefficient inside a row agrees with its flat row-major field. -/
theorem binarySignedMatrixValue_eq_flat (count width coefficients : List Bool) (i j : ℕ)
    (hj : j < count.length) :
    binarySignedMatrixValue count width coefficients i j =
      binarySignedRowValue width coefficients (i * count.length + j) := by
  unfold binarySignedMatrixValue binarySignedRowValue
  rw [List.drop_take, List.drop_drop, List.take_take]
  have hm : width.length ≤ count.length * width.length - j * width.length := by
    have hb := Nat.mul_le_mul_right width.length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.add_mul]

/-- Decode a direction from the packed signed fields. -/
def binarySignedDirectionValue (width directions : List Bool) (i : ℕ) : ℤ :=
  binarySignedRowValue width directions i

/-- Interpret the found header and index-ruler tail of a selector output. -/
def binarySignedRowSelectedIndex (word : List Bool) : Option ℕ :=
  if word.headD false then some word.tail.length else none

private def decodedLT (count width coefficients directions : List Bool) (i j : ℕ) : Bool :=
  GameTheory.Math.FiniteLexicographicCompare.lexLT
    (fun a : Fin count.length => binarySignedMatrixValue count width coefficients i a.val *
      binarySignedDirectionValue width directions j)
    (fun a : Fin count.length => binarySignedMatrixValue count width coefficients j a.val *
      binarySignedDirectionValue width directions i)

private def candidateDirection (v : Fin 6 → List Bool) : List Bool :=
  binarySignedRowField ![v 0, v 3, v 5]

private def candidateLT (v : Fin 6 → List Bool) : List Bool :=
  binarySignedRowLT ![v 2, v 3,
    binarySignedRowBlock ![v 0, v 2, v 3, v 4],
    binarySignedRowBlock ![(v 1).tail, v 2, v 3, v 4],
    candidateDirection v, binarySignedRowField ![(v 1).tail, v 3, v 5]]

private def selectStep (v : Fin 6 → List Bool) : List Bool :=
  caseBit₀ (andBit (binarySignedLTFlag [] (candidateDirection v))
    (orBit (notBit (bitAt [] (v 1))) (candidateLT v))) (true :: v 0) (v 1)

private theorem candidateLT_value (v : Fin 6 → List Bool) :
    candidateLT v = [decodedLT (v 2) (v 3) (v 4) (v 5) (v 0).length (v 1).tail.length] := by
  rw [candidateLT, binarySignedRowLT_compare]
  rfl

private theorem selectStep_value (r state count width coefficients directions : List Bool) :
    binarySignedRowSelectedIndex (selectStep ![r, state, count, width, coefficients, directions]) =
      if 0 < binarySignedDirectionValue width directions r.length then
        match binarySignedRowSelectedIndex state with
        | none => some r.length
        | some j => if decodedLT count width coefficients directions r.length j then
            some r.length else some j
      else binarySignedRowSelectedIndex state := by
  unfold selectStep candidateDirection
  rw [binarySignedLTFlag_value, candidateLT_value]
  change binarySignedRowSelectedIndex
    (caseBit₀ (andBit [decide (0 < binarySignedDirectionValue width directions r.length)]
      (orBit (notBit (bitAt [] state))
        [decodedLT count width coefficients directions r.length state.tail.length]))
      (true :: r) state) = _
  by_cases h : 0 < binarySignedDirectionValue width directions r.length
  · cases state with
    | nil => simp [h, binarySignedRowSelectedIndex, andBit, orBit, notBit, bitAt, caseBit₀]
    | cons b state =>
      cases b
      · simp [h, binarySignedRowSelectedIndex, andBit, orBit, notBit, bitAt, caseBit₀]
      · simp only [List.tail_cons, binarySignedRowSelectedIndex, List.headD_cons,
          ↓reduceIte]
        by_cases hc : decodedLT count width coefficients directions r.length state.length = true
        · simp [h, hc, andBit, orBit, notBit, bitAt, caseBit₀]
        · have hc' : decodedLT count width coefficients directions r.length state.length = false :=
            Bool.eq_false_iff.mpr hc
          simp [h, hc', andBit, orBit, notBit, bitAt, caseBit₀]
  · simp [h, andBit, caseBit₀]

/-- Select an eligible minimum. Inputs are row count, coefficient count, field width,
packed coefficients, and packed directions. The output is a found bit followed by
an index ruler; its tail length is the selected index. -/
def binarySignedRowSelect (v : Fin 5 → List Bool) : List Bool :=
  recNotation (fun _ => [false]) selectStep selectStep (v 0) (Fin.tail v)

private theorem selectStep_length (v : Fin 6 → List Bool) :
    (selectStep v).length ≤ max (v 1).length ((v 0).length + 1) := by
  unfold selectStep
  generalize andBit _ _ = c
  cases c with
  | nil => simp [caseBit₀]
  | cons b c => cases b <;> simp [caseBit₀]

theorem binarySignedRowSelect_length (v : Fin 5 → List Bool) :
    (binarySignedRowSelect v).length ≤ (v 0).length + 1 := by
  have aux (r : List Bool) (p : Fin 4 → List Bool) :
      (recNotation (fun _ => [false]) selectStep selectStep r p).length ≤ r.length + 1 := by
    induction r with
    | nil => simp [recNotation]
    | cons b r ih =>
      simp only [recNotation_cons, Bool.cond_self]
      exact (selectStep_length _).trans (by
        simp only [Fin.cons_zero, Fin.cons_one, List.length_cons]
        exact max_le (ih.trans (by omega)) (by omega))
  exact aux _ _

private theorem selectStep_cobham : Cobham selectStep := by
  have hd : Cobham candidateDirection :=
    Cobham.comp₃ binarySignedRowField_cobham (.proj 0) (.proj 3) (.proj 5)
  have hrow (i : Fin 6) : Cobham fun v : Fin 6 → List Bool =>
      binarySignedRowBlock ![v i, v 2, v 3, v 4] := by
    apply Cobham.comp binarySignedRowBlock_cobham
    intro j
    fin_cases j
    · exact .proj i
    · exact .proj 2
    · exact .proj 3
    · exact .proj 4
  have hbestrow : Cobham fun v : Fin 6 → List Bool =>
      binarySignedRowBlock ![(v 1).tail, v 2, v 3, v 4] := by
    apply Cobham.comp binarySignedRowBlock_cobham
    intro j
    fin_cases j
    · exact Cobham.tailFn (.proj 1)
    · exact .proj 2
    · exact .proj 3
    · exact .proj 4
  have hlt : Cobham candidateLT := by
    apply Cobham.comp binarySignedRowLT_cobham
    intro i
    fin_cases i
    · exact .proj 2
    · exact .proj 3
    · exact hrow 0
    · exact hbestrow
    · exact hd
    · exact Cobham.comp₃ binarySignedRowField_cobham (Cobham.tailFn (.proj 1))
        (.proj 3) (.proj 5)
  exact Cobham.iteFn (Cobham.andFn
    (Cobham.comp₂ binarySignedLTFlag_cobham (Cobham.const []) hd)
    (Cobham.orFn (Cobham.notFn
      (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1))) hlt))
    (Cobham.appendFn (Cobham.const [true]) (.proj 0)) (.proj 1)

theorem binarySignedRowSelect_cobham : Cobham binarySignedRowSelect := by
  have hb : Cobham fun v : Fin 5 → List Bool => true :: v 0 :=
    Cobham.appendFn (Cobham.const [true]) (.proj 0)
  exact (Cobham.boundedRec (Cobham.const [false]) selectStep_cobham selectStep_cobham hb
    (fun r p => binarySignedRowSelect_length (Fin.cons r p))).of_eq fun _ => rfl

theorem binarySignedRowSelect_mem_FPn : FPn binarySignedRowSelect :=
  cobham_iff_FPn.mp binarySignedRowSelect_cobham

/-- The machine realizes the increasing-index finite minimum recurrence exactly. -/
theorem binarySignedRowSelect_value (v : Fin 5 → List Bool) :
    binarySignedRowSelectedIndex (binarySignedRowSelect v) =
      GameTheory.Math.FiniteMinimumScan.minimumPrefix
        (fun i => decide (0 < binarySignedDirectionValue (v 2) (v 4) i))
        (fun i j => GameTheory.Math.FiniteLexicographicCompare.lexLT
          (fun a : Fin (v 1).length => binarySignedMatrixValue (v 1) (v 2) (v 3) i a.val *
            binarySignedDirectionValue (v 2) (v 4) j)
          (fun a : Fin (v 1).length => binarySignedMatrixValue (v 1) (v 2) (v 3) j a.val *
            binarySignedDirectionValue (v 2) (v 4) i)) (v 0).length := by
  have aux (r : List Bool) (p : Fin 4 → List Bool) :
      binarySignedRowSelectedIndex
        (recNotation (fun _ => [false]) selectStep selectStep r p) =
      GameTheory.Math.FiniteMinimumScan.minimumPrefix
        (fun i => decide (0 < binarySignedDirectionValue (p 1) (p 3) i))
        (decodedLT (p 0) (p 1) (p 2) (p 3)) r.length := by
    induction r with
    | nil => rfl
    | cons b r ih =>
      simp only [recNotation_cons, Bool.cond_self]
      change binarySignedRowSelectedIndex (selectStep
        ![r, recNotation (fun _ => [false]) selectStep selectStep r p,
          p 0, p 1, p 2, p 3]) = _
      rw [selectStep_value, ih]
      simp only [List.length_cons, GameTheory.Math.FiniteMinimumScan.minimumPrefix,
        decide_eq_true_eq]
      rfl
  exact aux _ _

/-- Selection realizes the canonical finite prefix ratio scan on the decoded data. -/
theorem binarySignedRowSelect_selectPrefix (v : Fin 5 → List Bool) :
    binarySignedRowSelectedIndex (binarySignedRowSelect v) =
      GameTheory.Math.IntegerRatioSelection.selectPrefix
        (fun i : Fin (v 0).length => fun a : Fin (v 1).length =>
          binarySignedMatrixValue (v 1) (v 2) (v 3) i.val a.val)
        (fun i => binarySignedDirectionValue (v 2) (v 4) i.val) := by
  rw [binarySignedRowSelect_value]
  apply GameTheory.Math.FiniteMinimumScan.minimumPrefix_congr
  · intro i hi
    simp [GameTheory.Math.IntegerRatioSelection.prefixEligible, hi]
  · intro i hi j hj
    simp [GameTheory.Math.IntegerRatioSelection.prefixCompare, hi, hj,
      GameTheory.Math.IntegerRatioSelection.compare]

theorem binarySignedRowSelect_none (v : Fin 5 → List Bool) :
    binarySignedRowSelectedIndex (binarySignedRowSelect v) = none ↔
      ∀ i : Fin (v 0).length, binarySignedDirectionValue (v 2) (v 4) i.val ≤ 0 := by
  rw [binarySignedRowSelect_selectPrefix]
  exact GameTheory.Math.IntegerRatioSelection.selectPrefix_none _ _

theorem binarySignedRowSelect_mem (v : Fin 5 → List Bool) (s : ℕ)
    (hs : binarySignedRowSelectedIndex (binarySignedRowSelect v) = some s) :
    s < (v 0).length := by
  rw [binarySignedRowSelect_selectPrefix] at hs
  exact GameTheory.Math.IntegerRatioSelection.selectPrefix_mem _ _ s hs

/-- A selected index satisfies the canonical leaving-row predicate for the decoded data. -/
theorem binarySignedRowSelect_some_spec (v : Fin 5 → List Bool) (s : Fin (v 0).length)
    (hs : binarySignedRowSelectedIndex (binarySignedRowSelect v) = some s.val) :
    GameTheory.Math.IsLeavingRow
      (fun i => fun a : Fin (v 1).length =>
        (binarySignedMatrixValue (v 1) (v 2) (v 3) i.val a.val : ℚ))
      (fun i => (binarySignedDirectionValue (v 2) (v 4) i.val : ℚ)) s := by
  rw [binarySignedRowSelect_selectPrefix] at hs
  exact GameTheory.Math.IntegerRatioSelection.selectPrefix_some_spec _ _ s hs

end GameTheory.Complexity.Backend
