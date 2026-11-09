module

public import GameTheoryComplexity.Backend.BinarySignedRowComparison
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheoryComplexity.Backend.WordFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import GameTheory.Math.FiniteMinimumScan

@[expose] public section

/-! Bounded scans selecting the earliest eligible minimum of packed signed rows. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Extract a packed row using row-index, coefficient-count, and field-width rulers. -/
def binarySignedRowBlock (v : Fin 4 → List Bool) : List Bool :=
  ((v 3).drop ((v 0).length * (v 1).length * (v 2).length)).take
    ((v 1).length * (v 2).length)

@[fun_prop] theorem binarySignedRowBlock_polyTime :
    ComputableInPolyTime binarySignedRowBlock (encPi encBits) encBits := by
  have hi : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hc : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hw : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hword : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 3)
      (encPi encBits) encBits := .pi_apply encBits 3
  have hil := ComputableInPolyTime.length_bits_comp hi
  have hcl := ComputableInPolyTime.length_bits_comp hc
  have hwl := ComputableInPolyTime.length_bits_comp hw
  have hoffset := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_mul' hil hcl) hwl
  have hsize := ComputableInPolyTime.unary_mul' hcl hwl
  exact (hword.bitsDropWithInput hoffset).bitsTakeWithInput hsize

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
  select (andFlag (binarySignedLTFlag [] (candidateDirection v))
    (orFlag (notFlag (indexedFlag 0 (v 1))) (candidateLT v))) (true :: v 0) (v 1)

private def rowSelectStep (params : Fin 4 → List Bool)
    (suffix state : List Bool) (_bit : Bool) : List Bool :=
  selectStep ![suffix, state, params 0, params 1, params 2, params 3]

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
      (select (andFlag [decide (0 < binarySignedDirectionValue width directions r.length)]
      (orFlag (notFlag (indexedFlag 0 state))
        [decodedLT count width coefficients directions r.length state.tail.length]))
      (true :: r) state) = _
  by_cases h : 0 < binarySignedDirectionValue width directions r.length
  · cases state with
    | nil => simp [h, binarySignedRowSelectedIndex, andFlag, orFlag, notFlag, indexedFlag, select]
    | cons b state =>
      cases b
      · simp [h, binarySignedRowSelectedIndex, andFlag, orFlag, notFlag, indexedFlag, select]
      · simp only [List.tail_cons, binarySignedRowSelectedIndex, List.headD_cons,
          ↓reduceIte]
        by_cases hc : decodedLT count width coefficients directions r.length state.length = true
        · simp [h, hc, andFlag, orFlag, notFlag, indexedFlag, select]
        · have hc' : decodedLT count width coefficients directions r.length state.length = false :=
            Bool.eq_false_iff.mpr hc
          simp [h, hc', andFlag, orFlag, notFlag, indexedFlag, select]
  · simp [h, andFlag, select]

/-- Select an eligible minimum. Inputs are row count, coefficient count, field width,
packed coefficients, and packed directions. The output is a found bit followed by
an index ruler; its tail length is the selected index. -/
def binarySignedRowSelect (v : Fin 5 → List Bool) : List Bool :=
  let step : (Fin 4 → List Bool) → List Bool → List Bool → Bool → List Bool :=
    fun (params : Fin 4 → List Bool) (suffix state : List Bool) (_bit : Bool) =>
      let direction := binarySignedRowField ![suffix, params 1, params 3]
      let currentRow := binarySignedRowBlock ![suffix, params 0, params 1, params 2]
      let selectedRow :=
        binarySignedRowBlock ![state.tail, params 0, params 1, params 2]
      let selectedDirection := binarySignedRowField ![state.tail, params 1, params 3]
      let comparison := binarySignedRowLT ![params 0, params 1, currentRow,
        selectedRow, direction, selectedDirection]
      select (andFlag (binarySignedLTFlag [] direction)
        (orFlag (notFlag (indexedFlag 0 state)) comparison)) (true :: suffix) state
  WordFold.suffixFold step (Fin.tail v) [false] (v 0)

private theorem selectStep_length (v : Fin 6 → List Bool) :
    (selectStep v).length ≤ max (v 1).length ((v 0).length + 1) := by
  unfold selectStep
  generalize andFlag (binarySignedLTFlag [] (candidateDirection v))
    (orFlag (notFlag (indexedFlag 0 (v 1))) (candidateLT v)) = condition
  cases condition with
  | nil => simp [select]
  | cons b rest =>
    cases b
    · simp [select]
    · simp only [select, List.headD_cons, ↓reduceIte,
        List.length_cons]
      exact Nat.le_max_right _ _

private theorem selectStep_polyTime :
    ComputableInPolyTime selectStep (encPi encBits) encBits := by
  have h0 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have h1 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have h2 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have h3 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 3)
      (encPi encBits) encBits := .pi_apply encBits 3
  have h4 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 4)
      (encPi encBits) encBits := .pi_apply encBits 4
  have h5 : ComputableInPolyTime (fun v : Fin 6 → List Bool => v 5)
      (encPi encBits) encBits := .pi_apply encBits 5
  have hdirArgs : ComputableInPolyTime (fun v : Fin 6 → List Bool => ![v 0, v 3, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact h0
    · exact h3
    · exact h5
  have hdir := binarySignedRowField_polyTime.comp hdirArgs
  have hrowArgs : ComputableInPolyTime (fun v : Fin 6 → List Bool => ![v 0, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact h0
    · exact h2
    · exact h3
    · exact h4
  have hrow := binarySignedRowBlock_polyTime.comp hrowArgs
  have hbest : ComputableInPolyTime (fun v : Fin 6 → List Bool => (v 1).tail)
      (encPi encBits) encBits :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp h1
  have hbestRowArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![(v 1).tail, v 2, v 3, v 4])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hbest
    · exact h2
    · exact h3
    · exact h4
  have hbestRow := binarySignedRowBlock_polyTime.comp hbestRowArgs
  have hbestDirArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![(v 1).tail, v 3, v 5])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hbest
    · exact h3
    · exact h5
  have hbestDir := binarySignedRowField_polyTime.comp hbestDirArgs
  have hcompareArgs : ComputableInPolyTime
      (fun v : Fin 6 → List Bool => ![v 2, v 3,
        binarySignedRowBlock ![v 0, v 2, v 3, v 4],
        binarySignedRowBlock ![(v 1).tail, v 2, v 3, v 4],
        binarySignedRowField ![v 0, v 3, v 5],
        binarySignedRowField ![(v 1).tail, v 3, v 5]])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact h2
    · exact h3
    · exact hrow
    · exact hbestRow
    · exact hdir
    · exact hbestDir
  have hlt := binarySignedRowLT_polyTime.comp hcompareArgs
  have hpositive := binarySignedLTFlag_polyTime (ComputableInPolyTime.const []) hdir
  have hfound : ComputableInPolyTime (fun v : Fin 6 → List Bool => indexedFlag 0 (v 1))
      (encPi encBits) encBits :=
    indexedFlag_polyTime.comp ((ComputableInPolyTime.const (0 : ℕ)).prod h1)
  have hmissing := notFlag_polyTime.comp hfound
  have heligible := orFlag_polyTime.comp (hmissing.prod hlt)
  have hchoose := andFlag_polyTime.comp (hpositive.prod heligible)
  have hyes : ComputableInPolyTime (fun v : Fin 6 → List Bool => true :: v 0)
      (encPi encBits) encBits := ComputableInPolyTime.bitsCons
        (ComputableInPolyTime.const true) h0
  exact select_polyTime.comp (hchoose.prod (hyes.prod h1))

private theorem rowSelectStep_polyTime :
    ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool =>
        rowSelectStep q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let encContext : (Fin 4 → List Bool) ↪ List Bool := encPi encBits
  let encMiddle : (Fin 4 → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair encContext (encPair encBits encBits)
  have hmiddle : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool => q.1)
      (encPair encMiddle encBool) encMiddle := ComputableInPolyTime.fst encMiddle encBool
  have hcontext : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) encContext :=
    (ComputableInPolyTime.fst encContext (encPair encBits encBits)).comp hmiddle
  have hcontext' : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    simpa [encContext] using hcontext
  have hstate : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.2)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hsuffix : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.1)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hargs : ComputableInPolyTime
      (fun q : ((Fin 4 → List Bool) × (List Bool × List Bool)) × Bool =>
        ![q.1.2.1, q.1.2.2, q.1.1 0, q.1.1 1, q.1.1 2, q.1.1 3])
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsuffix
    · exact hstate
    · exact (ComputableInPolyTime.pi_apply encBits 0).comp hcontext'
    · exact (ComputableInPolyTime.pi_apply encBits 1).comp hcontext'
    · exact (ComputableInPolyTime.pi_apply encBits 2).comp hcontext'
    · exact (ComputableInPolyTime.pi_apply encBits 3).comp hcontext'
  exact selectStep_polyTime.comp hargs

theorem binarySignedRowSelect_length (v : Fin 5 → List Bool) :
    (binarySignedRowSelect v).length ≤ (v 0).length + 1 := by
  change (WordFold.suffixFold rowSelectStep (Fin.tail v) [false] (v 0)).length ≤
    (v 0).length + 1
  have aux (r : List Bool) (p : Fin 4 → List Bool) :
      (WordFold.suffixFold rowSelectStep p [false] r).length ≤ r.length + 1 := by
    induction r with
    | nil => simp [WordFold.suffixFold]
    | cons b r ih =>
      rw [WordFold.suffixFold_cons]
      have hstep := selectStep_length
        ![r, WordFold.suffixFold rowSelectStep p [false] r, p 0, p 1, p 2, p 3]
      exact hstep.trans (by simp [List.length_cons]; omega)
  exact aux _ _

@[fun_prop] theorem binarySignedRowSelect_polyTime :
    ComputableInPolyTime binarySignedRowSelect (encPi encBits) encBits := by
  change ComputableInPolyTime
    (fun v : Fin 5 → List Bool =>
      WordFold.suffixFold rowSelectStep (Fin.tail v) [false] (v 0))
    (encPi encBits) encBits
  have hclock : ComputableInPolyTime (fun v : Fin 5 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hparams : ComputableInPolyTime (fun v : Fin 5 → List Bool => Fin.tail v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact .pi_apply encBits (Fin.succ i)
  have hbound : PolyBounded (fun v : Fin 5 → List Bool => (encPi encBits v).length)
      (fun v => (v 0).length + 1) := hclock.polyBounded_length.add (.const 1)
  exact WordFold.suffixFold_polyTime hparams hclock (.const [false])
    rowSelectStep_polyTime hbound
    (fun v suffix hsub => by
      have hlength := binarySignedRowSelect_length (Fin.cons suffix (Fin.tail v))
      change (WordFold.suffixFold rowSelectStep (Fin.tail v) [false] suffix).length ≤
        suffix.length + 1 at hlength
      exact hlength.trans (Nat.add_le_add_right hsub.length_le 1))

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
  change binarySignedRowSelectedIndex
      (WordFold.suffixFold rowSelectStep (Fin.tail v) [false] (v 0)) = _
  have aux (r : List Bool) (p : Fin 4 → List Bool) :
      binarySignedRowSelectedIndex
        (WordFold.suffixFold rowSelectStep p [false] r) =
      GameTheory.Math.FiniteMinimumScan.minimumPrefix
        (fun i => decide (0 < binarySignedDirectionValue (p 1) (p 3) i))
        (decodedLT (p 0) (p 1) (p 2) (p 3)) r.length := by
    induction r with
    | nil => rfl
    | cons b r ih =>
      rw [WordFold.suffixFold_cons]
      change binarySignedRowSelectedIndex (selectStep
        ![r, WordFold.suffixFold rowSelectStep p [false] r,
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
