module

public import GameTheoryComplexity.Backend.BinarySignedFixedWidth
public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.WordOperations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Indexed guarded lookup retains actual suffix words and arbitrary captured
context. Selected values use fixed-width signed storage; missing or malformed
false-headed flags leave the accumulated word unchanged. -/
namespace GameTheory.Complexity.Backend
open Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Retain the last matching suffix value, with fixed-width signed zero as default. -/
def binaryIndexedLookup {Context : Type}
    (test term : List Bool → Context → List Bool)
    (clock width : List Bool) (params : Context) : List Bool :=
  WordFold.suffixFold
    (fun (context : List Bool × Context) (suffix accumulated : List Bool) (_bit : Bool) =>
      select (test suffix context.2)
        (binarySignedFixed context.1 (term suffix context.2)) accumulated)
    (width, params) (binarySignedFixed width []) clock

@[simp] theorem binaryIndexedLookup_length {Context : Type}
    (test term : List Bool → Context → List Bool)
    (clock width : List Bool) (params : Context) :
    (binaryIndexedLookup test term clock width params).length = width.length := by
  induction clock with
  | nil => simp [binaryIndexedLookup, WordFold.suffixFold_nil]
  | cons b r ih =>
    rw [binaryIndexedLookup, WordFold.suffixFold_cons]
    change (select (test r params) (binarySignedFixed width (term r params))
      (binaryIndexedLookup test term r width params)).length = _
    cases ht : test r params with
    | nil => simpa [select] using ih
    | cons bit tail =>
      cases bit <;> simp [select, binarySignedFixed_length, ih]

private theorem binaryIndexedLookup_step_polyTime {Context : Type}
    {paramsEncoding : Context ↪ List Bool}
    {test term : List Bool → Context → List Bool}
    (htest : ComputableInPolyTime (fun p : Context × List Bool => test p.2 p.1)
      (encPair paramsEncoding encBits) encBits)
    (hterm : ComputableInPolyTime (fun p : Context × List Bool => term p.2 p.1)
      (encPair paramsEncoding encBits) encBits) :
    ComputableInPolyTime
      (fun q : (List Bool × Context) × (List Bool × List Bool) =>
        select (test q.2.1 q.1.2)
          (binarySignedFixed q.1.1 (term q.2.1 q.1.2)) q.2.2)
      (encPair (encPair encBits paramsEncoding) (encPair encBits encBits)) encBits := by
  let contextEncoding : List Bool × Context ↪ List Bool := encPair encBits paramsEncoding
  let stateEncoding : List Bool × List Bool ↪ List Bool := encPair encBits encBits
  have hcontext := ComputableInPolyTime.fst contextEncoding stateEncoding
  have hwidth := hcontext.fst'
  have hparams := hcontext.snd'
  have hstate := ComputableInPolyTime.snd contextEncoding stateEncoding
  have hsuffix := hstate.fst'
  have hacc := hstate.snd'
  have hcallback := hparams.prod hsuffix
  have htest' := htest.comp hcallback
  have hterm' := hterm.comp hcallback
  have hfixed := binarySignedFixed_polyTime hwidth hterm'
  exact select_polyTime.comp (htest'.prod (hfixed.prod hacc))

/-- Both callbacks, the original suffix clock, width, context and fixed-width state are charged. -/
@[fun_prop] theorem binaryIndexedLookup_polyTime {Context Input : Type}
    {paramsEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    {test term : List Bool → Context → List Bool}
    {clock width : Input → List Bool} {params : Input → Context}
    (htest : ComputableInPolyTime (fun p : Context × List Bool => test p.2 p.1)
      (encPair paramsEncoding encBits) encBits)
    (hterm : ComputableInPolyTime (fun p : Context × List Bool => term p.2 p.1)
      (encPair paramsEncoding encBits) encBits)
    (hclock : ComputableInPolyTime clock input encBits)
    (hwidth : ComputableInPolyTime width input encBits)
    (hparams : ComputableInPolyTime params input paramsEncoding) :
    ComputableInPolyTime
      (fun x => binaryIndexedLookup test term (clock x) (width x) (params x)) input encBits := by
  let contextEncoding : List Bool × Context ↪ List Bool := encPair encBits paramsEncoding
  let stateEncoding : List Bool × List Bool ↪ List Bool := encPair encBits encBits
  let contextStateEncoding : (List Bool × Context) × (List Bool × List Bool) ↪ List Bool :=
    encPair contextEncoding stateEncoding
  have hcontext := hwidth.prod hparams
  have hinitial := binarySignedFixed_polyTime hwidth (ComputableInPolyTime.const [])
  have hbound : PolyBounded (fun x => (input x).length) (fun x => (width x).length) :=
    hwidth.polyBounded_length
  have hstep := (binaryIndexedLookup_step_polyTime htest hterm).comp
    (ComputableInPolyTime.fst contextStateEncoding encBool)
  exact WordFold.suffixFold_polyTime hcontext hclock hinitial hstep hbound
    (fun x suffix hsuffix => by
      simpa [binaryIndexedLookup] using
        (binaryIndexedLookup_length test term suffix (width x) (params x)).le)

/-- Equal values at every matching index give an exact total lookup interpretation. -/
theorem binaryIndexedLookup_value {Context : Type}
    (test term : List Bool → Context → List Bool)
    (width : List Bool) (params : Context) (hit : ℕ → Bool) (z : ℤ)
    (htest : ∀ r, test r params = [hit r.length])
    (hterm : ∀ r, hit r.length = true → binarySignedValue (term r params) = z)
    (hw : 0 < width.length) (hz : z.natAbs < 2 ^ (width.length - 1)) (clock : List Bool) :
    binarySignedValue (binaryIndexedLookup test term clock width params) =
      if ∃ i < clock.length, hit i = true then z else 0 := by
  induction clock with
  | nil =>
    change binarySignedValue (binarySignedFixed width []) = _
    rw [binarySignedFixed_value_zero width [] rfl]
    simp
  | cons b r ih =>
    rw [binaryIndexedLookup, WordFold.suffixFold_cons]
    change binarySignedValue (select (test r params)
      (binarySignedFixed width (term r params))
      (binaryIndexedLookup test term r width params)) = _
    rw [htest]
    change binarySignedValue (if hit r.length then
      binarySignedFixed width (term r params)
      else binaryIndexedLookup test term r width params) = _
    by_cases hm : hit r.length = true
    · rw [hm]
      change binarySignedValue (binarySignedFixed width (term r params)) = _
      rw [binarySignedFixed_value width _ hw (by rw [hterm r hm]; exact hz), hterm r hm]
      have hhit : ∃ i < (b :: r).length, hit i = true := by
        exact ⟨r.length, by simp, hm⟩
      exact (ite_eq_left hhit).symm
    · have hf : hit r.length = false := Bool.eq_false_iff.mpr hm
      rw [hf]
      change binarySignedValue (binaryIndexedLookup test term r width params) = _
      rw [ih]
      have he : (∃ i < (b :: r).length, hit i = true) ↔
          ∃ i < r.length, hit i = true := by
        constructor
        · rintro ⟨i, hi, hmatch⟩
          refine ⟨i, ?_, hmatch⟩
          have hl : i ≠ r.length := by intro h; subst i; exact hm hmatch
          simp only [List.length_cons] at hi
          omega
        · rintro ⟨i, hi, hmatch⟩
          exact ⟨i, by simp only [List.length_cons]; omega, hmatch⟩
      simp only [he]

/-- Without a matching index, the total bounded lookup retains its initial zero. -/
theorem binaryIndexedLookup_value_zero {Context : Type}
    (test term : List Bool → Context → List Bool)
    (clock width : List Bool) (params : Context)
    (hno : ∀ r : List Bool, r.length < clock.length → test r params = [false]) :
    binarySignedValue (binaryIndexedLookup test term clock width params) = 0 := by
  revert hno
  induction clock with
  | nil =>
    intro hno
    simp only [binaryIndexedLookup, WordFold.suffixFold_nil]
    exact binarySignedFixed_value_zero width [] rfl
  | cons b r ih =>
    intro hno
    rw [binaryIndexedLookup, WordFold.suffixFold_cons]
    change binarySignedValue (select (test r params)
      (binarySignedFixed width (term r params))
      (binaryIndexedLookup test term r width params)) = 0
    rw [hno r (by simp only [List.length_cons]; omega)]
    simp only [select_cons, Bool.false_eq_true, ite_false]
    exact ih (fun s hs => hno s (by simp only [List.length_cons]; omega))
open scoped BigOperators

/-- A scan with at most one matching index equals the guarded finite sum of its values. -/
theorem binaryIndexedLookup_sum_value {Context : Type}
    (test term : List Bool → Context → List Bool)
    (width : List Bool) (params : Context) (hit : ℕ → Bool) (value : ℕ → ℤ)
    (htest : ∀ r, test r params = [hit r.length])
    (hterm : ∀ r, hit r.length = true → binarySignedValue (term r params) =
      value r.length) (hw : 0 < width.length) (clock : List Bool)
    (hbound : ∀ i < clock.length, hit i = true → (value i).natAbs < 2 ^ (width.length - 1))
    (hunique : ∀ i < clock.length, ∀ j < clock.length, hit i = true → hit j = true → i = j) :
    binarySignedValue (binaryIndexedLookup test term clock width params) =
      ∑ i ∈ Finset.range clock.length, if hit i then value i else 0 := by
  induction clock with
  | nil =>
    change binarySignedValue (binarySignedFixed width []) = _
    rw [binarySignedFixed_value_zero width [] rfl]
    rfl
  | cons b r ih =>
    have hl : r.length < (b :: r).length := by simp
    have hb : ∀ i < r.length, hit i = true →
        (value i).natAbs < 2 ^ (width.length - 1) := by
      intro i hi
      exact hbound i (hi.trans hl)
    have hu : ∀ i < r.length, ∀ j < r.length, hit i = true → hit j = true → i = j := by
      intro i hi j hj
      exact hunique i (hi.trans hl) j (hj.trans hl)
    rw [binaryIndexedLookup, WordFold.suffixFold_cons]
    change binarySignedValue (select (test r params)
      (binarySignedFixed width (term r params))
      (binaryIndexedLookup test term r width params)) = _
    rw [htest]
    change binarySignedValue (if hit r.length then
      binarySignedFixed width (term r params)
      else binaryIndexedLookup test term r width params) = _
    by_cases hm : hit r.length = true
    · rw [hm]
      change binarySignedValue (binarySignedFixed width (term r params)) = _
      rw [binarySignedFixed_value width _ hw
        (by rw [hterm r hm]; exact hbound r.length hl hm), hterm r hm]
      have hzero : ∀ i < r.length, hit i = false := by
        intro i hi
        apply Bool.eq_false_iff.mpr
        intro hiHit
        have he := hunique i (hi.trans hl) r.length hl hiHit hm
        omega
      have hsum : (∑ i ∈ Finset.range r.length, if hit i then value i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [hzero i (Finset.mem_range.mp hi), Bool.false_eq_true, ite_false]
      simp only [List.length_cons, Finset.sum_range_succ, hsum, hm, ite_true, zero_add]
    · have hf : hit r.length = false := Bool.eq_false_iff.mpr hm
      rw [hf]
      change binarySignedValue (binaryIndexedLookup test term r width params) = _
      rw [ih hb hu]
      simp only [List.length_cons, Finset.sum_range_succ, hf, Bool.false_eq_true,
        ite_false, add_zero]

end GameTheory.Complexity.Backend
