import GameTheoryComplexity.Backend.BinarySignedMatrixMachine

/-! Indexed guarded lookup with fixed-width signed storage. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private def lookupStep {p : ℕ}
    (test term : (Fin (p + 1) → List Bool) → List Bool)
    (v : Fin (p + 3) → List Bool) : List Bool :=
  caseBit₀ (test (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))))
    (binarySignedFixed (v 2) (term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))))) (v 1)

/-- Retain the last matching indexed value, with zero as the default value. -/
def binaryIndexedLookup {p : ℕ}
    (test term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) : List Bool :=
  recNotation (fun v : Fin (p + 1) → List Bool => binarySignedFixed (v 0) [])
    (lookupStep test term) (lookupStep test term) clock (Fin.cons width params)

@[simp] theorem binaryIndexedLookup_length {p : ℕ}
    (test term : (Fin (p + 1) → List Bool) → List Bool)
    (clock width : List Bool) (params : Fin p → List Bool) :
    (binaryIndexedLookup test term clock width params).length = width.length := by
  induction clock with
  | nil => exact binarySignedFixed_length _ _
  | cons b r ih =>
    simp only [binaryIndexedLookup, recNotation_cons, Bool.cond_self]
    change (caseBit₀ (test (Fin.cons r params))
      (binarySignedFixed width (term (Fin.cons r params)))
      (binaryIndexedLookup test term r width params)).length = _
    cases h : test (Fin.cons r params) with
    | nil => simpa only [caseBit₀] using ih
        | cons b tail =>
      cases b
      · exact ih
      · exact binarySignedFixed_length _ _
/-- The bounded scan is an actual polynomial-time string machine. -/
theorem binaryIndexedLookup_cobham {p : ℕ}
    {test term : (Fin (p + 1) → List Bool) → List Bool}
    (htest : Cobham test) (hterm : Cobham term) :
    Cobham fun v : Fin (p + 2) → List Bool =>
      binaryIndexedLookup test term (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  have ht : Cobham fun v : Fin (p + 3) → List Bool =>
      test (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))) := by
    apply Cobham.comp htest
    intro i
    exact Fin.cases (.proj 0) (fun j => .proj j.succ.succ.succ) i
  have hv : Cobham fun v : Fin (p + 3) → List Bool =>
      term (Fin.cons (v 0) (Fin.tail (Fin.tail (Fin.tail v)))) := by
    apply Cobham.comp hterm
    intro i
    exact Fin.cases (.proj 0) (fun j => .proj j.succ.succ.succ) i
  have hs : Cobham (lookupStep test term) :=
    Cobham.iteFn ht (Cobham.comp₂ binarySignedFixed_cobham (.proj 2) hv) (.proj 1)
  exact (Cobham.boundedRec
    (Cobham.comp₂ binarySignedFixed_cobham (.proj 0) (Cobham.const [])) hs hs (.proj 1)
    (fun r v => by
      have he : v = Fin.cons (v 0) (Fin.tail v) := by
        ext i
        cases i using Fin.cases <;> rfl
      rw [he]
      change (binaryIndexedLookup test term r (v 0) (Fin.tail v)).length ≤ _
      rw [binaryIndexedLookup_length]
      exact le_rfl)).of_eq fun v => by
        congr 1
        ext i
        cases i using Fin.cases <;> rfl

theorem binaryIndexedLookup_mem_FPn {p : ℕ}
    {test term : (Fin (p + 1) → List Bool) → List Bool}
    (htest : Cobham test) (hterm : Cobham term) :
    FPn (fun v : Fin (p + 2) → List Bool =>
      binaryIndexedLookup test term (v 0) (v 1) (Fin.tail (Fin.tail v))) :=
  cobham_iff_FPn.mp (binaryIndexedLookup_cobham htest hterm)

/-- Equal values at every matching index give an exact total lookup interpretation. -/
theorem binaryIndexedLookup_value {p : ℕ}
    (test term : (Fin (p + 1) → List Bool) → List Bool)
    (width : List Bool) (params : Fin p → List Bool) (hit : ℕ → Bool) (z : ℤ)
    (htest : ∀ r, test (Fin.cons r params) = [hit r.length])
    (hterm : ∀ r, hit r.length = true → binarySignedValue (term (Fin.cons r params)) = z)
    (hw : 0 < width.length) (hz : z.natAbs < 2 ^ (width.length - 1)) (clock : List Bool) :
    binarySignedValue (binaryIndexedLookup test term clock width params) =
      if ∃ i < clock.length, hit i = true then z else 0 := by
  induction clock with
  | nil =>
    change binarySignedValue (binarySignedFixed width []) = _
    rw [binarySignedFixed_value width [] hw (by simp [binarySignedValue]; positivity)]
    simpa using (show binarySignedValue [] = (0 : ℤ) from rfl)
  | cons b r ih =>
    simp only [binaryIndexedLookup, recNotation_cons, Bool.cond_self]
    change binarySignedValue (caseBit₀ (test (Fin.cons r params))
      (binarySignedFixed width (term (Fin.cons r params)))
      (binaryIndexedLookup test term r width params)) = _
    rw [htest]
    by_cases hm : hit r.length = true
    · rw [hm]
      change binarySignedValue (binarySignedFixed width (term (Fin.cons r params))) = _
      rw [binarySignedFixed_value width _ hw (by rw [hterm r hm]; exact hz), hterm r hm]
      exact (ite_eq_left ⟨r.length, by simp, hm⟩).symm
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

end GameTheory.Complexity.Backend
