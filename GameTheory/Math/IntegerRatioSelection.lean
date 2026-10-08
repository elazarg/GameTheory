import GameTheory.Math.FiniteLexicographicCompare
import GameTheory.Math.LexicographicPivot
import Mathlib.Data.List.FinRange

/-! Executable symbolic ratio selection using integer cross-products.

Only rows with positive direction are eligible. Comparing their cross-products
avoids rational division; the selected row minimizes the canonical rational
lexicographic ratio, retaining the earliest row when ratios are equal.
-/

namespace GameTheory.Math.IntegerRatioSelection

variable {n k : ℕ}

/-- Compare two rows without constructing rational ratios. -/
def compare (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) (i j : Fin n) : Bool :=
  FiniteLexicographicCompare.lexLT (fun a => C i a * d j) (fun a => C j a * d i)

theorem compare_eq_true (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) (i j : Fin n)
    (hi : 0 < d i) (hj : 0 < d j) :
    compare C d i j = true ↔
      toLex (fun a => (C i a : ℚ) / (d i : ℚ)) <
        toLex (fun a => (C j a : ℚ) / (d j : ℚ)) := by
  have hiQ : (0 : ℚ) < (d i : ℚ) := by exact_mod_cast hi
  have hjQ : (0 : ℚ) < (d j : ℚ) := by exact_mod_cast hj
  rw [compare, FiniteLexicographicCompare.lexLT_eq_true]
  constructor
  · rintro ⟨a, hpre, hlt⟩
    refine ⟨a, ?_, ?_⟩
    · intro b hb
      apply (div_eq_div_iff hiQ.ne' hjQ.ne').mpr
      exact_mod_cast hpre b hb
    · apply (div_lt_div_iff₀ hiQ hjQ).mpr
      exact_mod_cast hlt
  · rintro ⟨a, hpre, hlt⟩
    refine ⟨a, ?_, ?_⟩
    · intro b hb
      have he := (div_eq_div_iff hiQ.ne' hjQ.ne').mp (hpre b hb)
      exact_mod_cast he
    · have he := (div_lt_div_iff₀ hiQ hjQ).mp hlt
      exact_mod_cast he

private def selectFrom (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) :
    List (Fin n) → Option (Fin n)
  | [] => none
  | i :: rows => match selectFrom C d rows with
      | none => some i
      | some j => if compare C d j i then some j else some i

/-- Select the earliest minimum among the rows with strictly positive direction. -/
def select (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) : Option (Fin n) :=
  selectFrom C d ((List.finRange n).filter (fun i => decide (0 < d i)))

private theorem selectFrom_eq_none (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ)
    (rows : List (Fin n)) : selectFrom C d rows = none ↔ rows = [] := by
  cases rows with
  | nil => simp [selectFrom]
  | cons i rows =>
    cases h : selectFrom C d rows with
    | none => simp [selectFrom, h]
    | some j => simp [selectFrom, h]; split <;> simp

theorem select_none (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) :
    select C d = none ↔ ∀ i, d i ≤ 0 := by
  rw [select, selectFrom_eq_none]
  simp

private theorem selectFrom_spec (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ)
    (rows : List (Fin n)) (hs : ∀ i ∈ rows, 0 < d i) (l : Fin n)
    (hsel : selectFrom C d rows = some l) :
    l ∈ rows ∧ ∀ i ∈ rows,
      toLex (fun a => (C l a : ℚ) / (d l : ℚ)) ≤
        toLex (fun a => (C i a : ℚ) / (d i : ℚ)) := by
  induction rows generalizing l with
  | nil => simp [selectFrom] at hsel
  | cons a rows ih =>
    have ha : 0 < d a := hs a (by simp)
    have hrows : ∀ i ∈ rows, 0 < d i := fun i hi => hs i (List.mem_cons_of_mem _ hi)
    cases htail : selectFrom C d rows with
    | none =>
      have hempty := (selectFrom_eq_none C d rows).mp htail
      subst rows
      have hal : a = l := by simpa [selectFrom] using hsel
      subst l
      refine ⟨by simp, ?_⟩
      intro i hi
      have hai : i = a := by simpa using hi
      subst i
      exact le_rfl
    | some b =>
      have hb := ih hrows b htail
      have hpos : 0 < d b := hrows b hb.1
      by_cases hcomp : compare C d b a = true
      · have hbl : b = l := by simpa [selectFrom, htail, hcomp] using hsel
        subst l
        refine ⟨List.mem_cons_of_mem _ hb.1, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ((compare_eq_true C d b i hpos ha).mp hcomp).le
        · exact hb.2 i hi
      · have hal : a = l := by simpa [selectFrom, htail, hcomp] using hsel
        subst l
        have hab : toLex (fun z => (C a z : ℚ) / (d a : ℚ)) ≤
            toLex (fun z => (C b z : ℚ) / (d b : ℚ)) := by
          apply le_of_not_gt
          intro hlt
          exact hcomp ((compare_eq_true C d b a hpos ha).mpr hlt)
        refine ⟨by simp, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact le_rfl
        · exact hab.trans (hb.2 i hi)

/-- The executable minimum satisfies the existing rational leaving-row predicate. -/
theorem select_some_spec (C : Fin n → Fin k → ℤ) (d : Fin n → ℤ) (l : Fin n)
    (hsel : select C d = some l) :
    IsLeavingRow (fun i a => (C i a : ℚ)) (fun i => (d i : ℚ)) l := by
  have hs : ∀ i ∈ (List.finRange n).filter (fun i => decide (0 < d i)), 0 < d i := by
    intro i hi
    simpa using (List.mem_filter.mp hi).2
  have hl := selectFrom_spec C d _ hs l hsel
  have hpos := hs l hl.1
  refine ⟨?_, ?_⟩
  · change (0 : ℚ) < (d l : ℚ)
    exact_mod_cast hpos
  intro i hi
  change (0 : ℚ) < (d i : ℚ) at hi
  have hiZ : 0 < d i := by exact_mod_cast hi
  exact hl.2 i (by simp [hiZ])

end GameTheory.Math.IntegerRatioSelection
