import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Explicit row-major emission of bounded integer-payoff encodings.
A polynomial-time certificate for each cell is lifted to the entire table by
bounded recursion, so the certificate concerns a deterministic machine and not
merely the size of its output.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Append one encoded cell; the recursion counter indexes columns in increasing order. -/
def payoffRowStep (cell : (Fin 3 → List Bool) → List Bool)
    (v : Fin 4 → List Bool) : List Bool :=
  v 1 ++ cell ![v 2, v 0, v 3]

/-- Emit a row by recursion on a unary column ruler, retaining its row and source. -/
def payoffRowLoop (cell : (Fin 3 → List Bool) → List Bool)
    (columns : List Bool) (params : Fin 2 → List Bool) : List Bool :=
  recNotation (fun _ => []) (payoffRowStep cell) (payoffRowStep cell) columns params

/-- Serialize one row with the supplied cell serializer. -/
def payoffRow (cell : (Fin 3 → List Bool) → List Bool)
    (v : Fin 3 → List Bool) : List Bool :=
  payoffRowLoop cell (v 0) ![v 1, v 2]

private theorem payoffRowLoop_length_le
    (cell : (Fin 3 → List Bool) → List Bool) (width : List Bool → List Bool)
    (hcell : ∀ v, (cell v).length ≤ (width (v 2)).length)
    (columns : List Bool) (params : Fin 2 → List Bool) :
    (payoffRowLoop cell columns params).length ≤
      columns.length * (width (params 1)).length := by
  induction columns with
  | nil => simp [payoffRowLoop]
  | cons b columns ih =>
      simp only [payoffRowLoop, recNotation_cons, payoffRowStep,
        Bool.cond_self, Fin.cons_zero, List.length_append,
        List.length_cons]
      have hc := hcell ![params 0, columns, params 1]
      change (cell ![params 0, columns, params 1]).length ≤
        (width (params 1)).length at hc
      change (payoffRowLoop cell columns params).length +
        (cell ![params 0, columns, params 1]).length ≤ _
      nlinarith

/-- The explicit row emitter is polynomial-time whenever its cell function is,
with a uniform polynomial-time output-width ruler. -/
theorem payoffRow_cobham
    {cell : (Fin 3 → List Bool) → List Bool} {width : List Bool → List Bool}
    (hc : Cobham cell) (hw : Cobham fun v : Fin 1 → List Bool => width (v 0))
    (hcell : ∀ v, (cell v).length ≤ (width (v 2)).length) : Cobham (payoffRow cell) := by
  have hs : Cobham (payoffRowStep cell) := by
    apply Cobham.appendFn (Cobham.proj 1)
    apply Cobham.comp hc
    intro i
    fin_cases i
    · exact Cobham.proj 2
    · exact Cobham.proj 0
    · exact Cobham.proj 3
  have hwidth : Cobham fun v : Fin 3 → List Bool => width (v 2) :=
    (Cobham.comp hw fun _ => Cobham.proj 2).of_eq fun _ => rfl
  have hb : Cobham fun v : Fin 3 → List Bool => smash (v 0) (width (v 2)) :=
    Cobham.comp₂ Cobham.smash (Cobham.proj 0) hwidth
  have hr := Cobham.boundedRec Cobham.empty hs hs hb
    (fun columns params => by
      simp only [smash_length]
      change (payoffRowLoop cell columns params).length ≤
        columns.length * (width (params 1)).length
      exact payoffRowLoop_length_le cell width hcell columns params)
  apply hr.of_eq
  intro v
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Append a full row to the table accumulated so far. -/
def payoffTableStep (cell : (Fin 3 → List Bool) → List Bool)
    (v : Fin 4 → List Bool) : List Bool :=
  v 1 ++ payoffRowLoop cell (v 2) ![v 0, v 3]

/-- Emit rows while retaining the full column ruler and source string. -/
def payoffTableLoop (cell : (Fin 3 → List Bool) → List Bool)
    (rows : List Bool) (params : Fin 2 → List Bool) : List Bool :=
  recNotation (fun _ => []) (payoffTableStep cell) (payoffTableStep cell) rows params

/-- Explicit row-major serialization of a square table. -/
def payoffTable (cell : (Fin 3 → List Bool) → List Bool)
    (v : Fin 2 → List Bool) : List Bool :=
  payoffTableLoop cell (v 0) ![v 0, v 1]

private theorem payoffTableLoop_length_le
    (cell : (Fin 3 → List Bool) → List Bool) (width : List Bool → List Bool)
    (hcell : ∀ v, (cell v).length ≤ (width (v 2)).length)
    (rows : List Bool) (params : Fin 2 → List Bool) :
    (payoffTableLoop cell rows params).length ≤
      rows.length * (params 0).length * (width (params 1)).length := by
  induction rows with
  | nil => simp [payoffTableLoop]
  | cons b rows ih =>
      simp only [payoffTableLoop, recNotation_cons, payoffTableStep,
        Bool.cond_self, Fin.cons_zero, List.length_append, List.length_cons]
      have hr := payoffRowLoop_length_le cell width hcell (params 0) ![rows, params 1]
      change (payoffRowLoop cell (params 0) ![rows, params 1]).length ≤
        (params 0).length * (width (params 1)).length at hr
      change (payoffTableLoop cell rows params).length +
        (payoffRowLoop cell (params 0) ![rows, params 1]).length ≤ _
      nlinarith

/-- A certified cell evaluator yields a certified explicit square-table emitter. -/
theorem payoffTable_cobham
    {cell : (Fin 3 → List Bool) → List Bool} {width : List Bool → List Bool}
    (hc : Cobham cell) (hw : Cobham fun v : Fin 1 → List Bool => width (v 0))
    (hcell : ∀ v, (cell v).length ≤ (width (v 2)).length) : Cobham (payoffTable cell) := by
  have hs : Cobham (payoffTableStep cell) := by
    apply Cobham.appendFn (Cobham.proj 1)
    have h := Cobham.comp (payoffRow_cobham hc hw hcell)
      (gs := fun i => fun v : Fin 4 → List Bool =>
        (![v 2, v 0, v 3] : Fin 3 → List Bool) i) (by
          intro i
          fin_cases i
          · exact Cobham.proj 2
          · exact Cobham.proj 0
          · exact Cobham.proj 3)
    exact h.of_eq fun _ => rfl
  have hwidth : Cobham fun v : Fin 3 → List Bool => width (v 2) :=
    (Cobham.comp hw fun _ => Cobham.proj 2).of_eq fun _ => rfl
  have hb : Cobham fun v : Fin 3 → List Bool =>
      smash (v 0) (smash (v 1) (width (v 2))) :=
    Cobham.comp₂ Cobham.smash (Cobham.proj 0)
      (Cobham.comp₂ Cobham.smash (Cobham.proj 1) hwidth)
  have hr := Cobham.boundedRec Cobham.empty hs hs hb
    (fun rows params => by
      simp only [smash_length]
      change (payoffTableLoop cell rows params).length ≤
        rows.length * ((params 0).length * (width (params 1)).length)
      simpa only [Nat.mul_assoc] using
        payoffTableLoop_length_le cell width hcell rows params)
  have hcompose := Cobham.comp hr (gs := fun i => fun v : Fin 2 → List Bool =>
    (![v 0, v 0, v 1] : Fin 3 → List Bool) i) (by
      intro i
      fin_cases i
      · exact Cobham.proj 0
      · exact Cobham.proj 0
      · exact Cobham.proj 1)
  exact hcompose.of_eq fun _ => rfl

/-- Polynomial-time generation of every explicit payoff cell from one source string. -/
theorem payoffTable_mem_FP
    {cell : (Fin 3 → List Bool) → List Bool} {width ruler : List Bool → List Bool}
    (hc : Cobham cell) (hw : Cobham fun v : Fin 1 → List Bool => width (v 0))
    (hr : Cobham fun v : Fin 1 → List Bool => ruler (v 0))
    (hcell : ∀ v, (cell v).length ≤ (width (v 2)).length) :
    (fun input => payoffTable cell ![ruler input, input]) ∈ FP := by
  apply CobhamFP_subset_FP
  apply Cobham.comp (payoffTable_cobham hc hw hcell)
  intro i
  fin_cases i
  · exact hr
  · exact Cobham.proj 0

/-- On unary counters the row emitter is exactly concatenation over all column indices. -/
theorem payoffRowLoop_replicate (cell : (Fin 3 → List Bool) → List Bool)
    (n : ℕ) (params : Fin 2 → List Bool) :
    payoffRowLoop cell (List.replicate n true) params =
      (List.range n).flatMap fun j => cell ![params 0, List.replicate j true, params 1] := by
  induction n with
  | zero => simp [payoffRowLoop]
  | succ n ih =>
      simp only [List.replicate_succ, payoffRowLoop, recNotation_cons,
        payoffRowStep, Bool.cond_true, Fin.cons_zero]
      change payoffRowLoop cell (List.replicate n true) params ++
        cell ![params 0, List.replicate n true, params 1] = _
      rw [ih, List.range_succ, List.flatMap_append]
      simp

/-- On unary counters every table entry is emitted in row-major order. -/
theorem payoffTableLoop_replicate (cell : (Fin 3 → List Bool) → List Bool)
    (n : ℕ) (params : Fin 2 → List Bool) :
    payoffTableLoop cell (List.replicate n true) params =
      (List.range n).flatMap fun i => payoffRowLoop cell (params 0)
        ![List.replicate i true, params 1] := by
  induction n with
  | zero => simp [payoffTableLoop]
  | succ n ih =>
      simp only [List.replicate_succ, payoffTableLoop, recNotation_cons,
        payoffTableStep, Bool.cond_true, Fin.cons_zero]
      change payoffTableLoop cell (List.replicate n true) params ++
        payoffRowLoop cell (params 0) ![List.replicate n true, params 1] = _
      rw [ih, List.range_succ, List.flatMap_append]
      simp

/-- Semantic agreement with an explicit square matrix serializer; no source decoder
is needed to read its entries. -/
theorem payoffTable_replicate (cell : (Fin 3 → List Bool) → List Bool)
    (n : ℕ) (input : List Bool) :
    payoffTable cell ![List.replicate n true, input] =
      (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
        cell ![List.replicate i true, List.replicate j true, input] := by
  unfold payoffTable
  change payoffTableLoop cell (List.replicate n true) ![List.replicate n true, input] = _
  rw [payoffTableLoop_replicate]
  apply List.flatMap_congr
  intro i hi
  exact payoffRowLoop_replicate cell n _

end GameTheory.Complexity.Backend
