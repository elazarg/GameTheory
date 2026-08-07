/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite pivot orbits: output or repeated label

Once a projective complementarity construction has been resolved into a
single successor at every non-output **label**, the remaining recurrence
argument is purely finite.

Starting from one label, inspect the first `card Cell + 1` points of the
successor orbit.  Either an output label occurs, or two distinct times carry
the same non-output label.

This theorem deliberately proves no metric or projective return.  A labelled
cell may contain continuously many coefficient points, and repetition of its
label does not imply equality of those points, a fixed point of the chart
monodromy, or a seam which is small relative to a vanishing absorption
charge.  Converting a repeated label into a charged projective lasso therefore
requires a separate relative-return/decoder theorem.
-/

namespace Math

/-- Orbit of a deterministic pivot successor on a finite label type. -/
def finitePivotOrbit {Cell : Type*}
    (next : Cell → Cell) (start : Cell) : ℕ → Cell
  | 0 => start
  | time + 1 => next (finitePivotOrbit next start time)

@[simp] theorem finitePivotOrbit_zero {Cell : Type*}
    (next : Cell → Cell) (start : Cell) :
    finitePivotOrbit next start 0 = start :=
  rfl

@[simp] theorem finitePivotOrbit_succ {Cell : Type*}
    (next : Cell → Cell) (start : Cell) (time : ℕ) :
    finitePivotOrbit next start (time + 1) =
      next (finitePivotOrbit next start time) :=
  rfl

/-- **Finite output-or-repeated-label alternative.**

Among the first `card Cell + 1` points of a deterministic finite-label orbit,
either an output label is reached or two ordered times carry the same
non-output label. -/
theorem exists_output_or_repeated_finitePivotOrbit
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (next : Cell → Cell) (isOutput : Cell → Prop) (start : Cell) :
    (∃ time : Fin (Fintype.card Cell + 1),
      isOutput (finitePivotOrbit next start time)) ∨
    ∃ first second : Fin (Fintype.card Cell + 1),
      first < second ∧
      finitePivotOrbit next start first =
        finitePivotOrbit next start second ∧
      ∀ time : Fin (Fintype.card Cell + 1),
        ¬isOutput (finitePivotOrbit next start time) := by
  classical
  let orbit : Fin (Fintype.card Cell + 1) → Cell :=
    fun time => finitePivotOrbit next start time
  by_cases hout : ∃ time, isOutput (orbit time)
  · left
    simpa only [orbit] using hout
  · right
    have hcard :
        Fintype.card Cell <
          Fintype.card (Fin (Fintype.card Cell + 1)) := by
      simp
    obtain ⟨first, second, hne, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt orbit hcard
    have hno : ∀ time, ¬isOutput (orbit time) := by
      simpa only [not_exists] using hout
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, second, hlt,
        by simpa only [orbit] using heq,
        by simpa only [orbit] using hno⟩
    · exact ⟨second, first, hgt,
        by simpa only [orbit] using heq.symm,
        by simpa only [orbit] using hno⟩

/-- If the finite label system has no output labels, its first
`card Cell + 1` iterates contain a repeated label. -/
theorem exists_repeated_finitePivotOrbit
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (next : Cell → Cell) (start : Cell) :
    ∃ first second : Fin (Fintype.card Cell + 1),
      first < second ∧
      finitePivotOrbit next start first =
        finitePivotOrbit next start second := by
  rcases exists_output_or_repeated_finitePivotOrbit
      next (fun _ => False) start with hout | hrepeated
  · obtain ⟨time, hfalse⟩ := hout
    exact False.elim hfalse
  · obtain ⟨first, second, hlt, heq, _⟩ := hrepeated
    exact ⟨first, second, hlt, heq⟩

end Math
