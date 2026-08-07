/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite pivot orbits: output or lasso

Once a projective complementarity construction has been resolved into a
single physical successor at every non-output cell, the remaining recurrence
argument is purely finite.

Starting from one cell, inspect the first `card Cell + 1` points of the
successor orbit.  Either an output cell occurs, or two distinct times carry
the same cell.  Ordering those times gives a nonempty lasso.  On the latter
branch, every inspected cell is certified non-output.

This theorem is deliberately independent of the intended quitting-game
semantics.  The game-theoretic work is the local **physical pivot
completeness** theorem and the decoder from a repeated labelled projective
cell to a charged projective lasso.  This file discharges the global finite
pigeonhole step once those local data are available.
-/

namespace Math

/-- Orbit of a deterministic pivot successor. -/
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

/-- **Finite pivot output-or-lasso alternative.**

Among the first `card Cell + 1` points of a deterministic finite-state pivot
orbit, either an output is reached or two ordered times carry the same
non-output cell. -/
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

/-- If the pivot system has no output cells at all, its first
`card Cell + 1` iterates contain a nonempty lasso. -/
theorem exists_repeated_finitePivotOrbit
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (next : Cell → Cell) (start : Cell) :
    ∃ first second : Fin (Fintype.card Cell + 1),
      first < second ∧
      finitePivotOrbit next start first =
        finitePivotOrbit next start second := by
  rcases exists_output_or_repeated_finitePivotOrbit
      next (fun _ => False) start with hout | hlasso
  · obtain ⟨time, hfalse⟩ := hout
    exact False.elim hfalse
  · obtain ⟨first, second, hlt, heq, _⟩ := hlasso
    exact ⟨first, second, hlt, heq⟩

end Math
