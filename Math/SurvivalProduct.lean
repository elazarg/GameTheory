/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The canonical telescoping survival product

A census of `GameTheory.Concepts.Stochastic` found the finite product of a
per-stage "continue mass" over a window reinvented under (at least) four
names: `quittingFiniteContinueWeight` (a recursion, closed by a separate
theorem), `blockSurvival` (a direct product, entangled with one file's own
seam-price development), `quittingJointSurvivalWeight` and
`quittingSurvivalPrefix` (thin game-specific wrappers), plus a "deleted"
(opponent-restricted) sibling `quittingOpponentSurvivalWeight` and a
best-response variant `quittingFiniteFullSurvivalWeight`.  The identity
between two of these was proved twice, independently, in the same wave.

This file supplies the one canonical, dependency-free name, `survivalProduct`,
with a minimal telescoping API.  It does **not** replace or delete any of the
existing names -- each keeps its own file, its own bounds lemmas, and its own
call sites -- it only gives every one of them a common target to be proved
equal to, by a single bridging lemma living next to each original
definition.
-/

namespace Math

/-- The product of `C` over the half-open window `[start, start + fuel)`,
written as a shift by `start` over `Finset.range fuel`.  The canonical name
for what `GameTheory.quittingFiniteContinueWeight`, `GameTheory.blockSurvival`,
`GameTheory.quittingJointSurvivalWeight`, `GameTheory.quittingSurvivalPrefix`
(at `start = 0`), `GameTheory.quittingOpponentSurvivalWeight` (at the deleted
continue mass), and `GameTheory.quittingFiniteFullSurvivalWeight` (at its own
hazard) each independently reinvent -- see the bridging lemma next to each of
those definitions. -/
def survivalProduct (C : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel, C (start + offset)

@[simp] theorem survivalProduct_zero (C : ℕ → ℝ) (start : ℕ) :
    survivalProduct C start 0 = 1 := by
  simp [survivalProduct]

/-- Appending one more stage at the far end multiplies survival by that
stage's coefficient. -/
theorem survivalProduct_succ (C : ℕ → ℝ) (start fuel : ℕ) :
    survivalProduct C start (fuel + 1) =
      survivalProduct C start fuel * C (start + fuel) := by
  simp [survivalProduct, Finset.prod_range_succ]

/-- Survival over a concatenated window splits multiplicatively into the
survival of its two pieces: the telescoping law. -/
theorem survivalProduct_add (C : ℕ → ℝ) (start a b : ℕ) :
    survivalProduct C start (a + b) =
      survivalProduct C start a * survivalProduct C (start + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, survivalProduct_succ, ih,
        survivalProduct_succ, show start + a + b = start + (a + b) by omega]
      ring

theorem survivalProduct_nonneg (C : ℕ → ℝ) (hC : ∀ time, 0 ≤ C time)
    (start fuel : ℕ) : 0 ≤ survivalProduct C start fuel :=
  Finset.prod_nonneg fun offset _ => hC (start + offset)

theorem survivalProduct_le_one (C : ℕ → ℝ) (hC0 : ∀ time, 0 ≤ C time)
    (hC1 : ∀ time, C time ≤ 1) (start fuel : ℕ) :
    survivalProduct C start fuel ≤ 1 :=
  Finset.prod_le_one (fun offset _ => hC0 (start + offset))
    (fun offset _ => hC1 (start + offset))

end Math
