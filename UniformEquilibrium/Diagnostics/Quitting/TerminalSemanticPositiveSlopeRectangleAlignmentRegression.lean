/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

/-!
# The positive rectangle atom need not lie on the profitable edge

This finite stopping-law table is the exact alignment fence for the
four-profile decoder.  There are two players.  The observer's reward is `-2`
when either player stops alone and `-1` when they stop together.  Its source
law stops at time `0`, and its candidate best response stops at time `2`.

The other player's source stopping law is uniform on times `0,1,2`.  Its
target law has masses `1/6, 0, 1/2, 1/3` on times `0,1,2,3`.  Time `2` is a
maximal atom of every positive mixture of these two laws, so the candidate is
a literal best response in the finite pure-time problem.

The target-side candidate edge gains `1/3`, and the full payoff rectangle is
also `1/3`.  Nevertheless the unique positive rectangle atom is the other
player's solo outcome.  That atom is negative on the profitable target edge
and positive only on the reverse source edge.  The profitable target edge is
instead carried by the observer-solo atom, whose rectangle contribution is
negative.

Thus the positive-slope theorem can align a profitable edge with a positive
payoff atom, but the four-corner algebra cannot force that atom to be the
same coalition as the positive rectangle atom.  A positive semantic minimum
could repair this only through an additional global argument.
-/

namespace GameTheory
namespace PositiveSlopeRectangleAlignmentRegression

open scoped BigOperators

noncomputable section

/-- The three possible non-Never outcomes in the two-player finite stopping
experiment. -/
inductive Outcome
  | moverSolo
  | observerSolo
  | collision
  deriving DecidableEq, Fintype

/-- Uniform source law on dates `0,1,2`, with zero mass at date `3`. -/
def sourceStopMass : Fin 4 → ℝ := fun time =>
  ![1 / 3, 1 / 3, 1 / 3, 0] time

/-- Target masses `(1/6, 0, 1/2, 1/3)`. -/
def targetStopMass : Fin 4 → ℝ := fun time =>
  ![1 / 6, 0, 1 / 2, 1 / 3] time

/-- Complete-law interpolation of the two displayed stopping laws. -/
def mixedStopMass (lambda : ℝ) : Fin 4 → ℝ := fun time =>
  (1 - lambda) * sourceStopMass time + lambda * targetStopMass time

theorem sourceStopMass_sum : ∑ time, sourceStopMass time = 1 := by
  norm_num [sourceStopMass, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

theorem targetStopMass_sum : ∑ time, targetStopMass time = 1 := by
  norm_num [targetStopMass, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Date `2` is a maximal atom of every strictly positive mixture. -/
theorem mixedStopMass_le_timeTwo (lambda : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) (time : Fin 4) :
    mixedStopMass lambda time ≤ mixedStopMass lambda 2 := by
  fin_cases time <;>
    norm_num [mixedStopMass, sourceStopMass, targetStopMass,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    linarith

/-- Terminal law when the observer stops at date `0` (`late = false`) or
date `2` (`late = true`). -/
def terminalMass (law : Fin 4 → ℝ) (late : Bool) : Outcome → ℝ :=
  if late then fun
    | Outcome.moverSolo => law 0 + law 1
    | Outcome.observerSolo => law 3
    | Outcome.collision => law 2
  else fun
    | Outcome.moverSolo => 0
    | Outcome.observerSolo => law 1 + law 2 + law 3
    | Outcome.collision => law 0

/-- Observer rewards: either solo is `-2`, collision is `-1`. -/
def reward : Outcome → ℝ
  | Outcome.moverSolo => -2
  | Outcome.observerSolo => -2
  | Outcome.collision => -1

/-- Expected payoff of one displayed finite stopping law. -/
def payoff (law : Fin 4 → ℝ) (late : Bool) : ℝ :=
  terminalMass law late Outcome.moverSolo * reward Outcome.moverSolo +
    terminalMass law late Outcome.observerSolo * reward Outcome.observerSolo +
    terminalMass law late Outcome.collision * reward Outcome.collision

theorem payoff_source_timeZero : payoff sourceStopMass false = -5 / 3 := by
  norm_num [payoff, terminalMass, reward, sourceStopMass,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem payoff_source_timeTwo : payoff sourceStopMass true = -5 / 3 := by
  norm_num [payoff, terminalMass, reward, sourceStopMass,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem payoff_target_timeZero : payoff targetStopMass false = -11 / 6 := by
  norm_num [payoff, terminalMass, reward, targetStopMass,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem payoff_target_timeTwo : payoff targetStopMass true = -3 / 2 := by
  norm_num [payoff, terminalMass, reward, targetStopMass,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

/-- The target-side forward edge is profitable by exactly `1/3`. -/
theorem targetEdge_gain :
    payoff targetStopMass true - payoff targetStopMass false = 1 / 3 := by
  rw [payoff_target_timeTwo, payoff_target_timeZero]
  norm_num

/-- The source-side edge is payoff-flat. -/
theorem sourceEdge_gain :
    payoff sourceStopMass true - payoff sourceStopMass false = 0 := by
  rw [payoff_source_timeTwo, payoff_source_timeZero]
  ring

/-- Reward-weighted contribution of one outcome to the full square. -/
def rectangleAtom (outcome : Outcome) : ℝ :=
  (terminalMass targetStopMass true outcome -
      terminalMass sourceStopMass true outcome -
      terminalMass targetStopMass false outcome +
      terminalMass sourceStopMass false outcome) * reward outcome

/-- The full payoff rectangle is strictly positive. -/
theorem payoff_rectangle :
    payoff targetStopMass true - payoff sourceStopMass true -
        payoff targetStopMass false + payoff sourceStopMass false = 1 / 3 := by
  rw [payoff_target_timeTwo, payoff_source_timeTwo,
    payoff_target_timeZero, payoff_source_timeZero]
  norm_num

theorem rectangleAtom_moverSolo :
    rectangleAtom Outcome.moverSolo = 1 := by
  norm_num [rectangleAtom, terminalMass, reward, sourceStopMass,
    targetStopMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem rectangleAtom_observerSolo :
    rectangleAtom Outcome.observerSolo = -1 / 3 := by
  norm_num [rectangleAtom, terminalMass, reward, sourceStopMass,
    targetStopMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem rectangleAtom_collision :
    rectangleAtom Outcome.collision = -1 / 3 := by
  norm_num [rectangleAtom, terminalMass, reward, sourceStopMass,
    targetStopMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The mover-solo outcome is the unique positive rectangle atom. -/
theorem rectangleAtom_pos_iff (outcome : Outcome) :
    0 < rectangleAtom outcome ↔ outcome = Outcome.moverSolo := by
  cases outcome <;>
    simp [rectangleAtom_moverSolo, rectangleAtom_observerSolo,
      rectangleAtom_collision]

/-- But that rectangle-positive atom contributes negatively on the
profitable target-side edge. -/
theorem moverSolo_targetEdge_atom_negative :
    (terminalMass targetStopMass true Outcome.moverSolo -
        terminalMass targetStopMass false Outcome.moverSolo) *
      reward Outcome.moverSolo = -1 / 3 := by
  norm_num [terminalMass, reward, targetStopMass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The same atom is positive only on the reverse source edge. -/
theorem moverSolo_reverseSourceEdge_atom_positive :
    (terminalMass sourceStopMass false Outcome.moverSolo -
        terminalMass sourceStopMass true Outcome.moverSolo) *
      reward Outcome.moverSolo = 4 / 3 := by
  norm_num [terminalMass, reward, sourceStopMass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The profitable target edge is instead carried by the observer-solo atom,
whose rectangle contribution is negative. -/
theorem observerSolo_targetEdge_atom_positive :
    (terminalMass targetStopMass true Outcome.observerSolo -
        terminalMass targetStopMass false Outcome.observerSolo) *
      reward Outcome.observerSolo = 1 := by
  norm_num [terminalMass, reward, targetStopMass, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

end
end PositiveSlopeRectangleAlignmentRegression
end GameTheory
