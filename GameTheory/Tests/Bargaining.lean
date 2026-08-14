/-
# Hostile finite bargaining fixture

The feasible set contains three nontrivial individually-rational allocations
and the disagreement point.  The balanced allocation beats both asymmetric
allocations in Nash product, while unequal positive scales and nonzero shifts
exercise genuine componentwise affine invariance.
-/

import GameTheory.Cooperative.Bargaining
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace GameTheory.Tests.Bargaining

open GameTheory
open BargainingProblem
open scoped BigOperators

abbrev Player := Fin 2

def disagreement : Player → ℝ := fun _ => 0

def balanced : Player → ℝ := fun _ => 2

def leftHeavy : Player → ℝ := fun player =>
  if player = 0 then 3 else 1

def rightHeavy : Player → ℝ := fun player =>
  if player = 0 then 1 else 3

def fixture : BargainingProblem Player where
  feasible utility :=
    utility = disagreement ∨ utility = balanced ∨
      utility = leftHeavy ∨ utility = rightHeavy
  disagreement := disagreement
  disagreement_feasible := Or.inl rfl

theorem balanced_feasible : fixture.feasible balanced :=
  Or.inr (Or.inl rfl)

theorem balanced_ir : fixture.IsIndividuallyRational balanced := by
  intro player
  fin_cases player <;> norm_num [fixture, disagreement, balanced]

/-- The balanced point has product four; each asymmetric point has product
three.  Thus this is not a singleton-feasibility or constant-product test. -/
theorem balanced_solution : fixture.IsNashSolution balanced := by
  refine ⟨balanced_feasible, balanced_ir, ?_⟩
  intro alternative hfeasible _
  rcases hfeasible with rfl | rfl | rfl | rfl <;>
    norm_num [fixture, disagreement, balanced, leftHeavy, rightHeavy,
      Fin.prod_univ_two]

theorem leftHeavy_feasible : fixture.feasible leftHeavy :=
  Or.inr (Or.inr (Or.inl rfl))

theorem leftHeavy_ir : fixture.IsIndividuallyRational leftHeavy := by
  intro player
  fin_cases player <;> norm_num [fixture, disagreement, leftHeavy]

/-- Feasibility and individual rationality alone do not imply the solution
predicate: the balanced point has strictly larger Nash product. -/
theorem leftHeavy_not_solution : ¬ fixture.IsNashSolution leftHeavy := by
  intro solution
  have hmax := solution.2.2 balanced balanced_feasible balanced_ir
  norm_num [fixture, disagreement, balanced, leftHeavy,
    Fin.prod_univ_two] at hmax

def scale : Player → ℝ := fun player =>
  if player = 0 then 2 else 3

def shift : Player → ℝ := fun player =>
  if player = 0 then 5 else -1

theorem scale_positive : ∀ player, 0 < scale player := by
  intro player
  fin_cases player <;> norm_num [scale]

def transformedBalanced : Player → ℝ := fun player =>
  scale player * balanced player + shift player

theorem transformedBalanced_values :
    transformedBalanced 0 = 9 ∧ transformedBalanced 1 = 5 := by
  norm_num [transformedBalanced, scale, balanced, shift]

theorem transformed_disagreement_values :
    (fixture.positiveAffineMap scale scale_positive shift).disagreement 0 = 5 ∧
      (fixture.positiveAffineMap scale scale_positive shift).disagreement 1 = -1 := by
  norm_num [BargainingProblem.positiveAffineMap, fixture, disagreement,
    scale, shift]

/-- The generic invariance theorem specializes to unequal scales and nonzero
shifts, producing a numerically different maximizer. -/
theorem transformedBalanced_solution :
    (fixture.positiveAffineMap scale scale_positive shift).IsNashSolution
      transformedBalanced :=
  balanced_solution.positiveAffineMap fixture scale scale_positive shift

theorem balanced_weaklyPareto : fixture.IsWeaklyPareto balanced :=
  balanced_solution.isWeaklyPareto fixture

end GameTheory.Tests.Bargaining
