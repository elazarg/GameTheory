module

/-
# Positive and boundary Nash-product optima

Positive incumbent gains ensure full Pareto efficiency. Weak participation
alone does not guarantee it: a zero-product tie may permit a Pareto improvement.
-/

public import GameTheory.Cooperative.Bargaining
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Tests.BargainingScalarization

open scoped BigOperators

def zero : Bool → ℝ := fun _ => 0

def positiveLow : Bool → ℝ := fun _ => 1

def positiveHigh (player : Bool) : ℝ := if player then 2 else 1

/-- One player's zero gain makes every listed Nash product vanish. -/
def zeroGainLow (player : Bool) : ℝ := if player then 1 else 0

def zeroGainHigh (player : Bool) : ℝ := if player then 2 else 0

/-- Positive and zero-gain allocations share one feasible domain. -/
def positiveProblem : BargainingProblem Bool where
  feasible allocation := allocation = zero ∨ allocation = positiveLow ∨
    allocation = positiveHigh ∨ allocation = zeroGainLow ∨ allocation = zeroGainHigh
  disagreement := zero
  disagreement_feasible := Or.inl rfl

theorem positiveHigh_isNashSolution : positiveProblem.IsNashSolution positiveHigh := by
  refine ⟨by simp [positiveProblem], ?_, ?_⟩
  · intro player
    cases player <;> norm_num [positiveProblem, zero, positiveHigh]
  · intro alternative feasible _
    rcases feasible with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [positiveProblem, zero, positiveLow, positiveHigh,
        zeroGainLow, zeroGainHigh, Fintype.prod_bool]

/-- The positive-gain scalar optimum reaches the canonical Pareto predicate. -/
theorem positiveHigh_isPareto : positiveProblem.IsPareto positiveHigh :=
  positiveHigh_isNashSolution.isPareto_of_positive_gains (by
    intro player
    cases player <;> norm_num [positiveProblem, zero, positiveHigh])

/-- The same feasible domain contains strict improvements with equal product.
Global strict monotonicity would therefore reject this valid positive optimum. -/
theorem positiveProblem_product_not_strictMonoOn :
    ¬ StrictMonoOn
      (fun allocation : Bool → ℝ =>
        ∏ player, (allocation player - positiveProblem.disagreement player))
      {allocation | positiveProblem.feasible allocation ∧
        positiveProblem.IsIndividuallyRational allocation} := by
  intro monotone
  have low : positiveProblem.feasible zeroGainLow ∧
      positiveProblem.IsIndividuallyRational zeroGainLow := by
    refine ⟨by simp [positiveProblem], ?_⟩
    intro player
    cases player <;> norm_num [positiveProblem, zero, zeroGainLow]
  have high : positiveProblem.feasible zeroGainHigh ∧
      positiveProblem.IsIndividuallyRational zeroGainHigh := by
    refine ⟨by simp [positiveProblem], ?_⟩
    intro player
    cases player <;> norm_num [positiveProblem, zero, zeroGainHigh]
  have improved : zeroGainLow < zeroGainHigh := by
    apply Pi.lt_def.mpr
    refine ⟨fun player => ?_, true, by norm_num [zeroGainLow, zeroGainHigh]⟩
    cases player <;> norm_num [zeroGainLow, zeroGainHigh]
  have impossible := monotone low high improved
  norm_num [positiveProblem, zero, zeroGainLow, zeroGainHigh, Fintype.prod_bool] at impossible

def zeroGainProblem : BargainingProblem Bool where
  feasible allocation := allocation = zero ∨ allocation = zeroGainLow ∨ allocation = zeroGainHigh
  disagreement := zero
  disagreement_feasible := Or.inl rfl

/-- Weak participation alone permits a Pareto-dominated product maximizer. -/
theorem zeroGainLow_isNashSolution : zeroGainProblem.IsNashSolution zeroGainLow := by
  refine ⟨Or.inr (Or.inl rfl), ?_, ?_⟩
  · intro player
    cases player <;> norm_num [zeroGainProblem, zero, zeroGainLow]
  · intro alternative feasible _
    rcases feasible with rfl | rfl | rfl <;>
      norm_num [zeroGainProblem, zero, zeroGainLow, zeroGainHigh, Fintype.prod_bool]

theorem zeroGainLow_individuallyRational : zeroGainProblem.IsIndividuallyRational zeroGainLow :=
  zeroGainLow_isNashSolution.isIndividuallyRational

theorem zeroGainLow_not_positive :
    ¬ ∀ player, zeroGainProblem.disagreement player < zeroGainLow player := by
  intro positive
  have impossible := positive false
  norm_num [zeroGainProblem, zero, zeroGainLow] at impossible

theorem zeroGainLow_not_isPareto : ¬ zeroGainProblem.IsPareto zeroGainLow := by
  intro pareto
  apply pareto.2
  refine ⟨zeroGainHigh, Or.inr (Or.inr rfl), ?_, true, ?_⟩
  · intro player
    cases player <;> norm_num [zeroGainLow, zeroGainHigh]
  · norm_num [zeroGainLow, zeroGainHigh]

/-- The original weak-Pareto theorem remains valid for the same maximizer. -/
theorem zeroGainLow_isWeaklyPareto : zeroGainProblem.IsWeaklyPareto zeroGainLow :=
  zeroGainLow_isNashSolution.isWeaklyPareto

/-- Empty-player Pareto optimality is meaningful; unlike weak Pareto
optimality it does not demand a nonempty player carrier. -/
def emptyProblem : BargainingProblem Empty where
  feasible _ := True
  disagreement player := nomatch player
  disagreement_feasible := trivial

def emptyAllocation : Empty → ℝ := fun player => nomatch player

theorem emptyAllocation_isNashSolution : emptyProblem.IsNashSolution emptyAllocation := by
  refine ⟨trivial, ?_, ?_⟩
  · intro player
    exact player.elim
  · intro alternative _ _
    simp

theorem emptyAllocation_isPareto : emptyProblem.IsPareto emptyAllocation :=
  emptyAllocation_isNashSolution.isPareto_of_positive_gains (by
    intro player
    exact player.elim)

end GameTheory.Tests.BargainingScalarization
