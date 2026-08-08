/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.SCCExecution
import Math.Probability.PhaseOccupationDuality

/-!
# Global occupation balance does not supply a chronological SCC path

The example has two disjoint closed recurrent classes.  A half-half invariant
occupation has zero signed charge because the classes carry opposite charges.
Every legal path from the selected positive class, however, remains there and
has prefix charge equal to its length.  Thus the global cancellation cannot be
used as an execution witness for either component.
-/

noncomputable section

namespace GameTheory
namespace EssentialAPSMultivaluedOccupationRegression

open scoped BigOperators
open Math.Probability
open Math.Probability.PhaseOccupationDuality

/-- Identity dynamics on two disjoint closed recurrent classes. -/
def kernel (_ : Unit) (current : Bool) (_ : Unit) : PMF Bool :=
  PMF.pure current

/-- One-phase schedule. -/
def word : Phase 1 → Unit := fun _ => ()

/-- Half of the global occupation is placed in each closed class. -/
def occupation : PhaseOccupation 1 Bool Unit :=
  fun _ _ _ => (1 : ℝ) / 2

/-- The half-half occupation satisfies the exact coordinate flow law. -/
theorem occupation_pointwiseFlow :
    HasPointwisePhaseShiftFlow kernel word occupation := by
  intro phase current
  cases current <;> simp [kernel, occupation]

/-- It is therefore a genuine feasible global phase occupation. -/
theorem occupation_feasible :
    IsPhaseOccupation kernel word occupation := by
  refine ⟨?_, ?_,
    hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow occupation_pointwiseFlow⟩
  · intro phase current action
    norm_num [occupation]
  · simp [phaseSum, occupation]

/-- Opposite component charges.  `false` is the selected positive class. -/
def charge : Bool → ℝ
  | false => 1
  | true => -1

/-- The global occupation cancels the charges of the two SCCs. -/
theorem global_occupation_charge_zero :
    phaseSum (fun phase current action =>
      occupation phase current action * charge current) = 0 := by
  simp [phaseSum, occupation, charge]

/-- Chronological identity edges. -/
def executableEdge (current next : Bool) : Prop := next = current

/-- A path selected in the positive SCC stays there. -/
theorem path_started_positive_stays_positive
    (state : ℕ → Bool)
    (hinitial : state 0 = false)
    (hstep : ∀ time, executableEdge (state time) (state (time + 1))) :
    ∀ time, state time = false := by
  intro time
  induction time with
  | zero => exact hinitial
  | succ time ih =>
      exact (hstep time).trans ih

/-- Its chronological prefix charge is its length, not the globally cancelled
value zero. -/
theorem positive_path_prefix_charge
    (state : ℕ → Bool)
    (hinitial : state 0 = false)
    (hstep : ∀ time, executableEdge (state time) (state (time + 1)))
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, charge (state time) = (horizon : ℝ) := by
  have hpositive := path_started_positive_stays_positive state hinitial hstep
  calc
    ∑ time ∈ Finset.range horizon, charge (state time) =
        ∑ _time ∈ Finset.range horizon, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro time htime
          simp [hpositive time, charge]
    _ = (horizon : ℝ) := by simp

/-- Regression package: global balance and incompatible chronological behavior
hold simultaneously. -/
theorem global_balance_does_not_supply_chronological_cancellation :
    (phaseSum (fun phase current action =>
        occupation phase current action * charge current) = 0) ∧
      ∀ (state : ℕ → Bool),
        state 0 = false →
        (∀ time, executableEdge (state time) (state (time + 1))) →
        ∀ horizon : ℕ,
          ∑ time ∈ Finset.range horizon, charge (state time) =
            (horizon : ℝ) := by
  exact ⟨global_occupation_charge_zero,
    fun state hinitial hstep horizon =>
      positive_path_prefix_charge state hinitial hstep horizon⟩

end EssentialAPSMultivaluedOccupationRegression
end GameTheory
