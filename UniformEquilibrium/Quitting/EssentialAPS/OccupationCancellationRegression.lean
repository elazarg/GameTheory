/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathExecution
import Math.Probability.PhaseOccupationDuality

/-!
# Closed-class occupation cancellation is not chronological execution

This semantic fence has two disjoint closed recurrent classes. A half-half
invariant occupation has zero signed charge because the two classes carry
opposite signs. Every chronological execution beginning in the positive class
remains there, and its prefix charge is its length.

Thus an aggregate stationary cancellation does not select, or substitute for,
one executable path. The charged-path formulation also records the same
positive prefix growth in the generic execution API.
-/

noncomputable section

namespace GameTheory
namespace EssentialAPSOccupationCancellationRegression

open scoped BigOperators
open Math.ChargedPathBudget
open Math.Probability
open Math.Probability.PhaseOccupationDuality

/-- Identity dynamics on two disjoint closed recurrent classes. -/
def kernel (_ : Unit) (current : Bool) (_ : Unit) : PMF Bool :=
  PMF.pure current

/-- A one-phase schedule. -/
def word : Phase 1 → Unit := fun _ => ()

/-- Half of the global occupation is placed in each closed class. -/
def occupation : PhaseOccupation 1 Bool Unit :=
  fun _ _ _ => (1 : ℝ) / 2

/-- The half-half occupation satisfies exact coordinate flow. -/
theorem occupation_pointwiseFlow :
    HasPointwisePhaseShiftFlow kernel word occupation := by
  intro phase current
  cases current <;> simp [kernel, occupation]

/-- The half-half occupation is a feasible global phase occupation. -/
theorem occupation_feasible :
    IsPhaseOccupation kernel word occupation := by
  refine ⟨?_, ?_,
    hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow occupation_pointwiseFlow⟩
  · intro phase current action
    norm_num [occupation]
  · norm_num [phaseSum, occupation]

/-- Opposite signed charges on the two closed classes. -/
def signedCharge : Bool → ℝ
  | false => 1
  | true => -1

/-- The global occupation cancels the signed class charges. -/
theorem global_occupation_signedCharge_zero :
    phaseSum (fun phase current action =>
      occupation phase current action * signedCharge current) = 0 := by
  norm_num [phaseSum, occupation, signedCharge]

/-- An edge in the identity relation remembers its closed class. -/
structure IdentityEdge where
  point : Bool

/-- The charged identity relation. Its nonnegative path charge counts elapsed
chronological edges; the separate signed observable detects the cancellation
mistake. -/
def identityRelation : ChargedRelation Bool IdentityEdge where
  src edge := edge.point
  tgt edge := edge.point
  charge _ := 1
  charge_nonneg _ := by norm_num

/-- Every chronological edge stream starting in the positive class stays in
that class. -/
theorem edgeStream_started_positive_stays_positive
    (state : ℕ → Bool) (edge : ℕ → IdentityEdge)
    (hinitial : state 0 = false)
    (hstep : ∀ time,
      identityRelation.src (edge time) = state time ∧
        identityRelation.tgt (edge time) = state (time + 1)) :
    ∀ time, state time = false := by
  intro time
  induction time with
  | zero => exact hinitial
  | succ time ih =>
      have hsame : state (time + 1) = state time :=
        (hstep time).2.symm.trans (hstep time).1
      exact hsame.trans ih

/-- The chronological signed prefix charge is its length, rather than the
globally cancelled value zero. -/
theorem positive_edgeStream_signedPrefixCharge
    (state : ℕ → Bool) (edge : ℕ → IdentityEdge)
    (hinitial : state 0 = false)
    (hstep : ∀ time,
      identityRelation.src (edge time) = state time ∧
        identityRelation.tgt (edge time) = state (time + 1))
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, signedCharge (state time) =
      (horizon : ℝ) := by
  have hpositive :=
    edgeStream_started_positive_stays_positive state edge hinitial hstep
  calc
    ∑ time ∈ Finset.range horizon, signedCharge (state time) =
        ∑ _time ∈ Finset.range horizon, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro time _htime
          simp [hpositive time, signedCharge]
    _ = (horizon : ℝ) := by simp

/-- The same stream, packaged as an established charged infinite path, has
partial charge equal to elapsed time. -/
theorem positive_edgeStream_chargedPartialCharge
    (state : ℕ → Bool) (edge : ℕ → IdentityEdge)
    (hinitial : state 0 = false)
    (hstep : ∀ time,
      identityRelation.src (edge time) = state time ∧
        identityRelation.tgt (edge time) = state (time + 1))
    (horizon : ℕ) :
    (ChargedRelation.infinitePathFromOfEdgeStream
      identityRelation false state edge hinitial hstep).partialCharge horizon =
        (horizon : ℝ) := by
  rw [ChargedRelation.infinitePathFromOfEdgeStream_partialCharge]
  simp [identityRelation]

/-- Regression package: global cancellation and incompatible chronological
behavior hold simultaneously. -/
theorem global_balance_does_not_supply_chronological_cancellation :
    (phaseSum (fun phase current action =>
        occupation phase current action * signedCharge current) = 0) ∧
      ∀ (state : ℕ → Bool) (edge : ℕ → IdentityEdge),
        state 0 = false →
        (∀ time,
          identityRelation.src (edge time) = state time ∧
            identityRelation.tgt (edge time) = state (time + 1)) →
        ∀ horizon : ℕ,
          ∑ time ∈ Finset.range horizon, signedCharge (state time) =
            (horizon : ℝ) := by
  exact ⟨global_occupation_signedCharge_zero,
    fun state edge hinitial hstep horizon =>
      positive_edgeStream_signedPrefixCharge
        state edge hinitial hstep horizon⟩

end EssentialAPSOccupationCancellationRegression
end GameTheory
