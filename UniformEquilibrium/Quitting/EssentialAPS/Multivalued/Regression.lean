/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.Execution
import Math.Probability.PhaseOccupationDuality

/-!
# SCC chronology regressions

A normalized occupation may cancel signed charge by placing mass in different
closed SCCs.  Such a vector is not the law of one chronological path from a
specified entry.  The two-state example below is intentionally elementary:
each state is its own closed SCC, the half-half occupation has zero signed
charge, and every path starting in `false` remains there with charge `+1` at
every stage.

The regression is stated through the production phase-occupation API and then
through the corresponding path relation.  It prevents a future flow theorem
from replacing recurrent-component selection by global balance.
-/

noncomputable section

namespace GameTheory
namespace MultivaluedSCCRegression

open Math Probability
open Math.Probability.PhaseOccupationDuality

/-- Two disconnected deterministic recurrent classes. -/
def twoSCCKernel (_ : Unit) (state : Bool) (_ : Unit) : PMF Bool :=
  PMF.pure state

/-- The one-phase schedule for the disconnected kernel. -/
def twoSCCWord : Phase 1 → Unit := fun _ => ()

/-- Half of the global occupation is placed in each closed class. -/
def twoSCCOccupation : PhaseOccupation 1 Bool Unit :=
  fun _ _ _ => (1 : ℝ) / 2

/-- The half-half vector obeys the exact pointwise flow equations. -/
theorem twoSCCOccupation_pointwiseFlow :
    HasPointwisePhaseShiftFlow twoSCCKernel twoSCCWord twoSCCOccupation := by
  intro phase state
  fin_cases state <;> norm_num [twoSCCKernel, twoSCCOccupation]

/-- Hence the globally balanced vector is a genuine normalized phase
occupation, not merely an informal signed combination. -/
theorem twoSCCOccupation_feasible :
    IsPhaseOccupation twoSCCKernel twoSCCWord twoSCCOccupation := by
  refine ⟨?_, ?_,
    hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow
      twoSCCOccupation_pointwiseFlow⟩
  · intro phase state action
    norm_num [twoSCCOccupation]
  · norm_num [phaseSum, twoSCCOccupation]

/-- Opposite charges assigned to the two recurrent classes. -/
def twoSCCSignedCharge : Bool → ℝ
  | false => 1
  | true => -1

/-- Global occupation balance cancels the two SCC charges exactly. -/
theorem twoSCCOccupation_signedCharge_zero :
    phaseSum (fun phase state action =>
      twoSCCOccupation phase state action * twoSCCSignedCharge state) = 0 := by
  norm_num [phaseSum, twoSCCOccupation, twoSCCSignedCharge]

/-- The chronological transition relation associated with the deterministic
self-loop kernel. -/
def twoSCCStep (source target : Bool) : Prop := target = source

/-- A path started in the `false` SCC can never use the cancelling charge from
the other SCC. -/
theorem twoSCCPath_from_false_constant
    (path : ℕ → Bool) (hinitial : path 0 = false)
    (hstep : ∀ time, twoSCCStep (path time) (path (time + 1))) :
    ∀ time, path time = false := by
  intro time
  induction time with
  | zero => exact hinitial
  | succ time ih =>
      exact (hstep time).trans ih

/-- Every positive-length chronological prefix from `false` has strictly
positive total charge, despite the zero global occupation charge. -/
theorem twoSCCPath_from_false_prefixCharge
    (path : ℕ → Bool) (hinitial : path 0 = false)
    (hstep : ∀ time, twoSCCStep (path time) (path (time + 1)))
    (horizon : ℕ) :
    (∑ time in Finset.range horizon, twoSCCSignedCharge (path time)) =
      (horizon : ℝ) := by
  have hconstant := twoSCCPath_from_false_constant path hinitial hstep
  calc
    (∑ time in Finset.range horizon, twoSCCSignedCharge (path time)) =
        ∑ _time in Finset.range horizon, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro time _
      rw [hconstant time]
      rfl
    _ = (horizon : ℝ) := by simp

/-- In particular no nonempty executable prefix from `false` realizes the
zero charge of the global occupation. -/
theorem twoSCC_globalOccupationBalance_not_chronological
    (path : ℕ → Bool) (hinitial : path 0 = false)
    (hstep : ∀ time, twoSCCStep (path time) (path (time + 1)))
    {horizon : ℕ} (horizonPos : 0 < horizon) :
    (∑ time in Finset.range horizon, twoSCCSignedCharge (path time)) ≠ 0 := by
  rw [twoSCCPath_from_false_prefixCharge path hinitial hstep horizon]
  exact_mod_cast horizonPos.ne'

end MultivaluedSCCRegression
end GameTheory
