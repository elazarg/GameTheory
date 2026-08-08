/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Projective.WeightedProjectiveLasso
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FinCases

/-!
# Strictness of signed cyclic correction for a fixed candidate

The signed monodromy condition is genuinely weaker than the absolute-weighted
condition for a fixed proposed cycle and displayed value.  This file records a
minimal one-player, two-phase regression:

* every stage continues with probability `1/2`;
* the displayed value differs from the true periodic value by `1,-1` around
  the two phases.

The local policy residuals are therefore `3/2,-3/2`.  For either rotation the
signed one-turn charge has magnitude `3/4`, exactly equal to one-turn
absorption, while the absolute-weighted residual is `9/4`.

This strictness is only a fixed-candidate statement.  Exact finite cycles have
zero seam and therefore package back into the signed interface, as formalized
by the all-accuracy equivalence in `QuittingSignedProjectiveLasso`.
-/

noncomputable section

namespace GameTheory
namespace QuittingSignedProjectiveLassoStrictness

open Math.PMFProduct

abbrev Player := Unit
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- Zero terminal rewards; only cyclic correction is being tested. -/
def reward (_ : Terminal) : Payoff Player := 0

/-- A marginal which quits and continues with probability `1/2`. -/
def halfCoin : PMF Bool := PMF.uniformOfFintype Bool

/-- The same half-continuation root at both phases. -/
def cycle (_ : Fin 2) (_ : Player) : PMF Bool := halfCoin

/-- Alternating displacement from the exact periodic value. -/
def displacement (phase : Fin 2) : ℝ :=
  if phase = 0 then 1 else -1

/-- The exact periodic continuation shifted by the alternating displacement. -/
def value (phase : Fin 2) : Payoff Player :=
  fun who =>
    quittingCyclicTerminalValue reward cycle phase who + displacement phase

@[simp] theorem abs_displacement (phase : Fin 2) :
    |displacement phase| = 1 := by
  fin_cases phase <;> norm_num [displacement]

@[simp] private theorem finRotate_zero_two :
    finRotate 2 (0 : Fin 2) = 1 := by
  decide

@[simp] private theorem finRotate_one_two :
    finRotate 2 (1 : Fin 2) = 0 := by
  decide

@[simp] theorem displacement_finRotate (phase : Fin 2) :
    displacement (finRotate 2 phase) = -displacement phase := by
  fin_cases phase <;> simp [displacement]

@[simp] theorem value_sub_terminalValue (phase : Fin 2) (who : Player) :
    value phase who - quittingCyclicTerminalValue reward cycle phase who =
      displacement phase := by
  simp [value]

@[simp] theorem continueMass_cycle (phase : Fin 2) :
    quittingStationaryContinueMass (cycle phase) = (1 / 2 : ℝ) := by
  simp [quittingStationaryContinueMass, cycle, halfCoin,
    quittingAllContinueAction, pmfPi_apply, PMF.uniformOfFintype_apply]

/-- The displayed alternating displacement forces residual `3/2` times that
displacement at each phase. -/
theorem policyResidual_eq (phase : Fin 2) (who : Player) :
    quittingCyclicPolicyResidual reward cycle value phase who =
      (3 / 2 : ℝ) * displacement phase := by
  have hstep :=
    quittingCyclicValue_sub_terminalValue_step_with_residual
      reward cycle value who phase
  simp only [value_sub_terminalValue, continueMass_cycle,
    displacement_finRotate] at hstep
  linarith

@[simp] theorem weightedAbsorption_eq :
    quittingCyclicWeightedAbsorption cycle = (3 / 4 : ℝ) := by
  norm_num [quittingCyclicWeightedAbsorption, continueMass_cycle,
    Fin.prod_univ_two]

/-- The signed condition accepts the candidate exactly at error `1`. -/
theorem signedResidual_bound :
    IsQuittingRotationUniformSignedResidual reward cycle value 1 := by
  have habsorption : 0 < quittingCyclicWeightedAbsorption cycle := by
    rw [weightedAbsorption_eq]
    norm_num
  rw [isQuittingRotationUniformSignedResidual_iff_value_close
    reward cycle value 1 habsorption]
  intro phase who
  rw [value_sub_terminalValue, abs_displacement]

/-- Absolute weighted seam variation is `9/4` at either rotation. -/
theorem weightedResidual_eq (phase : Fin 2) (who : Player) :
    quittingCyclicWeightedResidual reward cycle value phase who =
      (9 / 4 : ℝ) := by
  classical
  norm_num [quittingCyclicWeightedResidual, quittingCyclicResidualCharge,
    Finset.sum_range_succ, quittingCyclicPrefixWeight_succ,
    policyResidual_eq, continueMass_cycle, abs_displacement]

/-- The stronger absolute-weighted predicate rejects the same candidate at
error `1`. -/
theorem not_weightedResidual_bound :
    ¬IsQuittingRotationUniformWeightedResidual reward cycle value 1 := by
  intro hweighted
  have h := hweighted (0 : Fin 2) ()
  rw [weightedResidual_eq, weightedAbsorption_eq] at h
  norm_num at h

/-- **Strictness regression.**  Signed monodromy accepts a fixed candidate
which absolute-weighted residual variation rejects. -/
theorem signedResidual_strictly_weaker_for_fixed_candidate :
    IsQuittingRotationUniformSignedResidual reward cycle value 1 ∧
      ¬IsQuittingRotationUniformWeightedResidual reward cycle value 1 :=
  ⟨signedResidual_bound, not_weightedResidual_bound⟩

end QuittingSignedProjectiveLassoStrictness
end GameTheory
