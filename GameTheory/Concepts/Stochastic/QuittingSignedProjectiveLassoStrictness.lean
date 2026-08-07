/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingWeightedProjectiveLasso
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FinCases

/-!
# Strictness of signed cyclic correction for a fixed candidate

The signed monodromy condition is genuinely weaker than the absolute-weighted
condition for a fixed proposed cycle and displayed value.  This file records a
minimal one-player, two-phase regression:

* every stage continues with probability `1/2`;
* all terminal rewards are zero;
* the displayed values alternate between `1` and `-1`.

The true periodic value is zero.  The two local seams are `3/2` and `-3/2`.
For either rotation the signed monodromy has magnitude `3/4`, exactly equal to
one-turn absorption, while the absolute-weighted residual is `9/4`.

This strictness is only a fixed-candidate statement.  Exact finite cycles have
zero seam and therefore package into both interfaces, as formalized by the
all-accuracy equivalence in `QuittingSignedProjectiveLasso`.
-/

noncomputable section

namespace GameTheory
namespace QuittingSignedProjectiveLassoStrictness

abbrev Player := Unit

/-- Zero terminal rewards for the one-player regression. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun _ _ => 0

/-- The fair Quit/Continue root. -/
def root : Player → PMF Bool :=
  fun _ => PMF.uniformOfFintype Bool

/-- The same fair root at both phases. -/
def cycle : Fin 2 → Player → PMF Bool :=
  fun _ => root

/-- Alternating displayed values `1,-1`. -/
def value : Fin 2 → Payoff Player :=
  fun phase _ => if phase = 0 then 1 else -1

@[simp] private theorem finRotate_zero_two :
    finRotate 2 (0 : Fin 2) = 1 := by
  decide

@[simp] private theorem finRotate_one_two :
    finRotate 2 (1 : Fin 2) = 0 := by
  decide

@[simp] theorem continueMass :
    ∀ phase : Fin 2,
      quittingStationaryContinueMass (cycle phase) = (1 / 2 : ℝ) := by
  intro phase
  unfold quittingStationaryContinueMass
  rw [Math.PMFProduct.pmfPi_apply]
  simp only [cycle, root]
  rw [show (∏ _ : Player, PMF.uniformOfFintype Bool false) =
      PMF.uniformOfFintype Bool false by simp]
  rw [PMF.uniformOfFintype_apply]
  norm_num

@[simp] theorem absorbingContribution_zero
    (tailRoot : Player → PMF Bool) :
    quittingRootAbsorbingContribution reward tailRoot () = 0 := by
  simp [quittingRootAbsorbingContribution, quittingRootExpectedPayoff,
    quittingRootPayoff, reward]

@[simp] theorem rootSuccessorPayoff
    (tail : Payoff Player) (phase : Fin 2) :
    quittingRootSuccessorPayoff reward tail (cycle phase) () =
      (1 / 2 : ℝ) * tail () := by
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    absorbingContribution_zero, continueMass]
  ring

@[simp] theorem residual_zero :
    quittingCyclicPolicyResidual reward cycle value (0 : Fin 2) () =
      (3 / 2 : ℝ) := by
  simp [quittingCyclicPolicyResidual, value]
  norm_num

@[simp] theorem residual_one :
    quittingCyclicPolicyResidual reward cycle value (1 : Fin 2) () =
      (-3 / 2 : ℝ) := by
  simp [quittingCyclicPolicyResidual, value]
  norm_num

@[simp] theorem weightedAbsorption :
    quittingCyclicWeightedAbsorption cycle = (3 / 4 : ℝ) := by
  simp [quittingCyclicWeightedAbsorption, continueMass]
  norm_num

@[simp] theorem weightedResidual_zero :
    quittingCyclicWeightedResidual reward cycle value (0 : Fin 2) () =
      (9 / 4 : ℝ) := by
  norm_num [quittingCyclicWeightedResidual, quittingCyclicResidualCharge,
    quittingCyclicPrefixWeight, quittingCyclicOrbit, continueMass]

@[simp] theorem terminalValue_zero (phase : Fin 2) :
    quittingCyclicTerminalValue reward cycle phase () = 0 := by
  let zeroValue : Fin 2 → Payoff Player := fun _ => 0
  have hpolicy : ∀ cyclePhase,
      zeroValue cyclePhase =
        quittingRootSuccessorPayoff reward
          (zeroValue (finRotate 2 cyclePhase)) (cycle cyclePhase) := by
    intro cyclePhase
    funext who
    cases who
    simp [zeroValue]
  have habsorbing :
      0 < quittingRootAbsorptionMass (cycle (0 : Fin 2)) := by
    rw [quittingRootAbsorptionMass, continueMass]
    norm_num
  have hcontract :
      (∏ cyclePhase : Fin 2,
        quittingStationaryContinueMass (cycle cyclePhase)) < 1 :=
    prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
      cycle 0 habsorbing
  have hselected :
      zeroValue = quittingCyclicTerminalValue reward cycle :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      reward cycle zeroValue hpolicy hcontract
  simpa [zeroValue] using (congrFun (congrFun hselected phase) ()).symm

/-- The alternating candidate satisfies the signed condition at error `1`. -/
theorem signedResidual_bound :
    IsQuittingRotationUniformSignedResidual reward cycle value 1 := by
  apply
    (isQuittingRotationUniformSignedResidual_iff_value_close
      reward cycle value 1 (by rw [weightedAbsorption]; norm_num)).mpr
  intro phase who
  cases who
  fin_cases phase <;> simp [value]

/-- The same candidate fails the absolute-weighted condition at error `1`. -/
theorem not_weightedResidual_bound :
    ¬IsQuittingRotationUniformWeightedResidual reward cycle value 1 := by
  intro hweighted
  have hzero := hweighted (0 : Fin 2) ()
  rw [weightedResidual_zero, weightedAbsorption] at hzero
  norm_num at hzero

/-- **Strictness regression.**  Signed monodromy accepts a fixed candidate
which the absolute-weighted residual rejects. -/
theorem signedResidual_strictly_weaker_for_fixed_candidate :
    IsQuittingRotationUniformSignedResidual reward cycle value 1 ∧
      ¬IsQuittingRotationUniformWeightedResidual reward cycle value 1 :=
  ⟨signedResidual_bound, not_weightedResidual_bound⟩

end QuittingSignedProjectiveLassoStrictness
end GameTheory
