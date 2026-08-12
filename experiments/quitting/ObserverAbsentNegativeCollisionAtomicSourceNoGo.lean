/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.Q182EndpointRecipientAtomInterfaceNoGo
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentRectangleBaselineDispatch
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtOwnerTransferCounterexample

/-!
# A forced-owner atomic barrier does not return to the actual source row

The observer-absent and negative-collision leaves both reach the atomic
blocker barrier, but at different rows.  In the negative-collision leaf the
sure quitter is part of the actual source profile.  In the observer-absent
leaf the sure quitter was installed counterfactually, and the outsider edge
must still be transported back across the owner square.

The two-player square below is a sharp regression for identifying those two
objects.  The counterfactual forced-Quit row has a positive outsider defect,
the selected outsider action has positive support, and the associated
forced-Continue-face loss is positive.  Nevertheless the actual source root
is exact endpoint Nash and both pure source actions have zero gain.

Neither positive global-minimum provenance nor the counterexample terminal
gap can be added to this local witness: either addition would already imply
nonexistence of a uniform-equilibrium payoff, contradicting the unconditional
two-player theorem.  Thus those global hypotheses do not provide an
independent source-row transport principle.  A genuine merger of the two
leaves needs a new signed square identity that returns the forced-row edge to
the carrier; the shared atomic barrier alone is insufficient.
-/

noncomputable section

namespace GameTheory
namespace ObserverAbsentNegativeCollisionAtomicSourceNoGo

open StochasticGame Math.Probability Math.PMFProduct
open QuittingDynamicDebtOwnerTransferCounterexample

abbrev owner : Bool := false
abbrev outsider : Bool := true

def ownerContinueRoot : Bool → PMF Bool :=
  Function.update root owner (PMF.pure false)

def ownerQuitRoot : Bool → PMF Bool :=
  Function.update root owner (PMF.pure true)

@[simp] theorem outsider_quitProbability :
    (root outsider true).toReal = 1 / 2 := by
  norm_num [root, outsider, PMF.uniformOfFintype_apply]

theorem actual_pureQuit_gain_eq_zero :
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure true) = 0 := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [true_quitPayoff, true_continuePayoff]
  ring

theorem actual_pureContinue_gain_eq_zero :
    quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure false) = 0 := by
  rw [quittingRootDeviationGain_pure_false_eq]
  unfold quittingRootEndpointDifference
  rw [true_quitPayoff, true_continuePayoff]
  ring

theorem ownerContinue_outsider_quitPayoff_eq_neg_one :
    quittingRootQuitPayoff reward (0 : Payoff Bool) ownerContinueRoot
        outsider = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff ownerContinueRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerContinue_outsider_continuePayoff_eq_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) ownerContinueRoot
        outsider = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    ownerContinueRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerContinue_pureQuit_gain_eq_neg_half :
    quittingRootDeviationGain reward (0 : Payoff Bool) ownerContinueRoot
        outsider (PMF.pure true) = -(1 / 2 : ℝ) := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [ownerContinue_outsider_quitPayoff_eq_neg_one,
    ownerContinue_outsider_continuePayoff_eq_zero]
  norm_num [ownerContinueRoot, root, outsider,
    PMF.uniformOfFintype_apply]

theorem ownerQuit_outsider_quitPayoff_eq_one :
    quittingRootQuitPayoff reward (0 : Payoff Bool) ownerQuitRoot outsider =
      1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff ownerQuitRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerQuit_outsider_continuePayoff_eq_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) ownerQuitRoot outsider =
      0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff ownerQuitRoot
  rw [QuittingDynamicDebtOwnerTransferCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [root, PMF.uniformOfFintype_apply, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction,
    owner, outsider]

theorem ownerQuit_pureQuit_gain_eq_half :
    quittingRootDeviationGain reward (0 : Payoff Bool) ownerQuitRoot outsider
        (PMF.pure true) = 1 / 2 := by
  rw [quittingRootDeviationGain_pure_true_eq]
  unfold quittingRootEndpointDifference
  rw [ownerQuit_outsider_quitPayoff_eq_one,
    ownerQuit_outsider_continuePayoff_eq_zero]
  norm_num [ownerQuitRoot, root, outsider, PMF.uniformOfFintype_apply]

theorem positive_quit_rectangle_eq_one :
    quittingOwnerOutsiderDeviationRectangle reward (0 : Payoff Bool) root
        owner outsider true = 1 := by
  unfold quittingOwnerOutsiderDeviationRectangle
  rw [show Function.update root owner (PMF.pure true) = ownerQuitRoot by rfl,
    show Function.update root owner (PMF.pure false) = ownerContinueRoot by rfl,
    ownerQuit_pureQuit_gain_eq_half,
    ownerContinue_pureQuit_gain_eq_neg_half]
  ring

/-- The counterfactual forced-Quit row carries a positive outsider defect.
This is exactly the local atomic object exported by both frontier leaves. -/
theorem half_le_forcedOwnerOutsiderDefect :
    (1 / 2 : ℝ) ≤ quittingForcedOwnerOutsiderDefect reward ownerQuitRoot owner := by
  have hcoordinate := quittingForcedOwnerOutsiderCoordinateDefect_le
    reward ownerQuitRoot owner outsider
  have hne : outsider ≠ owner := by decide
  have howner : ownerQuitRoot owner = PMF.pure true := by
    simp [ownerQuitRoot, owner]
  have hdefect := quittingRootCoordinateNashDefect_eq_forcedOwnerGain
    reward (0 : Payoff Bool) ownerQuitRoot owner outsider howner hne
  have hpure := ownerQuit_pureQuit_gain_eq_half
  have hpureLe := pureEndpointDeviationGain_le_coordinateNashDefect
    reward (0 : Payoff Bool) ownerQuitRoot outsider true
  have hraw : (1 / 2 : ℝ) ≤
      max (quittingStationaryFixedOpponentsQuitValue reward ownerQuitRoot outsider)
          (quittingStationaryFixedOpponentsContinueReward reward ownerQuitRoot outsider) -
        quittingRootAbsorbingContribution reward ownerQuitRoot outsider := by
    rw [← hdefect]
    rw [hpure] at hpureLe
    exact hpureLe
  have hcoordinateLower : (1 / 2 : ℝ) ≤
      quittingForcedOwnerOutsiderCoordinateDefect reward ownerQuitRoot owner
        outsider := by
    unfold quittingForcedOwnerOutsiderCoordinateDefect
    rw [if_neg hne]
    exact hraw.trans (le_max_right 0 _)
  exact hcoordinateLower.trans hcoordinate

/-- **Atomic source-row mismatch.**  A quantitatively positive forced-owner
defect and a supported positive face loss coexist with zero gain for both
pure actions at the actual source and exact endpoint Nash there. -/
theorem positive_forcedBarrier_but_no_actualSourceEdge :
    (1 / 2 : ℝ) ≤
        quittingForcedOwnerOutsiderDefect reward ownerQuitRoot owner ∧
      (root outsider true).toReal = 1 / 2 ∧
      max (-quittingRootDeviationGain reward (0 : Payoff Bool)
        ownerContinueRoot outsider (PMF.pure true)) 0 = 1 / 2 ∧
      quittingOwnerOutsiderDeviationRectangle reward (0 : Payoff Bool) root
        owner outsider true = 1 ∧
      quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure true) = 0 ∧
      quittingRootDeviationGain reward (0 : Payoff Bool) root outsider
        (PMF.pure false) = 0 ∧
      IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root := by
  refine ⟨half_le_forcedOwnerOutsiderDefect, outsider_quitProbability, ?_,
    positive_quit_rectangle_eq_one, actual_pureQuit_gain_eq_zero,
    actual_pureContinue_gain_eq_zero, root_isEndpointNash_zero⟩
  rw [ownerContinue_pureQuit_gain_eq_neg_half]
  norm_num

/-- A positive global semantic-debt minimum cannot be grafted onto this
regression.  Such a premise would already contradict unconditional
two-player uniform-equilibrium existence. -/
theorem not_exists_positive_globalSemanticDebtMinimum :
    ¬∃ minimum : QuittingTerminalSemanticPair Bool,
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum minimum := by
  rintro ⟨minimum, hminimum, hpositive⟩
  have hno := no_uniformPayoff_of_positive_globalSemanticDebtMinimum
    reward minimum hminimum hpositive
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
      (by decide) reward)

/-- Likewise the ambient counterexample terminal gap is unavailable in the
local table.  Adding it would itself assert that this two-player game is a
counterexample. -/
theorem not_exists_positive_terminalExploitabilityGap :
    ¬∃ gap : ℝ, 0 < gap ∧ HasTerminalExploitabilityGap reward gap := by
  intro hgap
  have hno :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).2 hgap
  exact hno
    (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
      (by decide) reward)

end ObserverAbsentNegativeCollisionAtomicSourceNoGo
end GameTheory
