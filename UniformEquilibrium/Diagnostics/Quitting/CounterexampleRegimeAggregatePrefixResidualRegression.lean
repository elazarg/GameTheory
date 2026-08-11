/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixConsumption
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapChargedAnchorCounterexample

/-!
# Regression for residual debt versus joint absorption

The exact augmented-cap counterexample has positive aggregate debt, while its
only exact Nash predecessor root is all-Continue and therefore has zero joint
absorption.  Consequently no finite universal multiplier can bound carried
residual debt by the predecessor's absorption charge using only exact Nash and
reward/cardinality data.

This is a local endpoint regression.  It does not assert that the displayed
augmented-cap state lies in the punishment-floor reachable component.  Its
role is to rule out the missing local inequality; reachability alone supplies
no equation capable of deleting the joint-Continue-carried debt term isolated
in `prependResidual_le_jointContinue_mul_anchorDebt_add_charge`.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingDynamicDebtCapChargedAnchorCounterexample

/-- All-Continue is an exact Nash root against the augmented cap. -/
theorem allContinue_isNash_at_augmentedCap :
    IsεQuittingRootNash reward augmentedCap 0
      (quittingAllContinueRoot : Bool → PMF Bool) := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward augmentedCap (quittingAllContinueRoot : Bool → PMF Bool)).1
  intro who
  rw [endpointDifference_augmentedCap]
  simp [quittingAllContinueRoot]

/-- Positive aggregate debt cannot be bounded by any finite multiple of the
joint absorption of an exact Nash predecessor at this endpoint. -/
theorem not_currentDebt_sum_le_mul_absorption_of_nash
    (C : ℝ) (arbitraryRoot : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward augmentedCap 0 arbitraryRoot) :
    ¬(∑ who, currentDebt who) ≤
      C * quittingRootAbsorptionMass arbitraryRoot := by
  rw [absorptionCharge_eq_zero_of_nash_at_augmentedCap arbitraryRoot hnash]
  norm_num [currentDebt, Fintype.sum_bool]

/-- There is no universal endpoint theorem bounding this positive residual
by `C` times the charge of every exact Nash predecessor. -/
theorem no_universal_currentDebt_sum_le_mul_nash_absorption (C : ℝ) :
    ¬∀ arbitraryRoot : Bool → PMF Bool,
      IsεQuittingRootNash reward augmentedCap 0 arbitraryRoot →
        (∑ who, currentDebt who) ≤
          C * quittingRootAbsorptionMass arbitraryRoot := by
  intro huniversal
  exact not_currentDebt_sum_le_mul_absorption_of_nash C
    (quittingAllContinueRoot : Bool → PMF Bool)
    allContinue_isNash_at_augmentedCap
    (huniversal (quittingAllContinueRoot : Bool → PMF Bool)
      allContinue_isNash_at_augmentedCap)

end QuittingDynamicDebtCapChargedAnchorCounterexample

end GameTheory
