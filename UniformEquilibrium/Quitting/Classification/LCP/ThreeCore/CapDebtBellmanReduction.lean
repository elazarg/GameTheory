/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# Autonomous cap--total-debt recursion

For an arbitrary product root, terminal semantic debt splits exactly into
surviving tail debt plus the one-row Nash defect computed against the absolute
cap.  Consequently the action on the cap vector and total debt is autonomous;
the individual prescribed coordinates carry no additional information for
this recursion.

This reduction is exact for arbitrary finite quitting tables. It does not
construct a positive barrier for the remaining full-core four-player branch.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingRootContinuePayoff_update_pair_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward
        (Function.update pair.1 who (pair.2 who)) root who =
      quittingRootContinuePayoff reward pair.2 root who := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp

/-- Exact arbitrary-root cap--debt recursion in one coordinate.  The local
error is the ordinary one-row Nash defect evaluated at the cap vector, not at
the prescribed vector. -/
theorem quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoordinateNashDefect reward pair.2 root who := by
  have hquit :
      quittingRootQuitPayoff reward pair.1 root who =
        quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant reward pair.1 pair.2 root who
  have hcontinue :=
    quittingRootContinuePayoff_update_pair_eq_cap reward pair root who
  have hsuccessor :
      quittingRootSuccessorPayoff reward pair.2 root who -
          quittingRootSuccessorPayoff reward pair.1 root who =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
    change
      quittingRootExpectedPayoff reward pair.2 root who -
          quittingRootExpectedPayoff reward pair.1 root who = _
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootExpectedPayoff_eq_absorbingContribution_add]
    unfold quittingTerminalSemanticDebt
    ring
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
  dsimp only
  rw [hquit, hcontinue]
  unfold quittingTerminalSemanticDebt at hsuccessor
  rw [← hsuccessor]
  ring

/-- Exact arbitrary-root recursion for total terminal semantic debt. -/
theorem quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) =
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        quittingRootTotalNashDefect reward pair.2 root := by
  unfold quittingTerminalSemanticDebtSum quittingRootTotalNashDefect
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro who _
  exact
    quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect
      reward pair root who

/-- The projected transition on `(cap, total debt)` induced by a product
root. -/
def quittingTerminalCapDebtPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (state : Payoff ι × ℝ) : Payoff ι × ℝ :=
  (fun who =>
      max
        (quittingRootQuitPayoff reward state.1 root who)
        (quittingRootContinuePayoff reward state.1 root who),
    quittingStationaryContinueMass root * state.2 +
      quittingRootTotalNashDefect reward state.1 root)

/-- Projecting a semantic prefix to its cap and total debt is exactly the
autonomous cap--debt transition. -/
theorem quittingTerminalCapDebtPrefix_projection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) :
    ((quittingTerminalSemanticPrefix reward root pair).2,
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair)) =
      quittingTerminalCapDebtPrefix reward root
        (pair.2, quittingTerminalSemanticDebtSum pair) := by
  apply Prod.ext
  · funext who
    have hquit :
        quittingRootQuitPayoff reward pair.1 root who =
          quittingRootQuitPayoff reward pair.2 root who :=
      quittingRootQuitPayoff_continuation_invariant
        reward pair.1 pair.2 root who
    have hcontinue :=
      quittingRootContinuePayoff_update_pair_eq_cap reward pair root who
    unfold quittingTerminalCapDebtPrefix quittingTerminalSemanticPrefix
    dsimp only
    rw [hquit, hcontinue]
  · exact
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
        reward pair root

end GameTheory
