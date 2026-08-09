/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtAugmentedEdge
import UniformEquilibrium.Quitting.Paths.SurvivalPrefixBridge

/-!
# The exact augmented-cap seam of dynamic debt

An exact dynamic-debt point carries a prescribed value `v` and its literal
best-response debt `d`.  Their sum is the augmented continuation cap.  Across
an exact dynamic-debt edge this cap is almost, but not quite, transported by
the displayed Nash--Bellman root:

`v + d = T(x, v' + d') + p ⊙ d`,

where `p i` is player `i`'s prescribed Quit probability at `x`.  Thus the
failure of the augmented cap to form an exact Bellman edge is neither an
unspecified error nor a full-vector perturbation.  It is a nonnegative
diagonal seam, supported exactly where a player both Quits and carries debt.

Consequently, vanishing of that seam is exactly the local criterion for the
displayed root to transport the augmented cap.  In that case the same root is
also exact Nash at the augmented successor cap, so the two cap states form an
exact Nash--Bellman edge.  This is a one-edge criterion only; no suffix
realization or global attachment conclusion is asserted.

This module proves only the local algebra.  It does not assert that the seam
can always be converted into absorption charge at the same cap.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The prescribed payoff plus its exact dynamic best-response debt. -/
def quittingDynamicDebtCap (state : QuittingDebtPoint ι) : Payoff ι :=
  state.1.1 + state.2

omit [DecidableEq ι] in
/-- The augmented-cap projection is continuous on the ambient debt state
space. -/
theorem continuous_quittingDynamicDebtCap :
    Continuous (quittingDynamicDebtCap : QuittingDebtPoint ι → Payoff ι) := by
  unfold quittingDynamicDebtCap
  fun_prop

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtCap_apply
    (state : QuittingDebtPoint ι) (who : ι) :
    quittingDynamicDebtCap state who = state.1.1 who + state.2 who := by
  rfl

/-- The coordinatewise obstruction to exact augmented-cap transport: a
player's prescribed Quit probability times its current dynamic debt. -/
def quittingDynamicDebtCapSeam (state : QuittingDebtPoint ι) : Payoff ι :=
  fun who =>
    (quittingRootOfSimplex state.1.2 who true).toReal * state.2 who

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtCapSeam_apply
    (state : QuittingDebtPoint ι) (who : ι) :
    quittingDynamicDebtCapSeam state who =
      (quittingRootOfSimplex state.1.2 who true).toReal * state.2 who := by
  rfl

/-- Replace a debt state's prescribed value by its augmented cap while
retaining the displayed root. -/
def quittingDynamicDebtCapPoint
    (state : QuittingDebtPoint ι) : QuittingNashBellmanPoint ι :=
  (quittingDynamicDebtCap state, state.1.2)

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtCapPoint_value
    (state : QuittingDebtPoint ι) :
    (quittingDynamicDebtCapPoint state).1 = quittingDynamicDebtCap state := by
  rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtCapPoint_root
    (state : QuittingDebtPoint ι) :
    (quittingDynamicDebtCapPoint state).2 = state.1.2 := by
  rfl

/-- Augmenting a continuation by dynamic debt does not change the pure-Quit
endpoint, because that endpoint absorbs before the continuation is reached. -/
theorem quittingRootQuitPayoff_dynamicDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingDebtPoint ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward (quittingDynamicDebtCap state) root who =
      quittingRootQuitPayoff reward state.1.1 root who := by
  unfold quittingRootQuitPayoff quittingDynamicDebtCap
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  simp

/-- Augmenting a continuation by dynamic debt raises the pure-Continue
endpoint by the opponents' Continue mass times the successor debt. -/
theorem quittingRootContinuePayoff_dynamicDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι) (who : ι) :
    quittingRootContinuePayoff reward (quittingDynamicDebtCap successor)
        (quittingRootOfSimplex current.1.2) who =
      quittingRootContinuePayoff reward successor.1.1
          (quittingRootOfSimplex current.1.2) who +
        quittingDebtOpponentContinueMass current who * successor.2 who := by
  unfold quittingRootContinuePayoff quittingDynamicDebtCap
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    ← quittingDebtOpponentContinueMass_eq_stationary current who]
  simp only [Pi.add_apply]
  ring

/-- The augmented current cap is the maximum of quitting now and continuing
to the augmented successor cap, with only the opponents' survival retained
in the latter endpoint. -/
theorem quittingDynamicDebtCap_eq_max_endpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    quittingDynamicDebtCap current who =
      max
        (quittingRootQuitPayoff reward successor.1.1
          (quittingRootOfSimplex current.1.2) who)
        (quittingRootContinuePayoff reward successor.1.1
            (quittingRootOfSimplex current.1.2) who +
          quittingDebtOpponentContinueMass current who * successor.2 who) := by
  rw [quittingDynamicDebtCap_apply, hedge.2 who]
  unfold quittingDynamicDebtUpdate
  ring

/-- If Continue has positive prescribed probability, exact Nash support and
the dynamic-debt recursion force debt to propagate with the full opponents'
Continue mass. -/
theorem quittingDynamicDebt_eq_opponentContinueMass_mul_of_continue_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2)
    (who : ι)
    (hcontinue : 0 <
      (quittingRootOfSimplex current.1.2 who false).toReal) :
    current.2 who =
      quittingDebtOpponentContinueMass current who * successor.2 who := by
  let root := quittingRootOfSimplex current.1.2
  let quitValue := quittingRootQuitPayoff reward successor.1.1 root who
  let continueValue :=
    quittingRootContinuePayoff reward successor.1.1 root who
  have hendpoint := hedge.1.2 who
  have hdifference :
      quittingRootEndpointDifference reward successor.1.1 root who =
        quitValue - continueValue := by
    rfl
  rw [hdifference] at hendpoint
  have hquit_le_continue : quitValue ≤ continueValue := by
    nlinarith [hendpoint.1]
  have hcontinue_le : continueValue ≤ current.1.1 who :=
    quittingRootContinuePayoff_le_currentValue_of_nashBellmanEdge
      reward current.1 successor.1 hedge.1 who
  have hmix :=
    quittingRootSuccessorPayoff_eq_endpointMix
      reward successor.1.1 root who
  have hpolicy := congrFun hedge.1.1 who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinue_eq : continueValue = current.1.1 who := by
    change current.1.1 who = _ at hpolicy
    change _ =
      (root who true).toReal * quitValue +
        (root who false).toReal * continueValue at hmix
    rw [hmix] at hpolicy
    have hweighted :
        (root who true).toReal * quitValue ≤
          (root who true).toReal * continueValue :=
      mul_le_mul_of_nonneg_left hquit_le_continue ENNReal.toReal_nonneg
    have hvalue_le : current.1.1 who ≤ continueValue := by
      calc
        current.1.1 who =
            (root who true).toReal * quitValue +
              (root who false).toReal * continueValue := hpolicy
        _ ≤ (root who true).toReal * continueValue +
              (root who false).toReal * continueValue :=
          add_le_add hweighted le_rfl
        _ = continueValue := by
          rw [← add_mul, add_comm, hsum, one_mul]
    exact le_antisymm hcontinue_le hvalue_le
  rw [hedge.2 who]
  unfold quittingDynamicDebtUpdate
  change
    max quitValue
        (continueValue +
          quittingDebtOpponentContinueMass current who * successor.2 who) -
        current.1.1 who = _
  have hdebt_nonneg :
      0 ≤ quittingDebtOpponentContinueMass current who * successor.2 who :=
    mul_nonneg (quittingDebtOpponentContinueMass_nonneg current who)
      (hsuccessorDebt who)
  rw [max_eq_right]
  · rw [hcontinue_eq]
    ring
  · linarith

/-- **Exact diagonal seam.**  Transporting the augmented successor cap
through the displayed root misses the augmented current cap by exactly the
current Quit probability times current debt. -/
theorem quittingDynamicDebtCap_sub_rootSuccessorPayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2)
    (who : ι) :
    quittingDynamicDebtCap current who -
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor)
          (quittingRootOfSimplex current.1.2) who =
      (quittingRootOfSimplex current.1.2 who true).toReal *
        current.2 who := by
  let root := quittingRootOfSimplex current.1.2
  have hpolicy := congrFun hedge.1.1 who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have htailDifference :
      quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who -
        quittingRootSuccessorPayoff reward successor.1.1 root who =
      quittingStationaryContinueMass root * successor.2 who := by
    unfold quittingDynamicDebtCap quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp only [Pi.add_apply]
    ring
  have hfactor :
      quittingStationaryContinueMass root =
        quittingDebtOpponentContinueMass current who *
          (root who false).toReal := by
    rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own]
    congr 1
    rw [quittingDebtOpponentContinueMass_eq_stationary]
    rfl
  by_cases hcontinueZero : (root who false).toReal = 0
  · rw [hfactor, hcontinueZero, mul_zero, zero_mul] at htailDifference
    have hquitOne : (root who true).toReal = 1 := by
      linarith
    have htailEq :
        quittingRootSuccessorPayoff reward
            (quittingDynamicDebtCap successor) root who =
          quittingRootSuccessorPayoff reward successor.1.1 root who := by
      linarith [htailDifference]
    rw [quittingDynamicDebtCap_apply]
    change current.1.1 who + current.2 who -
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who =
      (root who true).toReal * current.2 who
    change current.1.1 who =
      quittingRootSuccessorPayoff reward successor.1.1 root who at hpolicy
    rw [htailEq, ← hpolicy, hquitOne, one_mul]
    ring
  · have hcontinuePos : 0 < (root who false).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinueZero)
    have hdebt :=
      quittingDynamicDebt_eq_opponentContinueMass_mul_of_continue_pos
        reward current successor hedge hsuccessorDebt who hcontinuePos
    rw [hfactor] at htailDifference
    have htailDifference' :
        quittingRootSuccessorPayoff reward
            (quittingDynamicDebtCap successor) root who -
          quittingRootSuccessorPayoff reward successor.1.1 root who =
        (root who false).toReal * current.2 who := by
      calc
        _ = quittingDebtOpponentContinueMass current who *
              (root who false).toReal * successor.2 who := htailDifference
        _ = (root who false).toReal *
              (quittingDebtOpponentContinueMass current who *
                successor.2 who) := by ring
        _ = (root who false).toReal * current.2 who := by rw [← hdebt]
    rw [quittingDynamicDebtCap_apply]
    change current.1.1 who + current.2 who -
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who =
      (root who true).toReal * current.2 who
    change current.1.1 who =
      quittingRootSuccessorPayoff reward successor.1.1 root who at hpolicy
    have htailEq :
        quittingRootSuccessorPayoff reward
            (quittingDynamicDebtCap successor) root who =
          quittingRootSuccessorPayoff reward successor.1.1 root who +
            (root who false).toReal * current.2 who := by
      linarith [htailDifference']
    have hquitProbability :
        (root who true).toReal = 1 - (root who false).toReal := by
      linarith
    rw [htailEq, ← hpolicy, hquitProbability]
    ring

/-- Vector form of the exact seam identity. -/
theorem quittingDynamicDebtCap_eq_rootSuccessorPayoff_add_seam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2) :
    quittingDynamicDebtCap current =
      (quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor)
          (quittingRootOfSimplex current.1.2) : Payoff ι) +
        quittingDynamicDebtCapSeam current := by
  funext who
  have hseam := quittingDynamicDebtCap_sub_rootSuccessorPayoff_eq
    reward current successor hedge hsuccessorDebt who
  change quittingDynamicDebtCap current who =
    quittingRootSuccessorPayoff reward
        (quittingDynamicDebtCap successor)
        (quittingRootOfSimplex current.1.2) who +
      (quittingRootOfSimplex current.1.2 who true).toReal * current.2 who
  linarith

/-- On an exact dynamic-debt edge with nonnegative successor debt, exact
augmented-cap transport is equivalent to coordinatewise vanishing of the
diagonal debt seam. -/
theorem quittingDynamicDebtCap_transport_iff_capSeam_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2) :
    quittingDynamicDebtCap current =
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor)
          (quittingRootOfSimplex current.1.2) ↔
      quittingDynamicDebtCapSeam current = 0 := by
  constructor
  · intro htransport
    funext who
    have htransportWho := congrFun htransport who
    have hseam := quittingDynamicDebtCap_sub_rootSuccessorPayoff_eq
      reward current successor hedge hsuccessorDebt who
    simp only [quittingDynamicDebtCapSeam_apply, Pi.zero_apply]
    linarith
  · intro hseam
    rw [quittingDynamicDebtCap_eq_rootSuccessorPayoff_add_seam
      reward current successor hedge hsuccessorDebt, hseam, add_zero]

/-- A vanishing cap seam makes the displayed root exact Nash at the augmented
successor cap.  This is the strategic half of the local cap-edge criterion. -/
theorem isZeroQuittingRootNash_dynamicDebtCap_of_capSeam_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hseam : quittingDynamicDebtCapSeam current = 0) :
    IsεQuittingRootNash reward (quittingDynamicDebtCap successor) 0
      (quittingRootOfSimplex current.1.2) := by
  let root := quittingRootOfSimplex current.1.2
  have htransport :=
    (quittingDynamicDebtCap_transport_iff_capSeam_eq_zero
      reward current successor hedge hsuccessorDebt).2 hseam
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  have hmax := quittingDynamicDebtCap_eq_max_endpoints
    reward current successor hedge who
  have hsuccessorEqMax :
      quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who =
        max
          (quittingRootQuitPayoff reward
            (quittingDynamicDebtCap successor) root who)
          (quittingRootContinuePayoff reward
            (quittingDynamicDebtCap successor) root who) := by
    calc
      quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who =
          quittingDynamicDebtCap current who := by
        exact (congrFun htransport who).symm
      _ = max
          (quittingRootQuitPayoff reward
            (quittingDynamicDebtCap successor) root who)
          (quittingRootContinuePayoff reward
            (quittingDynamicDebtCap successor) root who) := by
        rw [quittingRootQuitPayoff_dynamicDebtCap,
          quittingRootContinuePayoff_dynamicDebtCap]
        exact hmax
  have hquitLe :
      quittingRootQuitPayoff reward
          (quittingDynamicDebtCap successor) root who ≤
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who := by
    rw [hsuccessorEqMax]
    exact le_max_left _ _
  have hcontinueLe :
      quittingRootContinuePayoff reward
          (quittingDynamicDebtCap successor) root who ≤
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap successor) root who := by
    rw [hsuccessorEqMax]
    exact le_max_right _ _
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward
    (quittingDynamicDebtCap successor) root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinueProbability :
      (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  have hquitRegret :
      (root who false).toReal *
          quittingRootEndpointDifference reward
            (quittingDynamicDebtCap successor) root who =
        quittingRootQuitPayoff reward
            (quittingDynamicDebtCap successor) root who -
          quittingRootSuccessorPayoff reward
            (quittingDynamicDebtCap successor) root who := by
    rw [quittingRootEndpointDifference, hmix, hcontinueProbability]
    ring
  have hcontinueRegret :
      (root who true).toReal *
          quittingRootEndpointDifference reward
            (quittingDynamicDebtCap successor) root who =
        quittingRootSuccessorPayoff reward
            (quittingDynamicDebtCap successor) root who -
          quittingRootContinuePayoff reward
            (quittingDynamicDebtCap successor) root who := by
    rw [quittingRootEndpointDifference, hmix, hcontinueProbability]
    ring
  constructor
  · rw [hquitRegret]
    linarith
  · rw [hcontinueRegret]
    linarith

/-- **Zero-seam cap-edge criterion.**  A clean exact dynamic-debt edge lifts
to an exact Nash--Bellman edge between its two augmented cap states. -/
theorem isQuittingNashBellmanEdge_dynamicDebtCapPoint_of_capSeam_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hseam : quittingDynamicDebtCapSeam current = 0) :
    IsQuittingNashBellmanEdge reward
      (quittingDynamicDebtCapPoint current)
      (quittingDynamicDebtCapPoint successor) := by
  constructor
  · exact (quittingDynamicDebtCap_transport_iff_capSeam_eq_zero
      reward current successor hedge hsuccessorDebt).2 hseam
  · exact
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (quittingDynamicDebtCap successor)
          (quittingRootOfSimplex current.1.2)).2
        (isZeroQuittingRootNash_dynamicDebtCap_of_capSeam_eq_zero
          reward current successor hedge hsuccessorDebt hseam)

end GameTheory
