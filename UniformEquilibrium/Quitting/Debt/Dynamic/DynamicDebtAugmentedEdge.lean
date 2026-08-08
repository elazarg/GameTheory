/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DebtOccupationCompactness

/-!
# Exact dynamic-debt augmented quitting edges

The multiplicative terminal-debt costate is only an upper envelope for a
player's actual finite-horizon deviation gain.  Exact local Nash slack can
discharge that envelope.  This file instead augments a Nash--Bellman edge by
the exact one-step Bellman recursion

`D = max(Q, C + c * D') - v`,

where `Q` and `C` are the two pure-action endpoints, `c` is the probability
that all opponents Continue, and `v` is the prescribed current payoff.

On an exact Nash--Bellman edge this update lies in `[0, c * D']`.  Thus exact
dynamic debt is still monotone backwards.  Moreover, zero total debt loss
and a positive successor debt force `c = 1`, giving the same opponent-support
consequence as the coarse costate without identifying the two notions.

The bounded exact dynamic-debt edge graph is also closed and compact.  No
projective extraction, occupation law, recurrence, or equilibrium conclusion
is claimed here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact one-step Bellman-debt update over a Nash--Bellman edge. -/
def quittingDynamicDebtUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι) (who : ι) : ℝ :=
  max
      (quittingRootQuitPayoff reward successor.1.1
        (quittingRootOfSimplex current.1.2) who)
      (quittingRootContinuePayoff reward successor.1.1
          (quittingRootOfSimplex current.1.2) who +
        quittingDebtOpponentContinueMass current who * successor.2 who) -
    current.1.1 who

/-- An exact Nash--Bellman edge carrying the true playerwise dynamic debt. -/
def IsQuittingDynamicDebtEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι) : Prop :=
  IsQuittingNashBellmanEdge reward current.1 successor.1 ∧
    ∀ who, current.2 who =
      quittingDynamicDebtUpdate reward current successor who

/-- Pure Quit cannot improve on the prescribed current value along an exact
Nash--Bellman edge. -/
theorem quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingNashBellmanPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current successor)
    (who : ι) :
    quittingRootQuitPayoff reward successor.1
        (quittingRootOfSimplex current.2) who ≤
      current.1 who := by
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward successor.1 (quittingRootOfSimplex current.2)).1 hedge.2
  have hquit := hnash who (PMF.pure true)
  change quittingRootQuitPayoff reward successor.1
      (quittingRootOfSimplex current.2) who ≤
    quittingRootSuccessorPayoff reward successor.1
      (quittingRootOfSimplex current.2) who + 0 at hquit
  have hvalue := congrFun hedge.1 who
  rw [hvalue]
  simpa using hquit

/-- Pure Continue cannot improve on the prescribed current value along an
exact Nash--Bellman edge. -/
theorem quittingRootContinuePayoff_le_currentValue_of_nashBellmanEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingNashBellmanPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current successor)
    (who : ι) :
    quittingRootContinuePayoff reward successor.1
        (quittingRootOfSimplex current.2) who ≤
      current.1 who := by
  have hnash :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward successor.1 (quittingRootOfSimplex current.2)).1 hedge.2
  have hcontinue := hnash who (PMF.pure false)
  change quittingRootContinuePayoff reward successor.1
      (quittingRootOfSimplex current.2) who ≤
    quittingRootSuccessorPayoff reward successor.1
      (quittingRootOfSimplex current.2) who + 0 at hcontinue
  have hvalue := congrFun hedge.1 who
  rw [hvalue]
  simpa using hcontinue

/-- The prescribed current value is at most the larger of its two pure
endpoints.  This is the elementary convex-mixture half of Bellman equality. -/
theorem currentValue_le_max_endpoints_of_nashBellmanEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingNashBellmanPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current successor)
    (who : ι) :
    current.1 who ≤
      max
        (quittingRootQuitPayoff reward successor.1
          (quittingRootOfSimplex current.2) who)
        (quittingRootContinuePayoff reward successor.1
          (quittingRootOfSimplex current.2) who) := by
  let root := quittingRootOfSimplex current.2
  let quitValue := quittingRootQuitPayoff reward successor.1 root who
  let continueValue :=
    quittingRootContinuePayoff reward successor.1 root who
  have hmix :=
    quittingRootSuccessorPayoff_eq_endpointMix reward successor.1 root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hsum' :
      (root who true).toReal + (root who false).toReal = 1 := by
    linarith
  rw [hedge.1, hmix]
  calc
    (root who true).toReal * quitValue +
          (root who false).toReal * continueValue ≤
        (root who true).toReal * max quitValue continueValue +
          (root who false).toReal * max quitValue continueValue := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _)
          ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left (le_max_right _ _)
          ENNReal.toReal_nonneg)
    _ = max quitValue continueValue := by
      rw [← add_mul, hsum', one_mul]

/-- Exact dynamic debt is nonnegative when the successor debt is
nonnegative. -/
theorem quittingDynamicDebtUpdate_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current.1 successor.1)
    (hsuccessorDebt : 0 ≤ successor.2)
    (who : ι) :
    0 ≤ quittingDynamicDebtUpdate reward current successor who := by
  let quitValue := quittingRootQuitPayoff reward successor.1.1
    (quittingRootOfSimplex current.1.2) who
  let continueValue := quittingRootContinuePayoff reward successor.1.1
    (quittingRootOfSimplex current.1.2) who
  let mass := quittingDebtOpponentContinueMass current who
  let nextDebt := successor.2 who
  have hbase : current.1.1 who ≤ max quitValue continueValue :=
    currentValue_le_max_endpoints_of_nashBellmanEdge
      reward current.1 successor.1 hedge who
  have hscaled : 0 ≤ mass * nextDebt :=
    mul_nonneg (quittingDebtOpponentContinueMass_nonneg current who)
      (hsuccessorDebt who)
  have hraise : max quitValue continueValue ≤
      max quitValue (continueValue + mass * nextDebt) := by
    exact max_le_max le_rfl (by linarith)
  unfold quittingDynamicDebtUpdate
  change 0 ≤ max quitValue (continueValue + mass * nextDebt) -
    current.1.1 who
  linarith

/-- Exact one-step debt is at most opponent survival times the successor
debt.  Local Nash slack may make this inequality strict. -/
theorem quittingDynamicDebtUpdate_le_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current.1 successor.1)
    (hsuccessorDebt : 0 ≤ successor.2)
    (who : ι) :
    quittingDynamicDebtUpdate reward current successor who ≤
      quittingDebtOpponentContinueMass current who * successor.2 who := by
  let quitValue := quittingRootQuitPayoff reward successor.1.1
    (quittingRootOfSimplex current.1.2) who
  let continueValue := quittingRootContinuePayoff reward successor.1.1
    (quittingRootOfSimplex current.1.2) who
  let mass := quittingDebtOpponentContinueMass current who
  let nextDebt := successor.2 who
  have hquit : quitValue ≤ current.1.1 who :=
    quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
      reward current.1 successor.1 hedge who
  have hcontinue : continueValue ≤ current.1.1 who :=
    quittingRootContinuePayoff_le_currentValue_of_nashBellmanEdge
      reward current.1 successor.1 hedge who
  have hscaled : 0 ≤ mass * nextDebt :=
    mul_nonneg (quittingDebtOpponentContinueMass_nonneg current who)
      (hsuccessorDebt who)
  have hmax : max quitValue (continueValue + mass * nextDebt) ≤
      current.1.1 who + mass * nextDebt := by
    apply max_le
    · linarith
    · linarith
  unfold quittingDynamicDebtUpdate
  change max quitValue (continueValue + mass * nextDebt) -
      current.1.1 who ≤ mass * nextDebt
  linarith

/-- Exact dynamic debt cannot increase when pulled one edge backwards. -/
theorem quittingDynamicDebtUpdate_le_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current.1 successor.1)
    (hsuccessorDebt : 0 ≤ successor.2)
    (who : ι) :
    quittingDynamicDebtUpdate reward current successor who ≤
      successor.2 who := by
  exact (quittingDynamicDebtUpdate_le_mul reward current successor hedge
    hsuccessorDebt who).trans
      (mul_le_of_le_one_left (hsuccessorDebt who)
        (quittingDebtOpponentContinueMass_le_one current who))

/-- Playerwise exact debt lost while moving to the successor. -/
def quittingDynamicDebtCoordinateLoss
    (current successor : QuittingDebtPoint ι) (who : ι) : ℝ :=
  successor.2 who - current.2 who

/-- Total exact dynamic-debt loss across one edge. -/
def quittingDynamicDebtEdgeLoss
    (current successor : QuittingDebtPoint ι) : ℝ :=
  ∑ who, quittingDynamicDebtCoordinateLoss current successor who

/-- Coordinate loss is nonnegative on an exact dynamic-debt edge whose
successor debt is nonnegative. -/
theorem quittingDynamicDebtCoordinateLoss_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    0 ≤ quittingDynamicDebtCoordinateLoss current successor who := by
  unfold quittingDynamicDebtCoordinateLoss
  rw [hedge.2 who]
  exact sub_nonneg.mpr
    (quittingDynamicDebtUpdate_le_successor reward current successor
      hedge.1 hsuccessorDebt who)

/-- Total exact dynamic-debt loss is nonnegative on the augmented box. -/
theorem quittingDynamicDebtEdgeLoss_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor) :
    0 ≤ quittingDynamicDebtEdgeLoss current successor := by
  unfold quittingDynamicDebtEdgeLoss
  exact Finset.sum_nonneg fun who _ ↦
    quittingDynamicDebtCoordinateLoss_nonneg reward current successor
      hsuccessor.2.1 hedge who

/-- Zero total exact-debt loss forces every coordinate loss to vanish. -/
theorem quittingDynamicDebtCoordinateLoss_eq_zero_of_edgeLoss_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hloss : quittingDynamicDebtEdgeLoss current successor = 0)
    (who : ι) :
    quittingDynamicDebtCoordinateLoss current successor who = 0 := by
  apply (Finset.sum_eq_zero_iff_of_nonneg
    (fun player _ ↦ quittingDynamicDebtCoordinateLoss_nonneg reward
      current successor hsuccessor.2.1 hedge player)).1
  · exact hloss
  · exact Finset.mem_univ who

/-- **Exact-debt zero-loss clock implication.**  Positive successor dynamic
debt on a zero-loss edge forces every opponent to Continue with total mass
one. -/
theorem quittingDebtOpponentContinueMass_eq_one_of_dynamicDebtLoss_eq_zero_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hloss : quittingDynamicDebtEdgeLoss current successor = 0)
    (owner : ι) (hdebt : 0 < successor.2 owner) :
    quittingDebtOpponentContinueMass current owner = 1 := by
  have hcoordinate :=
    quittingDynamicDebtCoordinateLoss_eq_zero_of_edgeLoss_eq_zero
      reward current successor hsuccessor hedge hloss owner
  have hcurrentEq : current.2 owner = successor.2 owner := by
    unfold quittingDynamicDebtCoordinateLoss at hcoordinate
    linarith
  have hupper := quittingDynamicDebtUpdate_le_mul reward current successor
    hedge.1 hsuccessor.2.1 owner
  rw [← hedge.2 owner, hcurrentEq] at hupper
  have hmassLe := quittingDebtOpponentContinueMass_le_one current owner
  nlinarith

/-- A positive exact-debt owner on a zero-loss edge is the only player who
may Quit at the current root. -/
theorem quittingRootOfSimplex_eq_pure_false_of_zeroDynamicDebtLoss_of_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hloss : quittingDynamicDebtEdgeLoss current successor = 0)
    (owner : ι) (hdebt : 0 < successor.2 owner)
    (other : ι) (hne : other ≠ owner) :
    quittingRootOfSimplex current.1.2 other = PMF.pure false := by
  have hmass :=
    quittingDebtOpponentContinueMass_eq_one_of_dynamicDebtLoss_eq_zero_of_pos
      reward current successor hsuccessor hedge hloss owner hdebt
  rw [quittingDebtOpponentContinueMass_eq_stationary] at hmass
  have hzero :=
    quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
      (quittingRootOfSimplex current.1.2) owner other hne hmass
  exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hzero

/-- Two positive successor dynamic-debt coordinates force the current root
to be all-Continue on a zero-loss edge. -/
theorem quittingRootOfSimplex_eq_allContinue_of_zeroDynamicDebtLoss_of_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hloss : quittingDynamicDebtEdgeLoss current successor = 0)
    (first second : ι) (hne : first ≠ second)
    (hfirst : 0 < successor.2 first) (hsecond : 0 < successor.2 second) :
    quittingRootOfSimplex current.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  funext player
  by_cases hp : player = first
  · subst player
    exact
      quittingRootOfSimplex_eq_pure_false_of_zeroDynamicDebtLoss_of_other
        reward current successor hsuccessor hedge hloss second hsecond
          first hne
  · exact
      quittingRootOfSimplex_eq_pure_false_of_zeroDynamicDebtLoss_of_other
        reward current successor hsuccessor hedge hloss first hfirst player hp

/-! ## Closed and compact exact dynamic-debt edge space -/

/-- Bounded exact dynamic-debt edge graph. -/
def quittingDynamicDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingDebtPoint ι × QuittingDebtPoint ι) :=
  {edge | edge.1 ∈ quittingDebtBox reward ∧
    edge.2 ∈ quittingDebtBox reward ∧
    IsQuittingDynamicDebtEdge reward edge.1 edge.2}

/-- The exact dynamic-debt update is jointly continuous. -/
theorem continuous_quittingDynamicDebtUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingDynamicDebtUpdate reward edge.1 edge.2 who) := by
  let endpointData :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) →
        Payoff ι × QuittingRootSimplex ι :=
    fun edge ↦ (edge.2.1.1, edge.1.1.2)
  have hendpointData : Continuous endpointData := by
    dsimp only [endpointData]
    fun_prop
  have hquit : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        quittingRootQuitPayoff reward edge.2.1.1
          (quittingRootOfSimplex edge.1.1.2) who) :=
    (continuous_quittingRootQuitPayoff_simplex reward who).comp hendpointData
  have hcontinue : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        quittingRootContinuePayoff reward edge.2.1.1
          (quittingRootOfSimplex edge.1.1.2) who) :=
    (continuous_quittingRootContinuePayoff_simplex reward who).comp
      hendpointData
  have hmass : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        quittingDebtOpponentContinueMass edge.1 who) :=
    (continuous_quittingDebtOpponentContinueMass who).comp continuous_fst
  have hsuccessorDebt : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        edge.2.2 who) := by
    fun_prop
  have hcurrentValue : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        edge.1.1.1 who) := by
    fun_prop
  unfold quittingDynamicDebtUpdate
  exact (hquit.max (hcontinue.add (hmass.mul hsuccessorDebt))).sub
    hcurrentValue

/-- The bounded exact dynamic-debt edge graph is closed. -/
theorem isClosed_quittingDynamicDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed (quittingDynamicDebtEdgeGraph reward) := by
  let nashProjection :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) →
        (QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι) :=
    fun edge ↦ (edge.1.1, edge.2.1)
  let debtCurrent :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → Payoff ι :=
    fun edge ↦ edge.1.2
  let debtSuccessor :
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → Payoff ι :=
    fun edge ↦ edge.2.2
  let recurrence : ι →
      (QuittingDebtPoint ι × QuittingDebtPoint ι) → ℝ :=
    fun who edge ↦ edge.1.2 who -
      quittingDynamicDebtUpdate reward edge.1 edge.2 who
  have hnash : IsClosed
      (nashProjection ⁻¹'
        {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
          edge.1 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
          edge.2 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
          IsQuittingNashBellmanEdge reward edge.1 edge.2}) :=
    (isClosed_quittingNashBellmanEdgeGraph reward
      (quittingRewardBound reward)).preimage (by
        dsimp only [nashProjection]
        fun_prop)
  have hcurrentDebt : IsClosed
      (debtCurrent ⁻¹' Set.Icc (0 : Payoff ι)
        (quittingPositiveSingletonDebtCap reward)) :=
    isClosed_Icc.preimage (by
      dsimp only [debtCurrent]
      fun_prop)
  have hsuccessorDebt : IsClosed
      (debtSuccessor ⁻¹' Set.Icc (0 : Payoff ι)
        (quittingPositiveSingletonDebtCap reward)) :=
    isClosed_Icc.preimage (by
      dsimp only [debtSuccessor]
      fun_prop)
  have hrecurrence : IsClosed
      {edge : QuittingDebtPoint ι × QuittingDebtPoint ι |
        ∀ who, recurrence who edge = 0} := by
    have heq : {edge : QuittingDebtPoint ι × QuittingDebtPoint ι |
          ∀ who, recurrence who edge = 0} =
        ⋂ who, {edge | recurrence who edge = 0} := by
      ext edge
      simp
    rw [heq]
    apply isClosed_iInter
    intro who
    exact isClosed_eq (by
      dsimp only [recurrence]
      exact ((continuous_apply who).comp
          (continuous_snd.comp continuous_fst)).sub
        (continuous_quittingDynamicDebtUpdate reward who)) continuous_const
  have heq : quittingDynamicDebtEdgeGraph reward =
      nashProjection ⁻¹'
          {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
            edge.1 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
            edge.2 ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
            IsQuittingNashBellmanEdge reward edge.1 edge.2} ∩
        debtCurrent ⁻¹' Set.Icc (0 : Payoff ι)
          (quittingPositiveSingletonDebtCap reward) ∩
        debtSuccessor ⁻¹' Set.Icc (0 : Payoff ι)
          (quittingPositiveSingletonDebtCap reward) ∩
        {edge | ∀ who, recurrence who edge = 0} := by
    ext edge
    simp only [quittingDynamicDebtEdgeGraph, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_preimage, nashProjection, debtCurrent,
      debtSuccessor, recurrence, quittingDebtBox,
      IsQuittingDynamicDebtEdge, sub_eq_zero]
    aesop
  rw [heq]
  exact ((hnash.inter hcurrentDebt).inter hsuccessorDebt).inter hrecurrence

/-- A limit of eventually exact bounded dynamic-debt edges is exact. -/
theorem isQuittingDynamicDebtEdge_of_tendsto_edgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {edge : QuittingDebtPoint ι × QuittingDebtPoint ι}
    {candidate : ℕ → QuittingDebtPoint ι × QuittingDebtPoint ι}
    (hcandidate : Tendsto candidate atTop (nhds edge))
    (heventually : ∀ᶠ index in atTop,
      candidate index ∈ quittingDynamicDebtEdgeGraph reward) :
    IsQuittingDynamicDebtEdge reward edge.1 edge.2 :=
  ((isClosed_quittingDynamicDebtEdgeGraph reward).mem_of_tendsto
    hcandidate heventually).2.2

/-- The bounded exact dynamic-debt edge graph is compact. -/
theorem quittingDynamicDebtEdgeGraph_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingDynamicDebtEdgeGraph reward) := by
  apply (quittingDebtBox_isCompact reward).prod
      (quittingDebtBox_isCompact reward) |>.of_isClosed_subset
    (isClosed_quittingDynamicDebtEdgeGraph reward)
  intro edge hedge
  exact ⟨hedge.1, hedge.2.1⟩

end GameTheory
