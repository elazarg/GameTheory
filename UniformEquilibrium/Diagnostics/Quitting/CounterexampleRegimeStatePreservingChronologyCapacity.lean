/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapacityNearMaximizerRebase

/-!
# State-preserving capacity on zero-boundary exact-D chronologies

The unrestricted prefix capacity can approach its supremum at states unrelated
to the positive exact dynamic debt selected by the counterexample regime.  This
file instead takes the supremum over the literal zero-boundary exact-D chains.
Every member of this family retains aggregate initial debt at least the regime's
terminal gap, while prepending an exact Nash--Bellman predecessor remains in the
same family and adds exactly that predecessor root's absorption mass.

Consequently, for every positive tolerance there is one finite chronology which
simultaneously carries positive calibrated debt and admits no exact bounded
predecessor with absorption as large as the tolerance.  Compactness is not used
to assert attainment of the infinite-horizon supremum.  The result is the exact
finite near-maximality statement needed before any projective extraction.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {cutoff : ℕ}

/-- Total literal absorption along the preterminal edges of one finite
zero-boundary exact Nash--Bellman chain. -/
def quittingFiniteZeroBoundaryChainCharge
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingRootAbsorptionMass
      (quittingFiniteNashBellmanPathRoots cutoff path time)

omit [DecidableEq ι] in
/-- Finite chain charge is nonnegative. -/
theorem quittingFiniteZeroBoundaryChainCharge_nonneg
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    0 ≤ quittingFiniteZeroBoundaryChainCharge cutoff path := by
  unfold quittingFiniteZeroBoundaryChainCharge
  apply Finset.sum_nonneg
  intro time _
  unfold quittingRootAbsorptionMass
  exact sub_nonneg.mpr
    (quittingStationaryContinueMass_le_one
      (quittingFiniteNashBellmanPathRoots cutoff path time))

/-- The intrinsic reversed admissible segment has exactly the sum of the
displayed roots' absorption masses on that segment. -/
theorem chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    ∀ (start fuel : ℕ) (hend : start + fuel ≤ cutoff),
      (quittingFiniteDynamicDebtAdmissibleReverseSegment
          path hpath hpunishment start fuel hend).chargeSum =
        ∑ offset ∈ Finset.range fuel,
          quittingRootAbsorptionMass
            (quittingFiniteNashBellmanPathRoots cutoff path (start + offset))
  | start, 0, hend => by
      simp [quittingFiniteDynamicDebtAdmissibleReverseSegment]
  | start, fuel + 1, hend => by
      simp only [quittingFiniteDynamicDebtAdmissibleReverseSegment]
      change quittingRootAbsorptionMass
            (quittingRootOfSimplex
              (quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path
                (start + fuel)).1.2) +
          (quittingFiniteDynamicDebtAdmissibleReverseSegment
            path hpath hpunishment start fuel (by omega)).chargeSum = _
      rw [chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
        path hpath hpunishment start fuel]
      rw [Finset.sum_range_succ]
      have hroot : quittingRootOfSimplex
            (quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path
              (start + fuel)).1.2 =
          quittingFiniteNashBellmanPathRoots cutoff path (start + fuel) := by
        unfold quittingFiniteNashBellmanPathDynamicDebtPoint
        rw [dif_pos (by omega)]
        rw [quittingFiniteNashBellmanPathRoots, dif_pos (by omega)]
      rw [hroot]
      ring

/-- Every zero-boundary exact-D chronology is bounded by the regime's global
punishment-floor prefix capacity when the punishment vector is nonpositive. -/
theorem quittingFiniteZeroBoundaryChainCharge_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryChainCharge cutoff path ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  let segment := quittingFiniteDynamicDebtAdmissibleReverseSegment
    path hpath hpunishment 0 cutoff (by omega)
  have hcharge : segment.chargeSum =
      quittingFiniteZeroBoundaryChainCharge cutoff path := by
    simpa [segment, quittingFiniteZeroBoundaryChainCharge] using
      (chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
        path hpath hpunishment 0 cutoff (by omega))
  rw [← hcharge]
  rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
  exact regime.prefixCharge_le _

/-- The set of charges of all finite zero-boundary exact-D chronologies. -/
def quittingZeroBoundaryChronologyCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set ℝ :=
  {charge | ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
    path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      charge = quittingFiniteZeroBoundaryChainCharge cutoff path}

/-- State-preserving chronology capacity: the supremum of literal absorption
charges over all finite zero-boundary exact-D chains. -/
def quittingZeroBoundaryChronologyCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sSup (quittingZeroBoundaryChronologyCharges reward)

/-- The chronology charge set is nonempty. -/
theorem quittingZeroBoundaryChronologyCharges_nonempty :
    (quittingZeroBoundaryChronologyCharges reward).Nonempty := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward 0
  refine ⟨0, 0, path,
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem reward 0,
    ?_⟩
  simp [quittingFiniteZeroBoundaryChainCharge]

/-- The counterexample regime bounds the chronology charge family. -/
theorem quittingZeroBoundaryChronologyCharges_bddAbove
    (regime : QuittingCounterexampleRegime reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    BddAbove (quittingZeroBoundaryChronologyCharges reward) := by
  refine ⟨quittingPunishmentFloorPrefixChargeBound reward, ?_⟩
  rintro charge ⟨cutoff, path, hpath, rfl⟩
  exact quittingFiniteZeroBoundaryChainCharge_le_prefixChargeBound
    regime hpunishment cutoff path hpath

/-- Every member charge lies below the chronology capacity. -/
theorem quittingFiniteZeroBoundaryChainCharge_le_chronologyCapacity
    (regime : QuittingCounterexampleRegime reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryChainCharge cutoff path ≤
      quittingZeroBoundaryChronologyCapacity reward := by
  exact le_csSup
    (quittingZeroBoundaryChronologyCharges_bddAbove regime hpunishment)
    ⟨cutoff, path, hpath, rfl⟩

omit [DecidableEq ι] in
/-- Prepending one bounded exact predecessor adds exactly its root's
absorption mass to the chronology charge. -/
theorem quittingFiniteZeroBoundaryChainCharge_prependPoint
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingFiniteZeroBoundaryChainCharge (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path) =
      quittingRootAbsorptionMass (quittingRootOfSimplex predecessor.2) +
        quittingFiniteZeroBoundaryChainCharge cutoff path := by
  unfold quittingFiniteZeroBoundaryChainCharge
  have hzero : quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path) 0 =
      quittingRootOfSimplex predecessor.2 := by
    unfold quittingFiniteNashBellmanPathRoots
    rw [dif_pos (by omega)]
    rfl
  have hshift : (∑ time ∈ Finset.range cutoff,
        quittingRootAbsorptionMass
          (quittingFiniteNashBellmanPathRoots (cutoff + 1)
            (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
            (time + 1))) =
      ∑ time ∈ Finset.range cutoff,
        quittingRootAbsorptionMass
          (quittingFiniteNashBellmanPathRoots cutoff path time) := by
    apply Finset.sum_congr rfl
    intro time htime
    rw [quittingFiniteNashBellmanPathRoots_prependPoint_shift]
  conv_lhs => rw [Finset.sum_range_succ']
  rw [hzero, hshift]
  ring

/-- Near-maximal chronology leaves less than `ε` absorption capacity for
every literal exact predecessor of its initial state. -/
theorem exists_nearMaximal_zeroBoundaryChronology
    (regime : QuittingCounterexampleRegime reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      quittingZeroBoundaryChronologyCapacity reward - ε <
        quittingFiniteZeroBoundaryChainCharge cutoff path ∧
      ∀ predecessor : QuittingNashBellmanPoint ι,
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) →
        IsQuittingNashBellmanEdge reward predecessor (path 0) →
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  have hbounded :=
    quittingZeroBoundaryChronologyCharges_bddAbove regime hpunishment
  have hnonempty : (quittingZeroBoundaryChronologyCharges reward).Nonempty :=
    quittingZeroBoundaryChronologyCharges_nonempty
  have hlt : quittingZeroBoundaryChronologyCapacity reward - ε <
      quittingZeroBoundaryChronologyCapacity reward := by
    exact sub_lt_self _ hε
  obtain ⟨charge, ⟨cutoff, path, hpath, rfl⟩, hnear⟩ :=
    (lt_csSup_iff hbounded hnonempty).mp hlt
  refine ⟨cutoff, path, hpath, hnear, ?_⟩
  intro predecessor hpredecessor hedge
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  have hupper :=
    quittingFiniteZeroBoundaryChainCharge_le_chronologyCapacity
      regime hpunishment (cutoff + 1) extended hextended
  rw [quittingFiniteZeroBoundaryChainCharge_prependPoint] at hupper
  linarith

/-- The terminal gap is retained by every admissible zero-boundary chain,
not only by the selected minimizer. -/
theorem terminalGap_le_zeroBoundaryChainAggregateDebt
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    regime.terminalGap ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path := by
  exact (regime.terminalGap_le_finiteMinMaxDynamicDebt cutoff).trans
    ((quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
        reward cutoff path hpath).trans
      (quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward cutoff path hpath))

/-- **State-preserving near-maximal chronology.**  One finite exact-D chain
simultaneously carries aggregate initial debt at least the regime gap and has
less than `ε` absorption available at every exact bounded prepend. -/
theorem exists_nearMaximal_positiveDebt_zeroBoundaryChronology
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      regime.terminalGap ≤
        quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path ∧
      quittingZeroBoundaryChronologyCapacity reward - ε <
        quittingFiniteZeroBoundaryChainCharge cutoff path ∧
      ∀ predecessor : QuittingNashBellmanPoint ι,
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) →
        IsQuittingNashBellmanEdge reward predecessor (path 0) →
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  obtain ⟨cutoff, path, hpath, hnear, hprepend⟩ :=
    exists_nearMaximal_zeroBoundaryChronology regime hpunishment hε
  exact ⟨cutoff, path, hpath,
    terminalGap_le_zeroBoundaryChainAggregateDebt regime cutoff path hpath,
    hnear, hprepend⟩

/-- The compact Nash--Bellman predecessor correspondence turns the universal
small-prepend conclusion into one actual state-matched edge.  Its successor
is the positive-debt initial point of the same near-maximal chronology. -/
theorem exists_nearMaximal_positiveDebtChronology_smallPredecessor
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      ∃ predecessor : QuittingNashBellmanPoint ι,
        path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
        regime.terminalGap ≤
          quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path ∧
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
        IsQuittingNashBellmanEdge reward predecessor (path 0) ∧
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  obtain ⟨cutoff, path, hpath, hdebt, _hnear, hsmall⟩ :=
    exists_nearMaximal_positiveDebt_zeroBoundaryChronology
      regime hpunishment hε
  obtain ⟨predecessor, hpredecessor, hedge⟩ :=
    exists_quittingNashBellmanPredecessor reward
      (abs_reward_le_quittingRewardBound reward) (path 0) (hpath.1 0)
  exact ⟨cutoff, path, predecessor, hpath, hdebt, hpredecessor, hedge,
    hsmall predecessor hpredecessor hedge⟩

/-- One exact dynamic-debt edge inherits the universal one-stage value-drift
bound, with the same literal joint absorption scale. -/
theorem abs_value_sub_le_two_mul_absorptionMass_of_dynamicDebtEdge
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    |successor.1.1 who - current.1.1 who| ≤
      2 * quittingRewardBound reward *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := by
  rw [congrFun hedge.1.1 who]
  simpa [abs_sub_comm] using
    (abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward successor.1.1 (quittingRootOfSimplex current.1.2) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
      (abs_le.mpr ⟨hsuccessor.1.1 who, hsuccessor.1.2 who⟩))

/-- On an active edge, prescribed-value drift normalized by joint absorption
stays in the fixed reward box. -/
theorem abs_normalized_valueDrift_le_two_rewardBound_of_dynamicDebtEdge
    (current successor : QuittingDebtPoint ι)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hactive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2))
    (who : ι) :
    |(successor.1.1 who - current.1.1 who) /
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2)| ≤
      2 * quittingRewardBound reward := by
  rw [abs_div, abs_of_pos hactive]
  apply (div_le_iff₀ hactive).2
  simpa [mul_assoc] using
    (abs_value_sub_le_two_mul_absorptionMass_of_dynamicDebtEdge
      current successor hsuccessor hedge who)

/-- Exact debt loss is also Lipschitz in literal absorption time.  The debt
coordinate therefore admits the same charge-time compactification as payoff. -/
theorem dynamicDebtCoordinateLoss_le_cap_mul_absorptionMass
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (who : ι) :
    quittingDynamicDebtCoordinateLoss current successor who ≤
      quittingPositiveSingletonDebtCap reward who *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := by
  have hconservation :=
    quittingDynamicDebt_eq_continueMass_mul_add_seam
      current successor hedge hsuccessor.2.1 who
  have hseamNonneg := quittingDynamicDebtSeam_nonneg current hcurrent who
  have habsorptionNonneg : 0 ≤ quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) := by
    unfold quittingRootAbsorptionMass
    exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
  have hloss : quittingDynamicDebtCoordinateLoss current successor who =
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who -
        quittingDynamicDebtSeam current who := by
    unfold quittingDynamicDebtCoordinateLoss quittingRootAbsorptionMass
    rw [hconservation]
    ring
  rw [hloss]
  calc
    quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who -
        quittingDynamicDebtSeam current who ≤
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) * successor.2 who :=
        sub_le_self _ hseamNonneg
    _ ≤ quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) *
        quittingPositiveSingletonDebtCap reward who :=
      mul_le_mul_of_nonneg_left (hsuccessor.2.2 who) habsorptionNonneg
    _ = quittingPositiveSingletonDebtCap reward who *
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) := mul_comm _ _

/-- On an active edge, normalized debt loss lies in its singleton-cap box. -/
theorem normalized_dynamicDebtCoordinateLoss_mem_Icc
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hactive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2))
    (who : ι) :
    quittingDynamicDebtCoordinateLoss current successor who /
        quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) ∈
      Set.Icc 0 (quittingPositiveSingletonDebtCap reward who) := by
  have hlossNonneg := quittingDynamicDebtCoordinateLoss_nonneg
    reward current successor hsuccessor.2.1 hedge who
  constructor
  · exact div_nonneg hlossNonneg hactive.le
  · apply (div_le_iff₀ hactive).2
    simpa [mul_comm] using
      (dynamicDebtCoordinateLoss_le_cap_mul_absorptionMass
        current successor hcurrent hsuccessor hedge who)

omit [DecidableEq ι] in
/-- A marginal Quit hazard normalized by positive joint absorption lies in
the unit interval. -/
theorem normalized_quitProbability_mem_Icc
    (root : ι → PMF Bool)
    (hactive : 0 < quittingRootAbsorptionMass root) (who : ι) :
    (root who true).toReal / quittingRootAbsorptionMass root ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg ENNReal.toReal_nonneg hactive.le
  · exact (div_le_one hactive).2
      (quitProbability_le_quittingRootAbsorptionMass root who)

/-- **Projective one-edge readout of chronology near-maximality.**  At every
scale there is a genuine state-matched exact dynamic-debt edge whose successor
retains aggregate debt at least the terminal gap and whose absorption is below
that scale.  Either the edge is already on the zero-absorption face, or its
normalized value drift is uniformly bounded coordinatewise. -/
theorem exists_nearMaximal_positiveDebt_smallDynamicDebtEdge
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ current successor : QuittingDebtPoint ι,
      current ∈ quittingDebtBox reward ∧
      successor ∈ quittingDebtBox reward ∧
      IsQuittingDynamicDebtEdge reward current successor ∧
      regime.terminalGap ≤ ∑ who, successor.2 who ∧
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) < ε ∧
      (quittingRootAbsorptionMass
            (quittingRootOfSimplex current.1.2) = 0 ∨
        (0 < quittingRootAbsorptionMass
              (quittingRootOfSimplex current.1.2) ∧
          ∀ who,
            |(successor.1.1 who - current.1.1 who) /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2)| ≤
              2 * quittingRewardBound reward)) := by
  obtain ⟨cutoff, path, predecessor, hpath, hdebt, hpredecessor, hedge,
      hsmall⟩ :=
    exists_nearMaximal_positiveDebtChronology_smallPredecessor
      regime hpunishment hε
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (cutoff + 1) extended 0
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (cutoff + 1) extended 1
  have hcurrent : current ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (cutoff + 1) extended hextended 0
  have hsuccessor : successor ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (cutoff + 1) extended hextended 1
  have hdynamic : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward (cutoff + 1) extended hextended 0 (by omega)
  have hsuccessorDebt :
      regime.terminalGap ≤ ∑ who, successor.2 who := by
    calc
      regime.terminalGap ≤
          quittingFiniteNashBellmanPathAggregateDynamicDebt
            reward cutoff path := hdebt
      _ = ∑ who, successor.2 who := by
        unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
        apply Finset.sum_congr rfl
        intro who _
        change quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who 0 =
          quittingFiniteNashBellmanPathDynamicDebt
            reward (cutoff + 1) extended who 1
        exact (quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
          reward cutoff predecessor path who).symm
  have hcurrentRoot : quittingRootOfSimplex current.1.2 =
      quittingRootOfSimplex predecessor.2 := by
    unfold current quittingFiniteNashBellmanPathDynamicDebtPoint
    rw [dif_pos (by omega)]
    rfl
  have hsmallCurrent : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) < ε := by
    rw [hcurrentRoot]
    exact hsmall
  refine ⟨current, successor, hcurrent, hsuccessor, hdynamic,
    hsuccessorDebt, hsmallCurrent, ?_⟩
  by_cases hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0
  · exact Or.inl hzero
  · have hactive : 0 < quittingRootAbsorptionMass
        (quittingRootOfSimplex current.1.2) :=
      lt_of_le_of_ne (by
        unfold quittingRootAbsorptionMass
        exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _))
        (Ne.symm hzero)
    exact Or.inr ⟨hactive, fun who ↦
      abs_normalized_valueDrift_le_two_rewardBound_of_dynamicDebtEdge
        current successor hsuccessor hdynamic hactive who⟩

/-- **Charge-time compact edge readout.**  The same state-matched edge has
uniformly bounded normalized payoff drift, debt loss, and marginal Quit
hazards whenever its absorption is positive.  These are exactly the bounded
coordinates available to a charge-time compactness argument. -/
theorem exists_nearMaximal_positiveDebt_chargeTimeCompactEdge
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι]
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ current successor : QuittingDebtPoint ι,
      current ∈ quittingDebtBox reward ∧
      successor ∈ quittingDebtBox reward ∧
      IsQuittingDynamicDebtEdge reward current successor ∧
      regime.terminalGap ≤ ∑ who, successor.2 who ∧
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) < ε ∧
      (quittingRootAbsorptionMass
            (quittingRootOfSimplex current.1.2) = 0 ∨
        (0 < quittingRootAbsorptionMass
              (quittingRootOfSimplex current.1.2) ∧
          (∀ who,
            |(successor.1.1 who - current.1.1 who) /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2)| ≤
              2 * quittingRewardBound reward) ∧
          (∀ who,
            quittingDynamicDebtCoordinateLoss current successor who /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2) ∈
              Set.Icc 0 (quittingPositiveSingletonDebtCap reward who)) ∧
          (∀ who,
            ((quittingRootOfSimplex current.1.2) who true).toReal /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2) ∈
              Set.Icc (0 : ℝ) 1))) := by
  obtain ⟨current, successor, hcurrent, hsuccessor, hedge, hdebt,
      hsmall, hactiveOrZero⟩ :=
    exists_nearMaximal_positiveDebt_smallDynamicDebtEdge
      regime hpunishment hε
  refine ⟨current, successor, hcurrent, hsuccessor, hedge, hdebt,
    hsmall, ?_⟩
  rcases hactiveOrZero with hzero | ⟨hactive, hvalue⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨hactive, hvalue, ?_, ?_⟩
    · exact fun who ↦ normalized_dynamicDebtCoordinateLoss_mem_Icc
        current successor hcurrent hsuccessor hedge hactive who
    · exact fun who ↦ normalized_quitProbability_mem_Icc
        (quittingRootOfSimplex current.1.2) hactive who

/-! ## Exact diagnosis of the projective zero-scale limit -/

/-- At an all-Continue current state, the exact augmented edge imposes no
condition on the stored root of the successor.  Payoff and debt can stay
fixed while that successor root is chosen arbitrarily.  Thus the root
coordinate is a control for the next edge, not a state coordinate whose
increment is controlled by the current edge's absorption mass. -/
theorem allContinue_dynamicDebtEdge_ignores_successorRoot
    (value debt : Payoff ι) (successorRoot : QuittingRootSimplex ι)
    (hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ value who)
    (hdebt : 0 ≤ debt) :
    IsQuittingDynamicDebtEdge reward
      (((value, quittingAllContinueSimplexRoot), debt) :
        QuittingDebtPoint ι)
      (((value, successorRoot), debt) : QuittingDebtPoint ι) := by
  have hnash : IsεQuittingRootNash reward value 0
      (quittingAllContinueRoot : ι → PMF Bool) :=
    quittingAllContinueRoot_isZeroNash_of_singleton_le reward value hsolo
  have hbellman : IsQuittingNashBellmanEdge reward
      (value, quittingAllContinueSimplexRoot) (value, successorRoot) := by
    constructor
    · change value = quittingRootSuccessorPayoff reward value
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        quittingRootSuccessorPayoff_allContinueRoot_eq]
    · change IsεQuittingRootEndpointNash reward value 0
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
      exact hnash
  refine ⟨hbellman, fun who ↦ ?_⟩
  have hopponent : quittingDebtOpponentContinueMass
      (((value, quittingAllContinueSimplexRoot), debt) :
        QuittingDebtPoint ι) who = 1 := by
    rw [quittingDebtOpponentContinueMass_eq_stationary,
      quittingRootOfSimplex_allContinueSimplexRoot]
    rw [show Function.update quittingAllContinueRoot who (PMF.pure false) =
        quittingAllContinueRoot by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingAllContinueRoot]
      · simp [Function.update_of_ne hplayer, quittingAllContinueRoot]]
    have habs := quittingRootAbsorptionMass_allContinueRoot (ι := ι)
    unfold quittingRootAbsorptionMass at habs
    linarith
  unfold quittingDynamicDebtUpdate
  rw [quittingRootOfSimplex_allContinueSimplexRoot,
    quittingRootQuitPayoff_allContinueRoot,
    quittingRootContinuePayoff_allContinueRoot, hopponent]
  rw [max_eq_right]
  · ring
  · apply (hsolo who).trans
    apply le_add_of_nonneg_right
    simpa using hdebt who

/-- A zero-absorption exact dynamic-debt edge preserves both payoff and debt;
its current root is all-Continue.  Thus vanishing absorption does not identify
the common payoff with terminal semantics. -/
theorem zeroAbsorption_dynamicDebtEdge_plateau
    (current successor : QuittingDebtPoint ι)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0) :
    current.1.1 = successor.1.1 ∧
      current.2 = successor.2 ∧
      quittingRootOfSimplex current.1.2 = quittingAllContinueRoot := by
  have hmass : quittingStationaryContinueMass
      (quittingRootOfSimplex current.1.2) = 1 := by
    unfold quittingRootAbsorptionMass at hzero
    linarith
  have hroot : quittingRootOfSimplex current.1.2 =
      quittingAllContinueRoot :=
    eq_quittingAllContinueRoot_of_continueMass_eq_one _ hmass
  have hvalue : current.1.1 = successor.1.1 := by
    rw [hedge.1.1, hroot]
    exact quittingRootSuccessorPayoff_allContinueRoot_eq reward successor.1.1
  have hopponent (who : ι) :
      quittingDebtOpponentContinueMass current who = 1 := by
    rw [quittingDebtOpponentContinueMass_eq_stationary, hroot]
    rw [show Function.update quittingAllContinueRoot who (PMF.pure false) =
        quittingAllContinueRoot by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingAllContinueRoot]
      · simp [Function.update_of_ne hplayer, quittingAllContinueRoot]]
    have habs := quittingRootAbsorptionMass_allContinueRoot (ι := ι)
    unfold quittingRootAbsorptionMass at habs
    linarith
  have hdebt : current.2 = successor.2 := by
    funext who
    have hcontinue : 0 <
        (quittingRootOfSimplex current.1.2 who false).toReal := by
      rw [hroot]
      simp [quittingAllContinueRoot]
    have hpropagate :=
      quittingDynamicDebt_eq_opponentContinueMass_mul_of_continue_pos
        reward current successor hedge hsuccessorDebt who hcontinue
    rw [hopponent, one_mul] at hpropagate
    exact hpropagate
  exact ⟨hvalue, hdebt, hroot⟩

/-- Two consecutive zero-absorption edges collapse to a literal positive-debt
all-Continue self-loop.  This is exactly the phantom plateau obtained from a
two-scale compact limit; no terminal payoff is produced. -/
theorem two_zeroAbsorption_dynamicDebtEdges_collapse_to_plateau
    (first second third : QuittingDebtPoint ι)
    (hsecondDebt : 0 ≤ second.2) (hthirdDebt : 0 ≤ third.2)
    (hfirstEdge : IsQuittingDynamicDebtEdge reward first second)
    (hsecondEdge : IsQuittingDynamicDebtEdge reward second third)
    (hfirstZero : quittingRootAbsorptionMass
      (quittingRootOfSimplex first.1.2) = 0)
    (hsecondZero : quittingRootAbsorptionMass
      (quittingRootOfSimplex second.1.2) = 0)
    {gap : ℝ} (hgap : gap ≤ ∑ who, third.2 who) :
    first = second ∧
      gap ≤ ∑ who, second.2 who ∧
      quittingRootOfSimplex first.1.2 = quittingAllContinueRoot := by
  obtain ⟨hvalueFirst, hdebtFirst, hrootFirst⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      first second hsecondDebt hfirstEdge hfirstZero
  obtain ⟨_valueSecond, hdebtSecond, hrootSecond⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      second third hthirdDebt hsecondEdge hsecondZero
  have hsimplex : first.1.2 = second.1.2 := by
    funext who
    apply (stdSimplexEquiv (α := Bool)).symm.injective
    exact congrFun (hrootFirst.trans hrootSecond.symm) who
  have hstate : first = second := by
    apply Prod.ext
    · exact Prod.ext hvalueFirst hsimplex
    · exact hdebtFirst
  refine ⟨hstate, ?_, hrootFirst⟩
  rw [hdebtSecond]
  exact hgap

end GameTheory
