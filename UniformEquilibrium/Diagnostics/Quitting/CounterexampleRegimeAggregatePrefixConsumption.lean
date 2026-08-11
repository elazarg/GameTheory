/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneAttachmentRepair
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCalibration
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation

/-!
# Aggregate prefix consumption of a terminal obstruction

A counterexample regime's literal terminal gap floors the behavioral-tail
repair value of the complete canonical aggregate-minimizing prefix.  The
quantitative terminal-anchor machinery then charges the same gap to a marked
packet at that cutoff.  This implication is unconditional and does not alter
the prefix or identify a stored boundary annotation with an actual tail.

The final theorem records the remaining replacement gate precisely.  If an
elementary capped continuation behind the calibrated prefix is quantitatively
controlled by the next optimized-objective drop plus the charge of an actual
reachable Nash--Bellman predecessor, then half of the terminal gap appears in
one of those two terms.  Current APIs provide neither the required attachment
of the selected zero-boundary state to the punishment-floor reachable
relation nor the displayed objective comparison; changing a behavioral tail
alone does not provide either fact.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

open QuittingAggregateCalibratedTerminalAnchor

/-- The literal regime gap floors the all-tail repair value of the complete
canonical aggregate exact-`D` minimizer at every positive cutoff. -/
theorem terminalGap_le_canonicalAggregateFullPrefixRepairValue
    (regime : QuittingCounterexampleRegime reward) (last : ℕ) :
    regime.terminalGap ≤
      QuittingAggregateCalibratedTerminalAnchor.canonicalAggregateFullPrefixRepairValue
        reward last := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward (last + 1)
  have hfloor := terminalExploitabilityGap_le_behavioralTailRepairValue
    reward (quittingFiniteNashBellmanPathRoots (last + 1) path)
      (last + 1) (by omega) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      regime.terminalExploitability
  simpa [path,
    QuittingAggregateCalibratedTerminalAnchor.canonicalAggregateFullPrefixRepairValue,
    QuittingAggregateCalibratedTerminalAnchor.canonicalAggregateFullPrefixHolonomy]
    using hfloor

/-- The fixed-prefix repair floor gives a direct quantitative sandwich from
the global terminal gap to the optimized aggregate exact-`D` objective. -/
theorem terminalGap_le_repairValue_le_minAggregate
    (regime : QuittingCounterexampleRegime reward) (last : ℕ) :
    regime.terminalGap ≤
        QuittingAggregateCalibratedTerminalAnchor.canonicalAggregateFullPrefixRepairValue
          reward last ∧
      QuittingAggregateCalibratedTerminalAnchor.canonicalAggregateFullPrefixRepairValue
          reward last ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (last + 1) := by
  exact ⟨regime.terminalGap_le_canonicalAggregateFullPrefixRepairValue last,
    canonicalAggregateFullPrefixRepairValue_le_minAggregate reward last⟩

/-- At every cutoff the regime's literal terminal gap is carried by a marked
packet of the canonical aggregate minimizer.  This is a calibrated packet
charge, not yet an edge in the punishment-floor reachable relation. -/
theorem exists_aggregateAnchor_terminalGap_le_packetCharge
    (regime : QuittingCounterexampleRegime reward) (last : ℕ) :
    ∃ anchor : QuittingAggregateCalibratedTerminalAnchor reward,
      anchor.last = last ∧
        regime.terminalGap ≤
          2 * quittingRewardBound reward * (Fintype.card ι : ℝ) *
            (Fintype.card (ι → Bool) : ℝ) * anchor.packetMass := by
  exact exists_packetCharge_of_pos_le_canonicalFullPrefixRepairValue
      reward (quittingRewardBound reward) regime.terminalGap last
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      regime.terminalGap_pos
      (regime.terminalGap_le_canonicalAggregateFullPrefixRepairValue last)

/-! ## The immediate Never cap -/

/-- Attaching Never immediately after the complete calibrated prefix reads
exactly the maximum playerwise dynamic debt.  This is the one elementary cap
whose boundary pair is already the zero-boundary pair used by exact-`D`.

A compressed Never cap with a positive internal cutoff does not satisfy this
identity: it retains the supplied behavioral word before reaching Never. -/
theorem immediateNever_terminalExploitability_eq_maxDynamicDebt
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (anchor.last + 1) anchor.path := by
  rw [← quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
    reward anchor.roots
      (quittingElementaryCapRoots
        (.never : QuittingElementaryTailCap ι))
      (anchor.last + 1) (by omega) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)]
  simpa [QuittingAggregateCalibratedTerminalAnchor.roots] using
    (fullPrefix_behavioralTailGain_elementaryNever_eq_maxDynamicDebt
      reward anchor.last anchor.path anchor.path_mem)

/-- For the immediate Never cap, the generic objective/charge comparison
reduces to a single endpoint statement: the next optimized residual debt is
paid by the legal edge charge. -/
theorem immediateNever_terminalExploitability_le_drop_add_charge
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (chargeScale : ℝ)
    (hendpoint :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) ≤
        chargeScale * edge.toBoxEdge.absorptionCharge) :
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 1) -
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) +
        chargeScale * edge.toBoxEdge.absorptionCharge := by
  calc
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (anchor.last + 1) anchor.path :=
      immediateNever_terminalExploitability_eq_maxDynamicDebt anchor
    _ ≤ quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 1) anchor.path :=
      quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward (anchor.last + 1) anchor.path anchor.path_mem
    _ = quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (anchor.last + 1) := by
      rw [anchor.path_eq_minimizer]
      rfl
    _ ≤ quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 1) -
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) +
        chargeScale * edge.toBoxEdge.absorptionCharge := by
      linarith

/-- **Conditional elementary-cap consumption gate.**

Suppose the initial state of an aggregate-calibrated prefix is literally the
tail of a reachable punishment-floor predecessor edge.  If the co-realized
terminal exploitability after an elementary cap is bounded by the next
aggregate-objective drop plus a scaled charge of that edge, then at least half
the regime gap is paid by the objective drop or by the legal predecessor
charge.

The `hcomparison` inequality is the minimal quantitative seam not supplied by
tail compression or calibration.  Calibration only says that a genuine
predecessor produces coordinate losses bounded by the optimized-objective
drop; it does not compare a changed tail's terminal exploitability with those
losses or with the predecessor's absorption mass. -/
theorem elementaryCap_consumed_by_minAggregateDrop_or_reachableCharge
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0)
    (tail : ℕ → ι → PMF Bool) (cap : QuittingElementaryTailCap ι)
    (capCutoff : ℕ) (chargeScale : ℝ) (hchargeScale : 0 ≤ chargeScale)
    (hcomparison :
      quittingTerminalExploitability reward
          (quittingPhaseSwitchProfile reward anchor.roots
            (quittingElementaryTailRoots tail capCutoff cap)
            (anchor.last + 1)) ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 1) -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 2) +
          chargeScale * edge.toBoxEdge.absorptionCharge) :
    regime.terminalGap / 2 ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 1) -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 2) ∨
      regime.terminalGap / 2 ≤
        chargeScale * edge.toBoxEdge.absorptionCharge := by
  have hedgeAnchor : IsQuittingNashBellmanEdge reward edge.current.1.1
      (anchor.path 0) := by
    rw [← htail]
    exact edge.exactEdge
  have hedgeMinimizer : IsQuittingNashBellmanEdge reward edge.current.1.1
      (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
        reward (anchor.last + 1) 0) := by
    rw [← anchor.path_eq_minimizer]
    exact hedgeAnchor
  have hcalibrated :=
    quittingFiniteDynamicDebt_sumMinimizer_prependPoint_calibrated
      reward (anchor.last + 1) edge.current.1.1 edge.current.1.2
      hedgeMinimizer
  dsimp only at hcalibrated
  have hdropNonneg :
      0 ≤ quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 1) -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 2) := by
    exact hcalibrated.1.trans hcalibrated.2
  have hchargeNonneg : 0 ≤
      chargeScale * edge.toBoxEdge.absorptionCharge :=
    mul_nonneg hchargeScale edge.toBoxEdge.absorptionCharge_nonneg
  have hgap := terminalExploitabilityGap_le_quittingTerminalExploitability
    reward (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      regime.terminalExploitability
      (quittingPhaseSwitchProfile reward anchor.roots
        (quittingElementaryTailRoots tail capCutoff cap)
        (anchor.last + 1))
  by_cases hdrop : regime.terminalGap / 2 ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 1) -
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2)
  · exact Or.inl hdrop
  · right
    linarith

/-! ## What joint charge actually controls -/

omit [Nonempty ι] in
/-- Exact one-edge conservation for a genuinely prepended calibrated chain.
The residual aggregate debt is bounded by the joint-Continue transport of
the old aggregate debt plus a diagonal seam paid by joint absorption.

This is the sharp universal replacement for a false bound of residual debt
by absorption alone.  The first term uses joint Continue mass and cannot be
discarded merely because the edge is reachable. -/
theorem prependResidual_le_jointContinue_mul_anchorDebt_add_charge
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path +
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        edge.toBoxEdge.absorptionCharge := by
  have hedgeAnchor : IsQuittingNashBellmanEdge reward edge.current.1.1
      (anchor.path 0) := by
    rw [← htail]
    exact edge.exactEdge
  let extended := quittingFiniteNashBellmanPathPrependPoint
    (anchor.last + 1) edge.current.1.1 anchor.path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet
        reward (anchor.last + 2) := by
    simpa [extended, Nat.add_assoc] using
      (quittingFiniteNashBellmanPathPrependPoint_mem
        reward (anchor.last + 1) anchor.path anchor.path_mem
        edge.current.1.1 edge.current.1.2 hedgeAnchor)
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (anchor.last + 2) extended 0
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (anchor.last + 2) extended 1
  have hcurrentBox : current ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (anchor.last + 2) extended hextended 0
  have hsuccessorBox : successor ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (anchor.last + 2) extended hextended 1
  have hdebtEdge : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward (anchor.last + 2) extended hextended 0 (by omega)
  have hcurrentPoint : current.1 = edge.current.1.1 := by
    simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint, extended]
  have hcurrentDebt (who : ι) : current.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 0 := by
    simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint]
  have hsuccessorDebt (who : ι) : successor.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 1) anchor.path who 0 := by
    rw [show successor.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 1 by
          simp [successor, quittingFiniteNashBellmanPathDynamicDebtPoint]]
    simpa [extended, Nat.add_assoc] using
      (quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
        reward (anchor.last + 1) edge.current.1.1 anchor.path who)
  have hconservation (who : ι) :
      current.2 who =
        quittingStationaryContinueMass
            (quittingRootOfSimplex edge.current.1.1.2) * successor.2 who +
          quittingDynamicDebtSeam current who := by
    have h := quittingDynamicDebt_eq_continueMass_mul_add_seam
      current successor hdebtEdge hsuccessorBox.2.1 who
    rwa [hcurrentPoint] at h
  have hseam (who : ι) :
      quittingDynamicDebtSeam current who ≤
        quittingRewardBound reward * edge.toBoxEdge.absorptionCharge := by
    have hraw := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      current hcurrentBox who
    have hcap : quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
      (le_abs_self _).trans
        (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
    have hcharge0 : 0 ≤ edge.toBoxEdge.absorptionCharge :=
      edge.toBoxEdge.absorptionCharge_nonneg
    rw [hcurrentPoint] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_right hcap hcharge0)
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  rw [show (∑ who,
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 0) =
      ∑ who, current.2 who by
        apply Finset.sum_congr rfl
        intro who _
        exact (hcurrentDebt who).symm]
  calc
    (∑ who, current.2 who) =
        ∑ who,
          (quittingStationaryContinueMass
              (quittingRootOfSimplex edge.current.1.1.2) * successor.2 who +
            quittingDynamicDebtSeam current who) := by
      apply Finset.sum_congr rfl
      intro who _
      exact hconservation who
    _ = quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who, successor.2 who) +
        ∑ who, quittingDynamicDebtSeam current who := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who, successor.2 who) +
        ∑ _who : ι,
          (quittingRewardBound reward * edge.toBoxEdge.absorptionCharge) := by
      have hs : (∑ who, quittingDynamicDebtSeam current who) ≤
          ∑ _who : ι,
            (quittingRewardBound reward *
              edge.toBoxEdge.absorptionCharge) := by
        apply Finset.sum_le_sum
        intro who _
        exact hseam who
      exact add_le_add_right hs _
    _ = quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who,
            quittingFiniteNashBellmanPathDynamicDebt
              reward (anchor.last + 1) anchor.path who 0) +
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := by
      rw [show (∑ who, successor.2 who) =
          ∑ who, quittingFiniteNashBellmanPathDynamicDebt
            reward (anchor.last + 1) anchor.path who 0 by
        apply Finset.sum_congr rfl
        intro who _
        exact hsuccessorDebt who]
      simp [mul_assoc]

omit [Nonempty ι] in
/-- The exact extra observable needed to turn conservation into a pure charge
bound is the joint-Continue-carried old debt.  If that surviving potential is
itself charged at scale `carriedScale`, the whole prepended residual is
charged at scale `carriedScale + card * rewardBound`. -/
theorem prependResidual_le_charge_of_carriedDebt_le_charge
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0)
    (carriedScale : ℝ)
    (hcarried :
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path ≤
        carriedScale * edge.toBoxEdge.absorptionCharge) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      (carriedScale +
          (Fintype.card ι : ℝ) * quittingRewardBound reward) *
        edge.toBoxEdge.absorptionCharge := by
  have hconservation :=
    prependResidual_le_jointContinue_mul_anchorDebt_add_charge
      anchor edge htail
  calc
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path +
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        edge.toBoxEdge.absorptionCharge := hconservation
    _ ≤ carriedScale * edge.toBoxEdge.absorptionCharge +
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := add_le_add_left hcarried _
    _ = (carriedScale +
          (Fintype.card ι : ℝ) * quittingRewardBound reward) *
        edge.toBoxEdge.absorptionCharge := by ring

/-- The immediate Never branch is consumed once the residual aggregate debt
of the genuinely prepended chain is charged to its new root.  Unlike the
generic gate, the hypothesis here is a concrete exact-`D` endpoint inequality
on a chain that the existing prepend constructor proves admissible.

No current theorem derives `hresidual` from absorption mass alone.  In
particular, playerwise dynamic debt is transported by deleted-player survival,
whereas the charged relation records joint absorption. -/
theorem immediateNever_consumed_of_prependResidual_le_charge
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0)
    (chargeScale : ℝ) (hchargeScale : 0 ≤ chargeScale)
    (hresidual :
      quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 2)
          (quittingFiniteNashBellmanPathPrependPoint
            (anchor.last + 1) edge.current.1.1 anchor.path) ≤
        chargeScale * edge.toBoxEdge.absorptionCharge) :
    regime.terminalGap / 2 ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 1) -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 2) ∨
      regime.terminalGap / 2 ≤
        chargeScale * edge.toBoxEdge.absorptionCharge := by
  have hedgeAnchor : IsQuittingNashBellmanEdge reward edge.current.1.1
      (anchor.path 0) := by
    rw [← htail]
    exact edge.exactEdge
  let extended := quittingFiniteNashBellmanPathPrependPoint
    (anchor.last + 1) edge.current.1.1 anchor.path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet
        reward (anchor.last + 2) := by
    simpa [extended, Nat.add_assoc] using
      (quittingFiniteNashBellmanPathPrependPoint_mem
        reward (anchor.last + 1) anchor.path anchor.path_mem
        edge.current.1.1 edge.current.1.2 hedgeAnchor)
  have hnext :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) ≤
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 2) extended := by
    exact quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le
      reward (anchor.last + 2) extended hextended
  have hendpoint :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) ≤
        chargeScale * edge.toBoxEdge.absorptionCharge := by
    exact hnext.trans (by simpa [extended] using hresidual)
  have hcomparison :=
    immediateNever_terminalExploitability_le_drop_add_charge
      anchor edge chargeScale hendpoint
  apply regime.elementaryCap_consumed_by_minAggregateDrop_or_reachableCharge
    anchor edge htail (fun _ => quittingAllContinueRoot) (.never) 0
      chargeScale hchargeScale
  have hroots :
      quittingElementaryTailRoots (fun _ => quittingAllContinueRoot) 0
          (.never : QuittingElementaryTailCap ι) =
        quittingElementaryCapRoots
          (.never : QuittingElementaryTailCap ι) := by
    funext time
    simpa using
      (quittingElementaryTailRoots_add
        (fun _ => quittingAllContinueRoot) 0 time
          (.never : QuittingElementaryTailCap ι))
  rw [hroots]
  exact hcomparison

/-- Natural chargeable-potential form of the immediate Never consumer.  The
only extra premise beyond literal reachable attachment is a bound on the old
debt that survives the new root's joint-Continue event. -/
theorem immediateNever_consumed_of_carriedDebt_le_charge
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0)
    (carriedScale : ℝ) (hcarriedScale : 0 ≤ carriedScale)
    (hcarried :
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path ≤
        carriedScale * edge.toBoxEdge.absorptionCharge) :
    regime.terminalGap / 2 ≤
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 1) -
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
            reward (anchor.last + 2) ∨
      regime.terminalGap / 2 ≤
        (carriedScale +
            (Fintype.card ι : ℝ) * quittingRewardBound reward) *
          edge.toBoxEdge.absorptionCharge := by
  have hscale : 0 ≤ carriedScale +
      (Fintype.card ι : ℝ) * quittingRewardBound reward :=
    add_nonneg hcarriedScale
      (mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward))
  apply regime.immediateNever_consumed_of_prependResidual_le_charge
    anchor edge htail
      (carriedScale +
        (Fintype.card ι : ℝ) * quittingRewardBound reward) hscale
  exact prependResidual_le_charge_of_carriedDebt_le_charge
    anchor edge htail carriedScale hcarried

end QuittingCounterexampleRegime

end GameTheory
