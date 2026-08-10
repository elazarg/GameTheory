/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneAttachmentRepair
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCalibration

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

set_option autoImplicit false

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

end QuittingCounterexampleRegime

end GameTheory
