/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneTangentReadout
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailGainDensity
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation

/-!
# Terminal repair alternative for a period-one tangent attachment

The period-one readout identifies a profitable stationary refusal diagnostic,
but attaching the selected root to its actual suffix introduces two boundary
questions: whether the suffix realizes the stored annotation, and whether its
literal `Never` payoff is large enough.  Neither follows from pointwise
all-Continue convergence.

The behavioral-tail machinery offers a different, fully co-realized output.
For every actual suffix it keeps the suffix's genuine prescribed payoff and
its genuine all-behavior envelope together.  A uniform terminal
exploitability gap therefore becomes a lower bound on the fixed-prefix repair
value, and elementary tail compression returns the obstruction through one
of the three canonical caps.  This does not identify the obstructing player
with the active tangent owner, but it is directly consumable by the terminal
prefix pipeline.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A uniform terminal exploitability gap is a lower bound on the literal
maximum positive terminal exploitability of every profile. -/
theorem terminalExploitabilityGap_le_quittingTerminalExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile) :
    gap ≤ quittingTerminalExploitability reward profile := by
  obtain ⟨who, deviation, hdeviation⟩ := hexploit profile
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation hM hreward
  have hcoordinate : gap ≤
      quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who := by
    linarith
  unfold quittingTerminalExploitability
  exact (hcoordinate.trans (le_max_right 0 _)).trans
    (QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun player ↦ max 0
        (quittingContinuationBestResponseValue reward profile player -
          quittingTerminalPayoff reward profile player)) who)

/-- A terminal exploitability gap floors the all-tail repair value of every
positive finite prefix.  No stored annotation occurs: both boundary
coordinates are supplied by the same actual suffix. -/
theorem terminalExploitabilityGap_le_behavioralTailRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {M gap : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap ≤ QuittingBoundaryHolonomy.behavioralTailRepairValue reward
      (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) := by
  rw [behavioralTailRepairValue_eq_sInf_phaseSwitch_terminalExploitability
    reward plan switch hswitch hM hreward]
  apply le_csInf (Set.range_nonempty _)
  rintro value ⟨tail, rfl⟩
  exact terminalExploitabilityGap_le_quittingTerminalExploitability
    reward hM hreward hexploit
      (quittingPhaseSwitchProfile reward plan tail switch)

/-- Elementary compression returns any actual-tail terminal obstruction to
one canonical capped suffix, losing only an arbitrary positive tolerance.
This is a co-realized cap return, not realization of a separately stored
Nash--Bellman annotation. -/
theorem exists_elementaryTailCap_terminalExploitability_gt_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {M gap ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      gap - ε < quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward plan
          (quittingElementaryTailRoots tail cutoff cap) switch) := by
  obtain ⟨cap, cutoff, hclose⟩ :=
    QuittingBoundaryHolonomy.exists_elementaryTailCap_behavioralTailGain_close
      reward tail plan 0 (switch - 1) hM hε hreward
  have hactual := terminalExploitabilityGap_le_quittingTerminalExploitability
    reward hM hreward hexploit
      (quittingPhaseSwitchProfile reward plan tail switch)
  change |QuittingBoundaryHolonomy.behavioralTailGain reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) tail -
      QuittingBoundaryHolonomy.behavioralTailGain reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1))
        (quittingElementaryTailRoots tail cutoff cap)| < ε at hclose
  rw [quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
      reward plan tail switch hswitch hM hreward,
    quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
      reward plan (quittingElementaryTailRoots tail cutoff cap)
        switch hswitch hM hreward] at hclose
  refine ⟨cap, cutoff, ?_⟩
  have hupper := (abs_lt.mp hclose).2
  linarith

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness
namespace CounterexampleRegimePeriodOneTangentReadout

variable (seam : QuittingCounterexampleSeamWitness regime)
variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- Every selected one-root prefix inherits the regime's terminal-gap floor
for the infimum over all co-realized behavioral tails.  This conclusion is
independent of tangent sign; it is the existing terminal obstruction, not an
attachment theorem for the active owner. -/
theorem terminalGap_le_periodOne_behavioralTailRepairValue (index : ℕ) :
    regime.terminalGap ≤
      QuittingBoundaryHolonomy.behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) 0 0) := by
  exact terminalExploitabilityGap_le_behavioralTailRepairValue reward
    (quittingPeriodOneRootSequence
      (seam.periodOneReadoutRoot readout.start index)) 1 (by omega)
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)
    regime.terminalExploitability

/-- For every selected root, elementary compression of its actual suffix
returns a co-realized terminal obstruction larger than half the regime gap.
This is likewise independent of the active-positive packet branch. -/
theorem exists_elementaryTailCap_periodOne_terminalObstruction (index : ℕ) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      regime.terminalGap / 2 < quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index))
          (quittingElementaryTailRoots
            (seam.periodOneReadoutActualSuffix readout.start index)
            cutoff cap) 1) := by
  have hhalf : 0 < regime.terminalGap / 2 := by
    linarith [regime.terminalGap_pos]
  obtain ⟨cap, cutoff, hcap⟩ :=
    exists_elementaryTailCap_terminalExploitability_gt_sub reward
      (quittingPeriodOneRootSequence
        (seam.periodOneReadoutRoot readout.start index))
      (seam.periodOneReadoutActualSuffix readout.start index) 1
      (by omega) (quittingRewardBound_nonneg reward) hhalf
      (abs_reward_le_quittingRewardBound reward)
      regime.terminalExploitability
  refine ⟨cap, cutoff, ?_⟩
  have hhalfEq : regime.terminalGap - regime.terminalGap / 2 =
      regime.terminalGap / 2 := by ring
  rw [← hhalfEq]
  exact hcap

end CounterexampleRegimePeriodOneTangentReadout
end QuittingCounterexampleSeamWitness

end GameTheory
