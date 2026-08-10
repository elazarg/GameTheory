/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCommonWordRealization
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneAttachmentRepair

/-!
# Playerwise punishment tails do not glue to a common repaired suffix

For every positive tolerance, stationary min--max approximation supplies all
finitely many players simultaneously with player-indexed target-closed tails
whose selected endpoints lie within that tolerance above punishment.  This
finite choice does not make the tails compatible.

The obstruction is already exact at the game level.  A positive terminal
exploitability gap lower-bounds the behavioral-tail repair value after every
positive finite prefix.  Consequently, inside a counterexample regime, the
packet's period-one two-owner root admits arbitrarily accurate playerwise
punishment tails while every single common behavioral suffix retains at least
the regime's positive terminal gap.

This also explains why the natural gluing operations do not follow from the
landed hypotheses.  Sequential blocks expose later tails only on survival;
nontrivial product-root randomization can absorb and pays the corresponding
coalition reward; and elementary caps approximate a boundary pair already
co-realized by one tail rather than combining coordinates from different
tails.  A common repair-zero premise, or a construction implying it, remains
necessary.  No return or cycle is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Nonempty ι] in
/-- At every positive accuracy, all finitely many players simultaneously have
player-indexed target-closed tails whose own endpoints lie within that
accuracy above their punishment values.  The tails remain player-indexed. -/
theorem exists_targetClosedApproxPunishmentTailFamily
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ tails : ι → ℕ → ι → PMF Bool,
      (∀ player, IsQuittingTargetClosedAt reward (tails player) player 0) ∧
      (∀ player,
        quittingRootSequenceTerminalValue reward (tails player) player 0 <
          quittingPunishmentValue reward player + δ) := by
  choose rows hrows using fun player : ι =>
    exists_stationaryRoot_cap_lt_punishmentValue_add reward player hδ
  obtain ⟨tails, hclosed, hvalue⟩ :=
    exists_quittingTargetClosedTailFamily_of_stationaryRoots reward rows
  refine ⟨tails, hclosed, ?_⟩
  intro player
  rw [hvalue player]
  exact hrows player

/-- A positive uniform terminal gap coexists with arbitrarily accurate
player-indexed target-closed punishment tails, while forcing strictly positive
common-tail repair after every positive finite prefix. -/
theorem targetClosedApproxPunishmentTails_and_commonRepair_pos
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    (∀ δ : ℝ, 0 < δ →
      ∃ tails : ι → ℕ → ι → PMF Bool,
        (∀ player,
          IsQuittingTargetClosedAt reward (tails player) player 0) ∧
        (∀ player,
          quittingRootSequenceTerminalValue reward (tails player) player 0 <
            quittingPunishmentValue reward player + δ)) ∧
      0 < behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) := by
  constructor
  · intro δ hδ
    exact exists_targetClosedApproxPunishmentTailFamily
      (reward := reward) hδ
  · have hlower := terminalExploitabilityGap_le_behavioralTailRepairValue
      reward plan switch hswitch (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hexploit
    exact hgap.trans_le hlower

namespace QuittingChargeTangentPacket

/-- In a counterexample regime, the exact two-owner seam exhibits the sharp
gluing regression: arbitrarily accurate playerwise closed punishment tails
exist, but its common-word repair value is bounded below by the positive
terminal gap. -/
theorem targetClosedApproxPunishmentTails_and_twoOwnerCommonRepair_pos
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ δ : ℝ, 0 < δ →
      ∃ tails : ι → ℕ → ι → PMF Bool,
        (∀ player,
          IsQuittingTargetClosedAt reward (tails player) player 0) ∧
        (∀ player,
          quittingRootSequenceTerminalValue reward (tails player) player 0 <
            quittingPunishmentValue reward player + δ)) ∧
      regime.terminalGap ≤
        packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 ∧
      0 < packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 := by
  have hregression :=
    targetClosedApproxPunishmentTails_and_commonRepair_pos
      (reward := reward)
      (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 1 (by norm_num)
      regime.terminalGap_pos regime.terminalExploitability
  refine ⟨hregression.1, ?_, hregression.2⟩
  simpa [twoOwnerCommonWordRepairValue] using
    (terminalExploitabilityGap_le_behavioralTailRepairValue reward
      (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 1 (by norm_num)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      regime.terminalExploitability)

/-- Therefore the common-word zero-repair premise cannot be derived from the
mere existence of arbitrarily accurate playerwise target-closed punishment
tails inside a counterexample regime. -/
theorem not_twoOwnerCommonWordRepairValue_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 ≠ 0 := by
  exact ne_of_gt
    (targetClosedApproxPunishmentTails_and_twoOwnerCommonRepair_pos
      regime packet first second t ht0 ht1).2.2

end QuittingChargeTangentPacket

end GameTheory


