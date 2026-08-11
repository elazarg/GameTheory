/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerApproxPunishment
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailGainDensity

/-!
# Common-word realization at a two-owner tangent seam

A target-closed punishment tail is selected separately for one target player;
nothing in that interface makes those playerwise suffixes equal.  This module
therefore keeps the common-tail consistency issue explicit.  For a fixed
finite prefix, `behavioralTailRepairValue` is the infimum of the actual
all-player gain envelope over single common behavioral suffixes.

Elementary tail compression shows that strict repair below `ε` is witnessed
by one capped elementary product-root word.  Its literal phase-switch profile
is terminal `ε`-Nash, and hence every player's payoff remains above the
punishment floor up to `ε`.  At the exact two-owner tangent root, zero repair
therefore supplies such a common word at every positive error.  Conversely,
the named repair value is a lower bound on the literal exploitability of every
common suffix, so a positive value is the exact surviving co-realization
obstruction.

This is a terminal one-prefix attachment theorem.  It does not identify the
separately constructed target-closed punishment tails, and it does not assert
a return, a cycle, or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Literal terminal exploitability bounds every behavioral deviation, hence
is a terminal approximate-Nash certificate. -/
theorem isεAsymptoticNash_of_quittingTerminalExploitability_le
    (profile : (quittingGame reward).BehaviorProfile) {ε : ℝ}
    (hexploit : quittingTerminalExploitability reward profile ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile := by
  intro who deviation
  have hM := quittingRewardBound_nonneg reward
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation hM (abs_reward_le_quittingRewardBound reward)
  have hcoordinate :
      max 0 (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) ≤
        quittingTerminalExploitability reward profile := by
    unfold quittingTerminalExploitability
    exact le_finitePlayerMax (fun player : ι =>
      max 0 (quittingContinuationBestResponseValue reward profile player -
        quittingTerminalPayoff reward profile player)) who
  have hgap : quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who ≤ ε :=
    (le_max_right 0 _).trans (hcoordinate.trans hexploit)
  linarith

omit [Nonempty ι] in
/-- Every terminal approximate Nash profile remains above punishment up to
its approximation error. -/
theorem punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash
    (profile : (quittingGame reward).BehaviorProfile) {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) (who : ι) :
    quittingPunishmentValue reward who - ε ≤
      quittingTerminalPayoff reward profile who := by
  have hbest : quittingBestReplyValue reward profile who ≤
      quittingTerminalPayoff reward profile who + ε := by
    unfold quittingBestReplyValue
    apply ciSup_le
    intro deviation
    exact hnash who deviation
  have hpunish := quittingPunishmentValue_le reward who profile
  linarith

/-- The common-tail repair value is nonnegative. -/
theorem behavioralTailRepairValue_nonneg
    (holonomy : QuittingBoundaryHolonomy ι) :
    0 ≤ behavioralTailRepairValue reward holonomy := by
  unfold behavioralTailRepairValue
  apply le_csInf (Set.range_nonempty _)
  rintro value ⟨roots, rfl⟩
  exact behavioralTailGain_nonneg reward holonomy roots

/-- The repair infimum is a lower bound for the co-realized gain of every
single common behavioral suffix. -/
theorem behavioralTailRepairValue_le_behavioralTailGain
    (holonomy : QuittingBoundaryHolonomy ι)
    (roots : ℕ → ι → PMF Bool) :
    behavioralTailRepairValue reward holonomy ≤
      behavioralTailGain reward holonomy roots := by
  unfold behavioralTailRepairValue
  exact csInf_le (bddBelow_range_behavioralTailGain reward holonomy)
    ⟨roots, rfl⟩

/-- If the fixed-prefix common-tail repair value is below `ε`, one elementary
capped tail gives a single common product-root word whose literal terminal
profile is `ε`-Nash and stays above punishment minus `ε`. -/
theorem exists_commonElementaryTail_isεAsymptoticNash_of_repairValue_lt
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {ε : ℝ}
    (hrepair : behavioralTailRepairValue reward
      (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) < ε) :
    ∃ source : ℕ → ι → PMF Bool,
      ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
        let tail := quittingElementaryTailRoots source cutoff cap
        let profile := quittingPhaseSwitchProfile reward plan tail switch
        quittingTerminalExploitability reward profile < ε ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          (∀ who, quittingPunishmentValue reward who - ε ≤
            quittingTerminalPayoff reward profile who) := by
  let holonomy := quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)
  have heq := elementaryTailRepairValue_eq_behavioralTailRepairValue
    reward plan 0 (switch - 1) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hlt : elementaryTailRepairValue reward holonomy < ε := by
    rw [heq]
    exact hrepair
  have hbdd := bddBelow_range_elementaryTailGain reward holonomy
  have hne := elementaryTailGain_range_nonempty reward holonomy
  obtain ⟨gain, ⟨index, rfl⟩, hgain⟩ := (csInf_lt_iff hbdd hne).mp hlt
  rcases index with ⟨source, cap, cutoff⟩
  let tail := quittingElementaryTailRoots source cutoff cap
  let profile := quittingPhaseSwitchProfile reward plan tail switch
  have hexploit : quittingTerminalExploitability reward profile < ε := by
    rw [← quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
      reward plan tail switch hswitch (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)]
    exact hgain
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le
    (reward := reward) profile hexploit.le
  refine ⟨source, cap, cutoff, hexploit, hnash, ?_⟩
  intro who
  exact punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash
    (reward := reward) profile hnash who

/-- At every accuracy, either a common elementary word realizes the fixed
prefix up to that accuracy, or the named common-tail repair value is already
an exact positive consistency obstruction at that scale. -/
theorem commonElementaryWord_or_repairValue_ge
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {ε : ℝ} :
    (∃ source : ℕ → ι → PMF Bool,
      ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
        let tail := quittingElementaryTailRoots source cutoff cap
        let profile := quittingPhaseSwitchProfile reward plan tail switch
        quittingTerminalExploitability reward profile < ε ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          (∀ who, quittingPunishmentValue reward who - ε ≤
            quittingTerminalPayoff reward profile who)) ∨
      ε ≤ behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) := by
  by_cases hrepair : behavioralTailRepairValue reward
      (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) < ε
  · exact Or.inl <|
      exists_commonElementaryTail_isεAsymptoticNash_of_repairValue_lt
        (reward := reward) plan switch hswitch hrepair
  · exact Or.inr (le_of_not_gt hrepair)

/-- Vanishing common-tail repair gives one common elementary word at every
strictly positive accuracy. -/
theorem exists_commonElementaryTail_isεAsymptoticNash_of_repairValue_eq_zero
    (plan : ℕ → ι → PMF Bool) (switch : ℕ) (hswitch : 0 < switch)
    {ε : ℝ} (hε : 0 < ε)
    (hrepair : behavioralTailRepairValue reward
      (quittingFiniteBoundaryHolonomy reward plan 0 (switch - 1)) = 0) :
    ∃ source : ℕ → ι → PMF Bool,
      ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
        let tail := quittingElementaryTailRoots source cutoff cap
        let profile := quittingPhaseSwitchProfile reward plan tail switch
        quittingTerminalExploitability reward profile < ε ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          (∀ who, quittingPunishmentValue reward who - ε ≤
            quittingTerminalPayoff reward profile who) := by
  apply exists_commonElementaryTail_isεAsymptoticNash_of_repairValue_lt
    (reward := reward) plan switch hswitch
  rw [hrepair]
  exact hε

namespace QuittingChargeTangentPacket

/-- The period-one prefix whose only used root is the packet's exact
two-owner product root. -/
def twoOwnerCommonWordPlan
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ℕ → ι → PMF Bool :=
  fun _ => packet.twoOwnerRootAt first second t ht0 ht1

/-- The exact common-tail consistency scalar behind the packet's period-one
two-owner product root. -/
def twoOwnerCommonWordRepairValue
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ℝ :=
  behavioralTailRepairValue reward
    (quittingFiniteBoundaryHolonomy reward
      (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 0 0)

/-- The seam's common-word repair scalar is a literal lower bound for the
terminal exploitability of every common behavioral suffix attached after the
two-owner root. -/
theorem twoOwnerCommonWordRepairValue_le_terminalExploitability
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (tail : ℕ → ι → PMF Bool) :
    packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 ≤
      quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward
          (packet.twoOwnerCommonWordPlan first second t ht0 ht1) tail 1) := by
  rw [← quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
    reward (packet.twoOwnerCommonWordPlan first second t ht0 ht1) tail 1
      (by norm_num) (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)]
  exact behavioralTailRepairValue_le_behavioralTailGain
    (reward := reward)
    (quittingFiniteBoundaryHolonomy reward
      (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 0 0) tail

/-- At a fixed accuracy, the exact two-owner seam root either extends to one
common elementary terminal word, or its named repair scalar separates every
common behavioral suffix at that accuracy. -/
theorem commonTwoOwnerElementaryWord_or_repairValue_ge
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ε : ℝ} :
    (∃ source : ℕ → ι → PMF Bool,
      ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
        let tail := quittingElementaryTailRoots source cutoff cap
        let profile := quittingPhaseSwitchProfile reward
          (packet.twoOwnerCommonWordPlan first second t ht0 ht1) tail 1
        quittingTerminalExploitability reward profile < ε ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          (∀ who, quittingPunishmentValue reward who - ε ≤
            quittingTerminalPayoff reward profile who)) ∨
      ε ≤ packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 := by
  simpa [twoOwnerCommonWordRepairValue] using
    (commonElementaryWord_or_repairValue_ge
      (reward := reward)
      (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 1 (by norm_num)
      (ε := ε))

/-- If the exact two-owner seam has zero common-tail repair, it extends to a
single common elementary terminal word at every positive error. -/
theorem exists_commonTwoOwnerElementaryWord_of_repairValue_eq_zero
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (hrepair : packet.twoOwnerCommonWordRepairValue
      first second t ht0 ht1 = 0) :
    ∃ source : ℕ → ι → PMF Bool,
      ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
        let tail := quittingElementaryTailRoots source cutoff cap
        let profile := quittingPhaseSwitchProfile reward
          (packet.twoOwnerCommonWordPlan first second t ht0 ht1) tail 1
        quittingTerminalExploitability reward profile < ε ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          (∀ who, quittingPunishmentValue reward who - ε ≤
            quittingTerminalPayoff reward profile who) := by
  apply exists_commonElementaryTail_isεAsymptoticNash_of_repairValue_eq_zero
    (reward := reward)
    (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 1 (by norm_num) hε
  simpa [twoOwnerCommonWordRepairValue] using hrepair

/-- The packet's period-one common repair vanishes exactly when capped common
product-root words make its literal terminal exploitability arbitrarily
small.  Thus a positive repair value is precisely the common-word consistency
obstruction left after playerwise target-tail construction. -/
theorem twoOwnerCommonWordRepairValue_eq_zero_iff
    (packet : QuittingChargeTangentPacket reward)
    (first second : ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    packet.twoOwnerCommonWordRepairValue first second t ht0 ht1 = 0 ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ source : ℕ → ι → PMF Bool,
          ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff : ℕ,
            let tail := quittingElementaryTailRoots source cutoff cap
            let profile := quittingPhaseSwitchProfile reward
              (packet.twoOwnerCommonWordPlan first second t ht0 ht1) tail 1
            quittingTerminalExploitability reward profile < ε := by
  constructor
  · intro hrepair ε hε
    obtain ⟨source, cap, cutoff, hexploit, _⟩ :=
      packet.exists_commonTwoOwnerElementaryWord_of_repairValue_eq_zero
        first second t ht0 ht1 hε hrepair
    exact ⟨source, cap, cutoff, hexploit⟩
  · intro hwords
    apply le_antisymm
    · by_contra hnot
      have hpositive : 0 < packet.twoOwnerCommonWordRepairValue
          first second t ht0 ht1 := lt_of_not_ge hnot
      obtain ⟨source, cap, cutoff, hexploit⟩ :=
        hwords (packet.twoOwnerCommonWordRepairValue
          first second t ht0 ht1 / 2) (half_pos hpositive)
      let tail := quittingElementaryTailRoots source cutoff cap
      have hlower := packet.twoOwnerCommonWordRepairValue_le_terminalExploitability
        first second t ht0 ht1 tail
      dsimp only at hexploit
      linarith
    · exact behavioralTailRepairValue_nonneg
        (reward := reward)
        (quittingFiniteBoundaryHolonomy reward
          (packet.twoOwnerCommonWordPlan first second t ht0 ht1) 0 0)

end QuittingChargeTangentPacket

end GameTheory

