/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse

/-!
# Quantitative opponent-clock budget below the punishment floor

Floor-violation amplification contains a quantitative statement stronger than
mere summability.  If the initial violation gap is `delta`, then every finite
suffix clock, and hence the full suffix clock, satisfies the division-free
bound

`delta * opponentClock ≤ punishmentValue + rewardBound`.

The cross-multiplied form remains meaningful for exact rational certificates
and avoids division or rounding in search code.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Finite, division-free floor-violation clock budget. -/
theorem quittingPunishmentGap_mul_partialOpponentClock_le
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start fuel : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    (quittingPunishmentValue reward who - (tail start).1.1 who) *
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
      quittingPunishmentValue reward who + quittingRewardBound reward := by
  let gap := quittingPunishmentValue reward who - (tail start).1.1 who
  let scale := quittingPunishmentValue reward who + quittingRewardBound reward
  have hgap : 0 < gap := sub_pos.mpr hviolation
  have hscale : 0 < scale := by
    have hlow : -quittingRewardBound reward ≤ (tail start).1.1 who :=
      (hbox start).1.1 who
    dsimp only [gap, scale] at hgap ⊢
    linarith
  have hraw : ∀ offset,
      gap ≤ quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots tail) who start offset * scale := by
    intro offset
    have htelescope :=
      quittingPunishmentGap_le_opponentSurvivalWeight_mul_of_dynamicDebtTail
        tail hedge who start hviolation offset
    have hlate : -quittingRewardBound reward ≤
        (tail (start + offset)).1.1 who :=
      (hbox (start + offset)).1.1 who
    have hweight := quittingOpponentSurvivalWeight_nonneg
      (quittingDynamicDebtTailRoots tail) who start offset
    dsimp only [gap, scale]
    calc
      quittingPunishmentValue reward who - (tail start).1.1 who ≤
          quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            (quittingPunishmentValue reward who -
              (tail (start + offset)).1.1 who) := htelescope
      _ ≤ quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            (quittingPunishmentValue reward who +
              quittingRewardBound reward) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight
  have hstep : ∀ offset,
      gap * quittingOpponentClockCharge
          (quittingDynamicDebtTailRoots tail) who (start + offset) ≤
        scale *
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset -
            quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start (offset + 1)) := by
    intro offset
    have hcharge := quittingOpponentClockCharge_nonneg
      (quittingDynamicDebtTailRoots tail) who (start + offset)
    have hfactor :
        quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset -
            quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start (offset + 1) =
          quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            quittingOpponentClockCharge
              (quittingDynamicDebtTailRoots tail) who (start + offset) := by
      rw [quittingOpponentSurvivalWeight_succ,
        quittingOpponentClockCharge_eq_one_sub]
      ring
    rw [hfactor]
    calc
      gap * quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset) ≤
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset * scale) *
            quittingOpponentClockCharge
              (quittingDynamicDebtTailRoots tail) who (start + offset) :=
        mul_le_mul_of_nonneg_right (hraw offset) hcharge
      _ = scale *
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            quittingOpponentClockCharge
              (quittingDynamicDebtTailRoots tail) who (start + offset)) := by
        ring
  have htelescope := Finset.sum_range_sub'
    (fun offset => quittingOpponentSurvivalWeight
      (quittingDynamicDebtTailRoots tail) who start offset) fuel
  have hweight := quittingOpponentSurvivalWeight_nonneg
    (quittingDynamicDebtTailRoots tail) who start fuel
  change gap * _ ≤ scale
  rw [Finset.mul_sum]
  calc
    (∑ offset ∈ Finset.range fuel,
        gap * quittingOpponentClockCharge
          (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
      ∑ offset ∈ Finset.range fuel, scale *
        (quittingOpponentSurvivalWeight
            (quittingDynamicDebtTailRoots tail) who start offset -
          quittingOpponentSurvivalWeight
            (quittingDynamicDebtTailRoots tail) who start (offset + 1)) :=
      Finset.sum_le_sum fun offset _ => hstep offset
    _ = scale * (1 - quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots tail) who start fuel) := by
      rw [← Finset.mul_sum, htelescope]
      simp [quittingOpponentSurvivalWeight]
    _ ≤ scale := by nlinarith

/-- Full division-free floor-violation clock budget. -/
theorem quittingPunishmentGap_mul_tsum_opponentClock_le
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    (quittingPunishmentValue reward who - (tail start).1.1 who) *
        ∑' offset, quittingOpponentClockCharge
          (quittingDynamicDebtTailRoots tail) who (start + offset) ≤
      quittingPunishmentValue reward who + quittingRewardBound reward := by
  let gap := quittingPunishmentValue reward who - (tail start).1.1 who
  let clock := fun offset => quittingOpponentClockCharge
    (quittingDynamicDebtTailRoots tail) who (start + offset)
  have hgap : 0 ≤ gap := (sub_pos.mpr hviolation).le
  have hnonneg : ∀ offset, 0 ≤ gap * clock offset := fun offset =>
    mul_nonneg hgap (quittingOpponentClockCharge_nonneg _ _ _)
  have hbound : ∀ fuel, ∑ offset ∈ Finset.range fuel,
      gap * clock offset ≤
        quittingPunishmentValue reward who + quittingRewardBound reward := by
    intro fuel
    rw [← Finset.mul_sum]
    exact quittingPunishmentGap_mul_partialOpponentClock_le
      tail hbox hedge who start fuel hviolation
  have htsum := Real.tsum_le_of_sum_range_le hnonneg hbound
  change gap * ∑' offset, clock offset ≤ _
  rw [← tsum_mul_left]
  exact htsum

end GameTheory
