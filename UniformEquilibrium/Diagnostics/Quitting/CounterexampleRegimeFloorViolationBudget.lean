/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.SurvivalAmplification
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse

/-!
# Quantitative opponent-clock budget below the punishment floor

Floor-violation amplification contains a quantitative statement stronger than
mere summability.  If the initial violation gap is `delta`, then every finite
suffix clock, and hence the full suffix clock, satisfies the division-free
bound

`delta * opponentClock ≤ punishmentValue + rewardBound`.

The proof is a thin quitting-game adapter around the scalar survival theorem
in `Math.Probability.SurvivalAmplification`: quitting semantics are used only
to produce positive bounded gaps and the one-step amplification inequality.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The scalar hazard obtained by shifting one player's opponent clock to a
chosen starting date. -/
def quittingOpponentClockHazard
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    DiscreteHazard.ScalarHazard where
  stop offset := quittingOpponentClockCharge roots who (start + offset)
  stop_nonneg _offset := quittingOpponentClockCharge_nonneg roots who _
  stop_le_one _offset := quittingOpponentClockCharge_le_one roots who _

/-- Shifted punishment-floor gap along a dynamic-debt tail. -/
def quittingPunishmentGapTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → QuittingDebtPoint ι) (who : ι) (start offset : ℕ) : ℝ :=
  quittingPunishmentValue reward who - (tail (start + offset)).1.1 who

theorem quittingPunishmentGapTail_pos
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    ∀ offset, 0 < quittingPunishmentGapTail reward tail who start offset := by
  intro offset
  have hlate := quittingDynamicDebtTail_floorViolation_mono
    tail hedge who hviolation (start + offset) (Nat.le_add_right start offset)
  exact sub_pos.mpr hlate

theorem quittingPunishmentGapTail_le_scale
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (who : ι) (start offset : ℕ) :
    quittingPunishmentGapTail reward tail who start offset ≤
      quittingPunishmentValue reward who + quittingRewardBound reward := by
  have hlow : -quittingRewardBound reward ≤
      (tail (start + offset)).1.1 who := (hbox (start + offset)).1.1 who
  unfold quittingPunishmentGapTail
  linarith

/-- The game-specific one-edge estimate is exactly scalar survival
amplification for the shifted opponent-clock hazard. -/
theorem quittingPunishmentGapTail_amplify
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    ∀ offset,
      quittingPunishmentGapTail reward tail who start offset ≤
        (1 - (quittingOpponentClockHazard
          (quittingDynamicDebtTailRoots tail) who start).stop offset) *
        quittingPunishmentGapTail reward tail who start (offset + 1) := by
  intro offset
  have hlate := quittingDynamicDebtTail_floorViolation_mono
    tail hedge who hviolation (start + offset) (Nat.le_add_right start offset)
  obtain ⟨-, hkey⟩ :=
    quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge
      (tail (start + offset)).1 (tail (start + offset + 1)).1
      (hedge (start + offset)).1 who hlate
  have hkeyFixed :
      quittingPunishmentValue reward who -
          (tail (start + offset)).1.1 who ≤
        quittingFixedOpponentsContinueMass
            (quittingDynamicDebtTailRoots tail) who (start + offset) *
          (quittingPunishmentValue reward who -
            (tail (start + offset + 1)).1.1 who) := hkey
  change
    quittingPunishmentValue reward who - (tail (start + offset)).1.1 who ≤
      (1 - quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) who (start + offset)) *
      (quittingPunishmentValue reward who -
        (tail (start + (offset + 1))).1.1 who)
  rw [quittingOpponentClockCharge_eq_one_sub]
  rw [show start + (offset + 1) = start + offset + 1 by omega]
  simpa using hkeyFixed

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
  simpa [quittingPunishmentGapTail, quittingOpponentClockHazard] using
    DiscreteHazard.ScalarHazard.gap_mul_sum_stop_le_bound
      (quittingOpponentClockHazard
        (quittingDynamicDebtTailRoots tail) who start)
      (quittingPunishmentGapTail reward tail who start)
      (quittingPunishmentValue reward who + quittingRewardBound reward)
      (quittingPunishmentGapTail_pos tail hedge who start hviolation)
      (quittingPunishmentGapTail_le_scale tail hbox who start)
      (quittingPunishmentGapTail_amplify tail hedge who start hviolation)
      0 fuel

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
  simpa [quittingPunishmentGapTail, quittingOpponentClockHazard] using
    DiscreteHazard.ScalarHazard.gap_mul_tsum_stop_natAdd_le_bound
      (quittingOpponentClockHazard
        (quittingDynamicDebtTailRoots tail) who start)
      (quittingPunishmentGapTail reward tail who start)
      (quittingPunishmentValue reward who + quittingRewardBound reward)
      (quittingPunishmentGapTail_pos tail hedge who start hviolation)
      (quittingPunishmentGapTail_le_scale tail hbox who start)
      (quittingPunishmentGapTail_amplify tail hedge who start hviolation)
      0

end GameTheory
