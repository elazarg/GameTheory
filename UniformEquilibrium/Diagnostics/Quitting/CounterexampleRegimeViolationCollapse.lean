/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit

/-!
# Violation collapse for exact dynamic-debt tails

Fix one exact Nash--Bellman edge with displayed value `v`, continuation `w`,
and root `x`.  If a player's displayed value violates the behavioral
punishment floor `chi`, comparing the floor with that player's stationary
reply cap at the very root `x` shows that the opponents-continue mass `c` of
`x` is positive and that the violation amplifies:

`chi - v <= c * (chi - w)`.

In particular the continuation violates at least as much.  Along a
chronological exact dynamic-debt tail the violating coordinate set is
therefore monotone --- rotation between violators is impossible --- and each
violator's gap below the floor is nondecreasing.  Telescoping the
amplification bounds every finite opponents-survival product below by the
initial gap over `chi + M`, where `M` is the reward bound, so a violator's
additive opponent clock is summable.

The collapse theorem combines this with the debt geometry.  Along a boxed
exact-debt tail with one floor-violating date and one positive debt
coordinate, the joint absorption charge is summable.  Otherwise the fixed
perpetual violator would carry a summable opponent clock but a nonsummable
own Quit mass; at its cofinal Quit-support dates exactness pins its displayed
value to the pure-Quit endpoint, which the vanishing opponent hazard drives
to the solo singleton reward.  The violator's solo reward then lies strictly
below the floor, forcing its positive-singleton debt cap --- and hence its
whole debt column --- to zero.  The positive debt thus belongs to another
player, whose summable opponent clock dominates the violator's own Quit
mass, a contradiction.

Consequently the optimized tail extracted from a counterexample regime has
summable joint absorption charge unconditionally: the previous two-branch
carrier alternative collapses to its summable horn, and the extracted roots
converge coordinatewise to all-Continue.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Violation amplification across one exact Nash--Bellman edge -/

/-- **Floor-violation amplification.**  If the displayed value of an exact
Nash--Bellman edge violates the behavioral punishment floor at one player,
then that player's opponents-continue mass at the displayed root is positive,
and the floor gap of the displayed value is at most that mass times the floor
gap of the continuation value.

The proof plays the displayed root against the punishment floor: the floor is
below the stationary reply cap at that root, the pure-Quit leg of the cap is
below the violating displayed value, so the cap is carried by the ride-forever
leg, whose cleared form is exactly the amplification inequality. -/
theorem quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge
    (current successor : QuittingNashBellmanPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current successor) (who : ι)
    (hviolation : current.1 who < quittingPunishmentValue reward who) :
    0 < quittingStationaryFixedOpponentsContinueMass
        (quittingRootOfSimplex current.2) who ∧
      quittingPunishmentValue reward who - current.1 who ≤
        quittingStationaryFixedOpponentsContinueMass
            (quittingRootOfSimplex current.2) who *
          (quittingPunishmentValue reward who - successor.1 who) := by
  have hquitLe :=
    quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
      reward current successor hedge who
  have hcontinueLe :=
    quittingRootContinuePayoff_le_currentValue_of_nashBellmanEdge
      reward current successor hedge who
  have hquitEq :
      quittingRootQuitPayoff reward successor.1
          (quittingRootOfSimplex current.2) who =
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingRootOfSimplex current.2) who :=
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
      (fun _ ↦ quittingRootOfSimplex current.2) who successor.1 0
  have hcontinueEq :
      quittingRootContinuePayoff reward successor.1
          (quittingRootOfSimplex current.2) who =
        quittingStationaryFixedOpponentsContinueReward reward
            (quittingRootOfSimplex current.2) who +
          quittingStationaryFixedOpponentsContinueMass
              (quittingRootOfSimplex current.2) who * successor.1 who :=
    quittingRootContinuePayoff_eq_fixedOpponents reward
      (fun _ ↦ quittingRootOfSimplex current.2) who successor.1 0
  rw [hquitEq] at hquitLe
  rw [hcontinueEq] at hcontinueLe
  have hquitDead :
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingRootOfSimplex current.2) who <
        quittingPunishmentValue reward who :=
    lt_of_le_of_lt hquitLe hviolation
  have hcap :=
    quittingPunishmentValue_le_stationaryUnilateralCap reward who
      (quittingRootOfSimplex current.2)
  rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
  have hmass0 :=
    quittingStationaryFixedOpponentsContinueMass_nonneg
      (quittingRootOfSimplex current.2) who
  have hmass1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one
      (quittingRootOfSimplex current.2) who
  have hmasspos :
      0 < quittingStationaryFixedOpponentsContinueMass
        (quittingRootOfSimplex current.2) who := by
    rcases eq_or_lt_of_le hmass0 with hzero | hpos
    · exfalso
      rw [← hzero] at hcontinueLe hcap
      rw [zero_mul, add_zero] at hcontinueLe
      norm_num at hcap
      have hcontinueDead :
          quittingStationaryFixedOpponentsContinueReward reward
              (quittingRootOfSimplex current.2) who <
            quittingPunishmentValue reward who :=
        lt_of_le_of_lt hcontinueLe hviolation
      rcases hcap with hcap | hcap
      · exact absurd hcap (not_le.mpr hquitDead)
      · exact absurd hcap (not_le.mpr hcontinueDead)
    · exact hpos
  refine ⟨hmasspos, ?_⟩
  rcases eq_or_lt_of_le hmass1 with hone | hlt
  · have hreward0 :
        quittingStationaryFixedOpponentsContinueReward reward
            (quittingRootOfSimplex current.2) who = 0 :=
      quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward hone
    rw [hreward0, hone] at hcontinueLe
    rw [hone]
    linarith
  · have hnever :
        quittingPunishmentValue reward who ≤
          quittingStationaryFixedOpponentsContinueReward reward
              (quittingRootOfSimplex current.2) who /
            (1 - quittingStationaryFixedOpponentsContinueMass
              (quittingRootOfSimplex current.2) who) := by
      rcases le_max_iff.mp hcap with hdead | hlive
      · exact absurd hdead (not_le.mpr hquitDead)
      · exact hlive
    have hclear :
        quittingPunishmentValue reward who *
            (1 - quittingStationaryFixedOpponentsContinueMass
              (quittingRootOfSimplex current.2) who) ≤
          quittingStationaryFixedOpponentsContinueReward reward
            (quittingRootOfSimplex current.2) who :=
      (le_div_iff₀ (by linarith)).mp hnever
    nlinarith [hclear, hcontinueLe]

/-- The continuation of an exact Nash--Bellman edge violates the punishment
floor whenever the displayed value does: violation propagates forward. -/
theorem successorValue_lt_quittingPunishmentValue_of_nashBellmanEdge
    (current successor : QuittingNashBellmanPoint ι)
    (hedge : IsQuittingNashBellmanEdge reward current successor) (who : ι)
    (hviolation : current.1 who < quittingPunishmentValue reward who) :
    successor.1 who < quittingPunishmentValue reward who := by
  obtain ⟨hmasspos, hgap⟩ :=
    quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge
      current successor hedge who hviolation
  by_contra hle
  push Not at hle
  have hproduct :
      quittingStationaryFixedOpponentsContinueMass
          (quittingRootOfSimplex current.2) who *
        (quittingPunishmentValue reward who - successor.1 who) ≤
      quittingStationaryFixedOpponentsContinueMass
          (quittingRootOfSimplex current.2) who * 0 :=
    mul_le_mul_of_nonneg_left (by linarith) hmasspos.le
  rw [mul_zero] at hproduct
  linarith

/-! ## No rotation: the violating coordinate set is monotone -/

/-- Along a chronological exact dynamic-debt tail, a punishment-floor
violation at one date persists at every later date.  The violator cannot
rotate away. -/
theorem quittingDynamicDebtTail_floorViolation_mono
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) {start : ℕ}
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    ∀ time, start ≤ time →
      (tail time).1.1 who < quittingPunishmentValue reward who := by
  intro time htime
  induction time, htime using Nat.le_induction with
  | base => exact hviolation
  | succ time _ ih =>
      exact successorValue_lt_quittingPunishmentValue_of_nashBellmanEdge
        (tail time).1 (tail (time + 1)).1 (hedge time).1 who ih

/-- One violating step of a chronological exact dynamic-debt tail cannot
raise the violating coordinate. -/
theorem quittingDynamicDebtTail_value_succ_le_of_floorViolation
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (time : ℕ)
    (hviolation : (tail time).1.1 who < quittingPunishmentValue reward who) :
    (tail (time + 1)).1.1 who ≤ (tail time).1.1 who := by
  obtain ⟨-, hgap⟩ :=
    quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge
      (tail time).1 (tail (time + 1)).1 (hedge time).1 who hviolation
  have hsuccessor := successorValue_lt_quittingPunishmentValue_of_nashBellmanEdge
    (tail time).1 (tail (time + 1)).1 (hedge time).1 who hviolation
  have hmass1 := quittingStationaryFixedOpponentsContinueMass_le_one
    (quittingRootOfSimplex (tail time).1.2) who
  have hshrink :
      quittingStationaryFixedOpponentsContinueMass
          (quittingRootOfSimplex (tail time).1.2) who *
        (quittingPunishmentValue reward who - (tail (time + 1)).1.1 who) ≤
      quittingPunishmentValue reward who - (tail (time + 1)).1.1 who :=
    mul_le_of_le_one_left (by linarith) hmass1
  linarith

/-- Once positive, the punishment-floor gap of a violator is nondecreasing
along a chronological exact dynamic-debt tail. -/
theorem quittingDynamicDebtTail_punishmentGap_mono
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) {start : ℕ}
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    ∀ time, start ≤ time →
      quittingPunishmentValue reward who - (tail start).1.1 who ≤
        quittingPunishmentValue reward who - (tail time).1.1 who := by
  intro time htime
  induction time, htime using Nat.le_induction with
  | base => exact le_rfl
  | succ time htime ih =>
      have hstep := quittingDynamicDebtTail_value_succ_le_of_floorViolation
        tail hedge who time
        (quittingDynamicDebtTail_floorViolation_mono tail hedge who
          hviolation time htime)
      linarith

/-! ## The violator's opponent clock is summable -/

/-- Telescoping the amplification inequality: the initial floor gap of a
violator is at most every later finite opponents-survival product times the
later floor gap. -/
theorem quittingPunishmentGap_le_opponentSurvivalWeight_mul_of_dynamicDebtTail
    (tail : ℕ → QuittingDebtPoint ι)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    ∀ fuel,
      quittingPunishmentValue reward who - (tail start).1.1 who ≤
        quittingOpponentSurvivalWeight
            (quittingDynamicDebtTailRoots tail) who start fuel *
          (quittingPunishmentValue reward who -
            (tail (start + fuel)).1.1 who) := by
  intro fuel
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hviolAt := quittingDynamicDebtTail_floorViolation_mono
        tail hedge who hviolation (start + fuel) (Nat.le_add_right start fuel)
      obtain ⟨-, hkey⟩ :=
        quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge
          (tail (start + fuel)).1 (tail (start + fuel + 1)).1
          (hedge (start + fuel)).1 who hviolAt
      have hkeyFixed :
          quittingPunishmentValue reward who -
              (tail (start + fuel)).1.1 who ≤
            quittingFixedOpponentsContinueMass
                (quittingDynamicDebtTailRoots tail) who (start + fuel) *
              (quittingPunishmentValue reward who -
                (tail (start + fuel + 1)).1.1 who) := hkey
      have hweight0 := quittingOpponentSurvivalWeight_nonneg
        (quittingDynamicDebtTailRoots tail) who start fuel
      calc
        quittingPunishmentValue reward who - (tail start).1.1 who ≤
            quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start fuel *
              (quittingPunishmentValue reward who -
                (tail (start + fuel)).1.1 who) := ih
        _ ≤ quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start fuel *
              (quittingFixedOpponentsContinueMass
                  (quittingDynamicDebtTailRoots tail) who (start + fuel) *
                (quittingPunishmentValue reward who -
                  (tail (start + fuel + 1)).1.1 who)) :=
            mul_le_mul_of_nonneg_left hkeyFixed hweight0
        _ = quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start (fuel + 1) *
              (quittingPunishmentValue reward who -
                (tail (start + (fuel + 1))).1.1 who) := by
            rw [quittingOpponentSurvivalWeight_succ]
            have hindex : start + fuel + 1 = start + (fuel + 1) := by omega
            rw [hindex]
            ring

/-- **The violator's opponent clock is summable.**  A single punishment-floor
violation along a boxed chronological exact dynamic-debt tail forces the
violator's additive opponent clock to be summable: every finite
opponents-survival product stays above the initial floor gap divided by
`chi + M`, and each stage's clock charge is paid by the survival decrement,
so all partial clock sums are bounded. -/
theorem summable_opponentClockCharge_of_dynamicDebtTail_floorViolation
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who) :
    Summable (quittingOpponentClockCharge
      (quittingDynamicDebtTailRoots tail) who) := by
  have hgap0 : 0 < quittingPunishmentValue reward who -
      (tail start).1.1 who := sub_pos.mpr hviolation
  have hlow : -quittingRewardBound reward ≤ (tail start).1.1 who :=
    (hbox start).1.1 who
  have hscale0 : 0 < quittingPunishmentValue reward who +
      quittingRewardBound reward := by linarith
  have hraw : ∀ fuel,
      quittingPunishmentValue reward who - (tail start).1.1 who ≤
        quittingOpponentSurvivalWeight
            (quittingDynamicDebtTailRoots tail) who start fuel *
          (quittingPunishmentValue reward who +
            quittingRewardBound reward) := by
    intro fuel
    have htelescope :=
      quittingPunishmentGap_le_opponentSurvivalWeight_mul_of_dynamicDebtTail
        tail hedge who start hviolation fuel
    have hlowLate : -quittingRewardBound reward ≤
        (tail (start + fuel)).1.1 who := (hbox (start + fuel)).1.1 who
    have hweight0 := quittingOpponentSurvivalWeight_nonneg
      (quittingDynamicDebtTailRoots tail) who start fuel
    calc
      quittingPunishmentValue reward who - (tail start).1.1 who ≤
          quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start fuel *
            (quittingPunishmentValue reward who -
              (tail (start + fuel)).1.1 who) := htelescope
      _ ≤ quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start fuel *
            (quittingPunishmentValue reward who +
              quittingRewardBound reward) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight0
  have hstep : ∀ offset,
      (quittingPunishmentValue reward who - (tail start).1.1 who) *
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset) ≤
        (quittingPunishmentValue reward who + quittingRewardBound reward) *
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset -
            quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start (offset + 1)) := by
    intro offset
    have hsucc := quittingOpponentSurvivalWeight_succ
      (quittingDynamicDebtTailRoots tail) who start offset
    have hchargeEq := quittingOpponentClockCharge_eq_one_sub
      (quittingDynamicDebtTailRoots tail) who (start + offset)
    have hcharge0 := quittingOpponentClockCharge_nonneg
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
      rw [hsucc, hchargeEq]
      ring
    rw [hfactor]
    calc
      (quittingPunishmentValue reward who - (tail start).1.1 who) *
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset) ≤
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            (quittingPunishmentValue reward who +
              quittingRewardBound reward)) *
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset) :=
        mul_le_mul_of_nonneg_right (hraw offset) hcharge0
      _ = (quittingPunishmentValue reward who + quittingRewardBound reward) *
          (quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start offset *
            quittingOpponentClockCharge
              (quittingDynamicDebtTailRoots tail) who (start + offset)) := by
        ring
  have hbound : ∀ fuel,
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
        (quittingPunishmentValue reward who + quittingRewardBound reward) /
          (quittingPunishmentValue reward who - (tail start).1.1 who) := by
    intro fuel
    have hzeroWeight : quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots tail) who start 0 = 1 := by
      simp [quittingOpponentSurvivalWeight]
    have hfuelWeight := quittingOpponentSurvivalWeight_nonneg
      (quittingDynamicDebtTailRoots tail) who start fuel
    have htelescopeSum :
        (∑ offset ∈ Finset.range fuel,
            (quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start offset -
              quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start (offset + 1))) =
          quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start 0 -
            quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start fuel :=
      Finset.sum_range_sub' (fun offset ↦
        quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots tail) who start offset) fuel
    have hsum :
        (quittingPunishmentValue reward who - (tail start).1.1 who) *
            (∑ offset ∈ Finset.range fuel,
              quittingOpponentClockCharge
                (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
          (quittingPunishmentValue reward who + quittingRewardBound reward) *
            (1 - quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start fuel) := by
      rw [Finset.mul_sum]
      calc
        (∑ offset ∈ Finset.range fuel,
            (quittingPunishmentValue reward who - (tail start).1.1 who) *
              quittingOpponentClockCharge
                (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
            ∑ offset ∈ Finset.range fuel,
              (quittingPunishmentValue reward who +
                  quittingRewardBound reward) *
                (quittingOpponentSurvivalWeight
                    (quittingDynamicDebtTailRoots tail) who start offset -
                  quittingOpponentSurvivalWeight
                    (quittingDynamicDebtTailRoots tail) who start
                    (offset + 1)) :=
          Finset.sum_le_sum fun offset _ ↦ hstep offset
        _ = (quittingPunishmentValue reward who +
              quittingRewardBound reward) *
            ∑ offset ∈ Finset.range fuel,
              (quittingOpponentSurvivalWeight
                  (quittingDynamicDebtTailRoots tail) who start offset -
                quittingOpponentSurvivalWeight
                  (quittingDynamicDebtTailRoots tail) who start
                  (offset + 1)) := by
          rw [Finset.mul_sum]
        _ = (quittingPunishmentValue reward who +
              quittingRewardBound reward) *
            (quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start 0 -
              quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots tail) who start fuel) := by
          rw [htelescopeSum]
        _ = (quittingPunishmentValue reward who +
              quittingRewardBound reward) *
            (1 - quittingOpponentSurvivalWeight
              (quittingDynamicDebtTailRoots tail) who start fuel) := by
          rw [hzeroWeight]
    rw [le_div_iff₀ hgap0]
    have hproduct0 : 0 ≤ (quittingPunishmentValue reward who +
        quittingRewardBound reward) *
      quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots tail) who start fuel :=
      mul_nonneg hscale0.le hfuelWeight
    linarith [hsum]
  have hsuffix : Summable (fun offset ↦
      quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) who (start + offset)) :=
    summable_of_sum_range_le
      (fun offset ↦ quittingOpponentClockCharge_nonneg
        (quittingDynamicDebtTailRoots tail) who (start + offset))
      hbound
  have hshift : Summable (fun offset ↦
      quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) who (offset + start)) := by
    simpa [Nat.add_comm] using hsuffix
  exact (summable_nat_add_iff start).1 hshift

/-! ## Splitting one stage of joint absorption -/

/-- One stage's joint absorption mass is at most the selected player's own
Quit probability plus that player's opponent-absorption hazard: joint
absorption is covered by the own hazard and the opponent hazard together. -/
theorem quittingRootAbsorptionMass_le_quitProbability_add_opponentAbsorptionMass
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root ≤
      (root who true).toReal +
        quittingRootOpponentAbsorptionMass root who := by
  have hfactor :=
    quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
  have hopponent : quittingRootOpponentAbsorptionMass root who =
      1 - quittingStationaryFixedOpponentsContinueMass root who := rfl
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hmass1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hquit0 : (0 : ℝ) ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hproduct : 0 ≤ (root who true).toReal *
      (1 - quittingStationaryFixedOpponentsContinueMass root who) :=
    mul_nonneg hquit0 (by linarith)
  have hown : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hfactor, hopponent, hown]
  linarith [hproduct]

omit [DecidableEq ι] in
/-- A single player's Quit probability is part of the joint absorption
mass. -/
theorem quitProbability_le_quittingRootAbsorptionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal ≤ quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

/-- A nonnegative series which is not summable has arbitrarily late strictly
positive terms. -/
private theorem exists_ge_pos_of_not_summable
    {f : ℕ → ℝ} (hnonneg : ∀ time, 0 ≤ f time)
    (hnot : ¬ Summable f) (threshold : ℕ) :
    ∃ time, threshold ≤ time ∧ 0 < f time := by
  by_contra hnone
  push Not at hnone
  apply hnot
  have hzero : ∀ offset, f (offset + threshold) = 0 := fun offset ↦
    le_antisymm (hnone (offset + threshold) (Nat.le_add_left threshold offset))
      (hnonneg (offset + threshold))
  have hshift : Summable (fun offset ↦ f (offset + threshold)) := by
    have hconst : (fun offset ↦ f (offset + threshold)) =
        fun _ ↦ (0 : ℝ) := funext hzero
    rw [hconst]
    exact summable_zero
  exact (summable_nat_add_iff threshold).1 hshift

/-! ## Collapse of a violating positive-debt tail -/

/-- **A violator with cofinal own-Quit support undercuts its own solo
reward.**  Once a coordinate of a boxed chronological exact-debt tail falls
below the behavioral punishment floor, its value column is nonincreasing and
converges.  If the violator's own Quit probability is positive at cofinally
many dates, exactness pins the displayed value to the pure-Quit endpoint at
each such date, and the summable opponent clock drives that endpoint to the
solo singleton reward.  The limit is therefore the solo reward itself, which
consequently lies strictly below the punishment floor. -/
theorem quittingSingletonReward_lt_punishmentValue_of_dynamicDebtTail_quitSupport
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start : ℕ)
    (hviolation : (tail start).1.1 who < quittingPunishmentValue reward who)
    (hsupport : ∀ threshold, ∃ time, threshold ≤ time ∧
      0 < (quittingDynamicDebtTailRoots tail time who true).toReal) :
    reward (quittingSingletonTerminal who) who <
      quittingPunishmentValue reward who := by
  have hclock :=
    summable_opponentClockCharge_of_dynamicDebtTail_floorViolation
      tail hbox hedge who start hviolation
  have hviolAll := quittingDynamicDebtTail_floorViolation_mono
    tail hedge who hviolation
  have hanti : Antitone (fun offset ↦ (tail (start + offset)).1.1 who) := by
    apply antitone_nat_of_succ_le
    intro offset
    exact quittingDynamicDebtTail_value_succ_le_of_floorViolation
      tail hedge who (start + offset)
      (hviolAll (start + offset) (Nat.le_add_right start offset))
  have hbdd : BddBelow (Set.range
      fun offset ↦ (tail (start + offset)).1.1 who) := by
    refine ⟨-quittingRewardBound reward, ?_⟩
    rintro value ⟨offset, rfl⟩
    exact (hbox (start + offset)).1.1 who
  have hshifted : Tendsto (fun offset ↦ (tail (start + offset)).1.1 who)
      atTop (nhds (⨅ offset, (tail (start + offset)).1.1 who)) :=
    tendsto_atTop_ciInf hanti hbdd
  have hswapped : Tendsto (fun offset ↦ (tail (offset + start)).1.1 who)
      atTop (nhds (⨅ offset, (tail (start + offset)).1.1 who)) := by
    apply hshifted.congr
    intro offset
    rw [Nat.add_comm start offset]
  have hvalue : Tendsto (fun time ↦ (tail time).1.1 who)
      atTop (nhds (⨅ offset, (tail (start + offset)).1.1 who)) :=
    (tendsto_add_atTop_iff_nat start).1 hswapped
  have hlimitLe : (⨅ offset, (tail (start + offset)).1.1 who) ≤
      (tail start).1.1 who := by
    simpa using ciInf_le hbdd 0
  have hlimitLt : (⨅ offset, (tail (start + offset)).1.1 who) <
      quittingPunishmentValue reward who :=
    lt_of_le_of_lt hlimitLe hviolation
  have hhazard : Tendsto (fun time ↦ 2 * quittingRewardBound reward *
      quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) who time) atTop (nhds 0) := by
    simpa using hclock.tendsto_atTop_zero.const_mul
      (2 * quittingRewardBound reward)
  have hkey : (⨅ offset, (tail (start + offset)).1.1 who) =
      reward (quittingSingletonTerminal who) who := by
    by_contra hne
    set limitValue := ⨅ offset, (tail (start + offset)).1.1 who
    set soloReward := reward (quittingSingletonTerminal who) who with hsoloDef
    have hεpos : 0 < |limitValue - soloReward| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    have hhalf : 0 < |limitValue - soloReward| / 2 := half_pos hεpos
    have hlowValue : ∀ᶠ time : ℕ in atTop,
        limitValue - |limitValue - soloReward| / 2 <
          (tail time).1.1 who :=
      hvalue.eventually (Ioi_mem_nhds (by linarith))
    have hhighValue : ∀ᶠ time : ℕ in atTop,
        (tail time).1.1 who <
          limitValue + |limitValue - soloReward| / 2 :=
      hvalue.eventually (Iio_mem_nhds (by linarith))
    have hsmall : ∀ᶠ time : ℕ in atTop,
        2 * quittingRewardBound reward *
            quittingOpponentClockCharge
              (quittingDynamicDebtTailRoots tail) who time <
          |limitValue - soloReward| / 2 :=
      hhazard.eventually (Iio_mem_nhds hhalf)
    obtain ⟨threshold, hthreshold⟩ :=
      eventually_atTop.mp ((hlowValue.and hhighValue).and hsmall)
    obtain ⟨time, htime, hquit⟩ := hsupport threshold
    obtain ⟨⟨h1, h2⟩, h3⟩ := hthreshold time htime
    have hnash := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (tail (time + 1)).1.1
        (quittingRootOfSimplex (tail time).1.2)).1 (hedge time).1.2
    have hquitPositive :
        0 < ((quittingRootOfSimplex (tail time).1.2) who true).toReal := hquit
    have hendpoint :=
      quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
        reward (tail (time + 1)).1.1
        (quittingRootOfSimplex (tail time).1.2) who hnash hquitPositive
    have hvalueEq : (tail time).1.1 who =
        quittingRootQuitPayoff reward (tail (time + 1)).1.1
          (quittingRootOfSimplex (tail time).1.2) who := by
      rw [hendpoint]
      exact congrFun (hedge time).1.1 who
    have hclose :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (tail (time + 1)).1.1 (quittingRootOfSimplex (tail time).1.2)
        who (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
    rw [← hvalueEq, ← hsoloDef] at hclose
    have hchargeEq : quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) who time =
        quittingRootOpponentAbsorptionMass
          (quittingRootOfSimplex (tail time).1.2) who := rfl
    rw [hchargeEq] at h3
    have hpair := abs_le.mp hclose
    have hnear : |limitValue - (tail time).1.1 who| <
        |limitValue - soloReward| / 2 :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have hsolo : |(tail time).1.1 who - soloReward| <
        |limitValue - soloReward| / 2 :=
      abs_sub_lt_iff.mpr ⟨by linarith [hpair.2], by linarith [hpair.1]⟩
    have hcontradiction : |limitValue - soloReward| <
        |limitValue - soloReward| :=
      calc
        |limitValue - soloReward| ≤
            |limitValue - (tail time).1.1 who| +
              |(tail time).1.1 who - soloReward| := abs_sub_le _ _ _
        _ < |limitValue - soloReward| / 2 +
              |limitValue - soloReward| / 2 := add_lt_add hnear hsolo
        _ = |limitValue - soloReward| := by ring
    exact lt_irrefl _ hcontradiction
  rw [← hkey]
  exact hlimitLt

/-- **Violation collapse.**  A boxed chronological exact dynamic-debt tail
with one punishment-floor violation and one positive debt coordinate has
summable joint absorption charge.

Otherwise the fixed violator identified by monotone propagation would carry a
summable opponent clock while the divergent joint absorption forced its own
Quit mass to diverge; the resulting cofinal own-Quit support drives the
violator's value down to a solo reward strictly below the punishment floor,
zeroing its positive-singleton debt cap and hence its entire debt column.
The positive debt then belongs to another player, whose summable opponent
clock dominates the violator's own Quit mass --- a contradiction. -/
theorem summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hviolation : ∃ start who,
      (tail start).1.1 who < quittingPunishmentValue reward who)
    (hdebt : ∃ time who, 0 < (tail time).2 who) :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail) := by
  by_contra hjoint
  obtain ⟨start, violator, hviolStart⟩ := hviolation
  have hclock :=
    summable_opponentClockCharge_of_dynamicDebtTail_floorViolation
      tail hbox hedge violator start hviolStart
  have hown : ¬ Summable (fun time ↦
      (quittingDynamicDebtTailRoots tail time violator true).toReal) := by
    intro hsum
    apply hjoint
    exact Summable.of_nonneg_of_le
      (quittingDynamicDebtTailAbsorptionCharge_nonneg tail)
      (fun time ↦
        quittingRootAbsorptionMass_le_quitProbability_add_opponentAbsorptionMass
          (quittingDynamicDebtTailRoots tail time) violator)
      (hsum.add hclock)
  have hsupport : ∀ threshold, ∃ time, threshold ≤ time ∧
      0 < (quittingDynamicDebtTailRoots tail time violator true).toReal :=
    fun threshold ↦ exists_ge_pos_of_not_summable
      (fun _ ↦ ENNReal.toReal_nonneg) hown threshold
  have hsolo :=
    quittingSingletonReward_lt_punishmentValue_of_dynamicDebtTail_quitSupport
      tail hbox hedge violator start hviolStart hsupport
  have hcap : quittingPositiveSingletonDebtCap reward violator = 0 := by
    have hmax := quittingPunishmentValue_le_max_solo reward violator
    have hsoloEq : quittingSetReward reward ({violator} : Finset ι) violator =
        reward (quittingSingletonTerminal violator) violator := by
      unfold quittingSingletonTerminal
      exact quittingSetReward_of_nonempty reward
        (Finset.singleton_nonempty violator) violator
    rw [hsoloEq] at hmax
    have hsoloNonpos :
        reward (quittingSingletonTerminal violator) violator ≤ 0 := by
      by_contra hpos
      push Not at hpos
      rw [max_eq_left hpos.le] at hmax
      linarith
    unfold quittingPositiveSingletonDebtCap
    exact max_eq_left hsoloNonpos
  have hzeroDebt : ∀ time, (tail time).2 violator = 0 := by
    intro time
    refine le_antisymm ?_ ((hbox time).2.1 violator)
    have hupper := (hbox time).2.2 violator
    rwa [hcap] at hupper
  obtain ⟨time₀, owner, howner⟩ := hdebt
  have hne : violator ≠ owner := by
    intro heq
    rw [← heq] at howner
    rw [hzeroDebt time₀] at howner
    exact lt_irrefl 0 howner
  have hclockOwner := summable_clock_of_quittingDynamicDebtTail_pos
    reward tail hbox hedge owner time₀ howner
  exact hown (Summable.of_nonneg_of_le
    (fun _ ↦ ENNReal.toReal_nonneg)
    (fun time ↦ quittingProbability_le_opponentAbsorptionMass
      (quittingDynamicDebtTailRoots tail time) hne)
    hclockOwner)

/-! ## Coordinatewise convergence to all-Continue -/

omit [DecidableEq ι] in
/-- Summable joint absorption forces every player's Quit probability to
vanish along the tail. -/
theorem quitProbability_tendsto_zero_of_summable_dynamicDebtTailAbsorptionCharge
    (tail : ℕ → QuittingDebtPoint ι)
    (hsummable : Summable (quittingDynamicDebtTailAbsorptionCharge tail))
    (who : ι) :
    Tendsto (fun time ↦
        (quittingDynamicDebtTailRoots tail time who true).toReal)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun _ ↦ ENNReal.toReal_nonneg
  · exact fun time ↦ quitProbability_le_quittingRootAbsorptionMass
      (quittingDynamicDebtTailRoots tail time) who
  · exact hsummable.tendsto_atTop_zero

omit [DecidableEq ι] in
/-- Summable joint absorption forces every player's Continue probability to
one: the displayed roots converge coordinatewise to all-Continue. -/
theorem continueProbability_tendsto_one_of_summable_dynamicDebtTailAbsorptionCharge
    (tail : ℕ → QuittingDebtPoint ι)
    (hsummable : Summable (quittingDynamicDebtTailAbsorptionCharge tail))
    (who : ι) :
    Tendsto (fun time ↦
        (quittingDynamicDebtTailRoots tail time who false).toReal)
      atTop (nhds 1) := by
  have hquit :=
    quitProbability_tendsto_zero_of_summable_dynamicDebtTailAbsorptionCharge
      tail hsummable who
  have hidentity : (fun time ↦
        (quittingDynamicDebtTailRoots tail time who false).toReal) =
      fun time ↦
        1 - (quittingDynamicDebtTailRoots tail time who true).toReal := by
    funext time
    linarith [quittingRoot_continueProbability_add_quitProbability
      (quittingDynamicDebtTailRoots tail time) who]
  rw [hidentity]
  simpa using tendsto_const_nhds.sub hquit

/-! ## The regime's extracted tail has summable absorption -/

namespace QuittingCounterexampleRegime

/-- **Unconditional collapse of the carrier alternative.**  The projectively
extracted optimized exact-debt tail of a counterexample regime has summable
joint absorption charge, unconditionally.

The regime's carrier alternative offers either summable joint absorption or
an eventual coordinatewise punishment-floor violation; but the extracted tail
carries an owner whose initial debt is at least the positive terminal gap, so
the violation horn collapses onto the summable horn by the violation-collapse
theorem.  In particular the extracted roots converge coordinatewise to
all-Continue. -/
theorem exists_terminalGapDynamicDebtTail_summableAbsorption
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι] :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      regime.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge limit) := by
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock⟩ :=
    regime.exists_terminalGapDynamicDebtTail
  refine ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock, ?_⟩
  rcases regime.summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
      limit hbox hedge with hsummable | hviolation
  · exact hsummable
  · obtain ⟨start, hstart⟩ := hviolation
    obtain ⟨player, hplayer⟩ := hstart start le_rfl
    exact
      summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt
        limit hbox hedge ⟨start, player, hplayer⟩
        ⟨0, who, lt_of_lt_of_le regime.terminalGap_pos hdebt⟩

end QuittingCounterexampleRegime

end GameTheory
