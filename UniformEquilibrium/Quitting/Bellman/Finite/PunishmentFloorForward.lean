/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationFiniteClosing

/-!
# A punishment-floor Nash--Bellman forward producer

The arbitrary compact Nash--Bellman spine admits the vacuous all-Continue
selection at the top of the reward box.  This module anchors the serial
selection instead at the coordinatewise stationary punishment value.

The key invariant is one-stage and exact.  Suppose the declared continuation
value of player `i` is at least its punishment value.  Every exact Nash root
then has current payoff at least the same punishment value.  Indeed the
punishment value is below the stationary unilateral cap of the opponents'
row.  If the cap is attained by quitting, exact root Nash dominates that pure
endpoint.  If it is attained by waiting, the Bellman continuation endpoint
is still above the punishment value.  The degenerate row in which every
opponent surely continues is handled separately by the exact empty-row cap.

Consequently predecessor iteration from the punishment vector gives one
chronological, product-realizable forward orbit of exact one-stage Nash roots,
all of whose values are individually rational.  Finite prefixes of this orbit
are the natural source packets for the existing finite-forward closing
compiler.  No convexified APS selection or public correlation is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coordinatewise behavioral punishment floor. -/
def quittingPunishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who => quittingPunishmentValue reward who

/-- The punishment floor lies in the canonical reward box. -/
theorem abs_quittingPunishmentFloor_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) :
    |quittingPunishmentFloor reward who| ≤ quittingRewardBound reward := by
  rw [abs_le]
  constructor
  · unfold quittingPunishmentFloor quittingPunishmentValue
    exact le_ciInf fun profile =>
      neg_quittingRewardBound_le_quittingBestReplyValue reward profile who
  · exact (quittingPunishmentValue_le reward who
      (quittingAlwaysContinueProfile reward)).trans
      (quittingBestReplyValue_le reward
        (quittingAlwaysContinueProfile reward) who fun deviation =>
          (le_abs_self _).trans
            (abs_quittingTerminalPayoff_le reward _ who
              (quittingRewardBound_nonneg reward)
              (abs_reward_le_quittingRewardBound reward)))

/-- Exact root Nash dominates the pure-Quit endpoint. -/
theorem quittingRootQuitPayoff_le_successor_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootQuitPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have h := hnash who (PMF.pure true)
  change quittingRootQuitPayoff reward tail root who ≤
    quittingRootSuccessorPayoff reward tail root who + 0 at h
  simpa using h

/-- Exact root Nash dominates the pure-Continue endpoint. -/
theorem quittingRootContinuePayoff_le_successor_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootContinuePayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have h := hnash who (PMF.pure false)
  change quittingRootContinuePayoff reward tail root who ≤
    quittingRootSuccessorPayoff reward tail root who + 0 at h
  simpa using h

/-- **Punishment-floor invariance.**  An exact Nash predecessor of a tail
above the punishment floor remains above that floor. -/
theorem quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (htail : quittingPunishmentValue reward who ≤ tail who)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingPunishmentValue reward who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  let c := quittingStationaryFixedOpponentsContinueMass root who
  have hc0 : 0 ≤ c := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hc1 : c ≤ 1 := quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
    reward tail root who hnash
  by_cases hdeg : c = 1
  · have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who root
    rw [quittingStationaryUnilateralCap_of_fixedOpponentsContinueMass_eq_one
      (root := root) (who := who) hdeg] at hcap
    rcases (le_max_iff.mp hcap) with hsolo | hzero
    · have hagree :=
        eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
          (root := root) (who := who) hdeg
      have hupdate : Function.update root who (PMF.pure true) =
          quittingPureSetRoot ({who} : Finset ι) := by
        funext player
        by_cases hp : player = who
        · subst player
          simp [quittingPureSetRoot]
        · simpa [Function.update_of_ne hp, quittingPureSetRoot] using
            hagree player hp
      have hquitEq :
          quittingRootQuitPayoff reward tail root who =
            reward (quittingSingletonTerminal who) who := by
        unfold quittingRootQuitPayoff
        rw [hupdate]
        simp [quittingPureSetRoot]
      rw [hquitEq] at hquit
      exact hsolo.trans hquit
    · have hagree :=
        eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
          (root := root) (who := who) hdeg
      have hupdate : Function.update root who (PMF.pure false) =
          (quittingAllContinueRoot : ι → PMF Bool) := by
        funext player
        by_cases hp : player = who
        · subst player
          simp [quittingAllContinueRoot]
        · simpa [Function.update_of_ne hp, quittingPureSetRoot_empty,
            quittingAllContinueRoot] using hagree player hp
      have hcontinueEq :
          quittingRootContinuePayoff reward tail root who = tail who := by
        unfold quittingRootContinuePayoff
        rw [hupdate]
        change quittingRootSuccessorPayoff reward tail
          (quittingAllContinueRoot : ι → PMF Bool) who = tail who
        rw [quittingRootSuccessorPayoff_allContinueRoot_eq]
      rw [hcontinueEq] at hcontinue
      exact htail.trans hcontinue
  · have hc : c < 1 := lt_of_le_of_ne hc1 hdeg
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who root
    rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
    rcases (le_max_iff.mp hcap) with hq | hw
    · have hquitEq :
          quittingRootQuitPayoff reward tail root who =
            quittingStationaryFixedOpponentsQuitValue reward root who := by
        simpa [quittingStationaryFixedOpponentsQuitValue] using
          (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward (fun _ => root) who tail 0)
      rw [hquitEq] at hquit
      exact hq.trans hquit
    · have hden : 0 < 1 - c := sub_pos.mpr hc
      have hmul :
          quittingPunishmentValue reward who * (1 - c) ≤
            quittingStationaryFixedOpponentsContinueReward reward root who :=
        (le_div_iff₀ hden).mp hw
      have hctail : c * quittingPunishmentValue reward who ≤ c * tail who :=
        mul_le_mul_of_nonneg_left htail hc0
      have hbellman :
          quittingPunishmentValue reward who ≤
            quittingStationaryFixedOpponentsContinueReward reward root who +
              c * tail who := by
        nlinarith
      have hcontinueEq :
          quittingRootContinuePayoff reward tail root who =
            quittingStationaryFixedOpponentsContinueReward reward root who +
              c * tail who := by
        simpa [c, quittingStationaryFixedOpponentsContinueReward,
          quittingStationaryFixedOpponentsContinueMass] using
          (quittingRootContinuePayoff_eq_fixedOpponents
            reward (fun _ => root) who tail 0)
      rw [hcontinueEq] at hcontinue
      exact hbellman.trans hcontinue

/-- The punishment vector as a state of the canonical finite Nash--Bellman
system. -/
def quittingPunishmentFloorState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingFiniteNashBellmanSystem reward).carrier :=
  ⟨quittingPunishmentFloor reward,
    abs_quittingPunishmentFloor_le_quittingRewardBound reward⟩

/-- Iterated exact Nash predecessors, oriented forward from the punishment
floor. -/
def quittingPunishmentFloorForwardState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ℕ → (quittingFiniteNashBellmanSystem reward).carrier
  | 0 => quittingPunishmentFloorState reward
  | time + 1 =>
      (quittingFiniteNashBellmanSystem reward).predecessor
        (quittingPunishmentFloorForwardState reward time)

/-- The selected product root on a forward predecessor edge. -/
def quittingPunishmentFloorForwardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) : ι → PMF Bool :=
  Classical.choose (show ∃ root : ι → PMF Bool,
      (quittingPunishmentFloorForwardState reward (time + 1)).1 =
        quittingRootSuccessorPayoff reward
          (quittingPunishmentFloorForwardState reward time).1 root ∧
      IsεQuittingRootNash reward
        (quittingPunishmentFloorForwardState reward time).1 0 root by
    simpa [quittingPunishmentFloorForwardState,
      quittingFiniteNashBellmanSystem] using
      (quittingFiniteNashBellmanSystem reward).predecessor_related
        (quittingPunishmentFloorForwardState reward time))

/-- Exact Bellman transport on the punishment-floor forward orbit. -/
theorem quittingPunishmentFloorForward_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    (quittingPunishmentFloorForwardState reward (time + 1)).1 =
      quittingRootSuccessorPayoff reward
        (quittingPunishmentFloorForwardState reward time).1
        (quittingPunishmentFloorForwardRoot reward time) :=
  (Classical.choose_spec (show ∃ root : ι → PMF Bool,
      (quittingPunishmentFloorForwardState reward (time + 1)).1 =
        quittingRootSuccessorPayoff reward
          (quittingPunishmentFloorForwardState reward time).1 root ∧
      IsεQuittingRootNash reward
        (quittingPunishmentFloorForwardState reward time).1 0 root by
    simpa [quittingPunishmentFloorForwardState,
      quittingFiniteNashBellmanSystem] using
      (quittingFiniteNashBellmanSystem reward).predecessor_related
        (quittingPunishmentFloorForwardState reward time))).1

/-- Exact root Nash on every selected forward edge. -/
theorem quittingPunishmentFloorForward_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) :
    IsεQuittingRootNash reward
      (quittingPunishmentFloorForwardState reward time).1 0
      (quittingPunishmentFloorForwardRoot reward time) :=
  (Classical.choose_spec (show ∃ root : ι → PMF Bool,
      (quittingPunishmentFloorForwardState reward (time + 1)).1 =
        quittingRootSuccessorPayoff reward
          (quittingPunishmentFloorForwardState reward time).1 root ∧
      IsεQuittingRootNash reward
        (quittingPunishmentFloorForwardState reward time).1 0 root by
    simpa [quittingPunishmentFloorForwardState,
      quittingFiniteNashBellmanSystem] using
      (quittingFiniteNashBellmanSystem reward).predecessor_related
        (quittingPunishmentFloorForwardState reward time))).2

/-- Every value on the selected forward orbit remains above the punishment
floor. -/
theorem quittingPunishmentFloor_le_forwardState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤
      (quittingPunishmentFloorForwardState reward time).1 who := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingPunishmentFloorForward_policy reward time]
      exact quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
        reward (quittingPunishmentFloorForwardState reward time).1
        (quittingPunishmentFloorForwardRoot reward time) who ih
        (quittingPunishmentFloorForward_isZeroNash reward time)

end GameTheory
