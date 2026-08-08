/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCapEnvelopeIdentities
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailProfileAdapter
import UniformEquilibrium.Quitting.Debt.Ledger.TruncationLedgerFold
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Deleted-tail coupling for the Never cap

This file isolates the probabilistic core of elementary tail compression.
For a player who continues through a cutoff, changing all later opponent
hazards to Continue can matter only if the opponents survive to the cutoff but
not forever.  The resulting estimate is uniform over deterministic quit times;
behavioral pure-time extremality then transfers it to the full behavioral
best-response envelope.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The opponent-only live-mass limit of a root suffix is the conditional
deleted-survival quotient. -/
theorem quittingLiveMassLimit_opponentOnly_rootSequenceProfile_eq_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingRootSequenceProfile reward roots start) who) =
      quittingOpponentSurvivalLimit roots who 0 /
        quittingOpponentSurvivalWeight roots who 0 start := by
  let tailProfile := quittingRootSequenceProfile reward roots start
  have hlive : quittingLiveMass reward
      (quittingOpponentOnlyProfile reward tailProfile who) =
      quittingOpponentSurvivalWeight roots who start := by
    funext fuel
    have hweights := quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward tailProfile who fuel
    have hroot : quittingProfileLiveRoot reward tailProfile =
        fun time => roots (start + time) := by
      dsimp [tailProfile]
      rw [quittingRootSequenceProfile_eq_shift,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    rw [hroot] at hweights
    rw [← hweights]
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_congr rfl
    intro offset _
    simp only [Nat.zero_add]
    rfl
  apply tendsto_nhds_unique
    (tendsto_quittingLiveMass reward
      (quittingOpponentOnlyProfile reward tailProfile who))
  rw [hlive]
  exact tendsto_quittingOpponentSurvivalWeight_tail roots who
    (quittingOpponentSurvivalLimit roots who 0)
    (tendsto_quittingOpponentSurvivalLimit roots who 0) hpositive start

/-- A deterministic quit at a finite time forces eventual absorption. -/
theorem quittingLiveMassLimit_rootSequenceUpdate_pureTime_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime start : ℕ)
    (hstart : start ≤ quitTime) :
    quittingLiveMassLimit reward
        (quittingRootSequenceProfile reward
          (quittingRootSequenceUpdate roots who
            (quittingPureTimeHazard (some quitTime))) start) = 0 := by
  let profile := quittingRootSequenceProfile reward
    (quittingRootSequenceUpdate roots who
      (quittingPureTimeHazard (some quitTime))) start
  have hzero : ∀ fuel, quitTime - start < fuel →
      quittingLiveMass reward profile fuel = 0 := by
    intro fuel hfuel
    dsimp [profile]
    rw [quittingRootSequenceProfile_eq_shift]
    rw [← quittingJointSurvivalWeight_eq_liveMass_rootSequence reward
      (fun time => quittingRootSequenceUpdate roots who
        (quittingPureTimeHazard (some quitTime)) (start + time)) fuel]
    rw [quittingJointSurvivalWeight_eq_prod]
    refine Finset.prod_eq_zero
      (Finset.mem_range.mpr (show quitTime - start < fuel from hfuel)) ?_
    rw [Nat.zero_add, quittingStationaryContinueMass_eq_prod_continueProbability]
    refine Finset.prod_eq_zero (Finset.mem_univ who) ?_
    rw [quittingRootSequenceUpdate]
    have htime : start + (quitTime - start) = quitTime :=
      Nat.add_sub_of_le hstart
    rw [htime, quittingPureTimeHazard_some_self]
    simp
  apply tendsto_nhds_unique (tendsto_quittingLiveMass reward profile)
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨quitTime - start + 1, fun fuel hfuel => ?_⟩
  rw [hzero fuel (by omega), dist_self]
  exact hε

/-- Conditional late-quit coupling: after a live cutoff, a finite pure quit
differs from the player's singleton reward only through later opponent
absorption. -/
theorem abs_quittingRootSequencePureTimeTerminalValue_sub_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime start : ℕ)
    (hstart : start ≤ quitTime) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequencePureTimeTerminalValue reward roots who
          (some quitTime) start - reward (quittingSingletonTerminal who) who| ≤
      2 * M * (1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingRootSequenceProfile reward roots start) who)) := by
  let profile := quittingRootSequenceProfile reward
    (quittingRootSequenceUpdate roots who
      (quittingPureTimeHazard (some quitTime))) start
  have habsorbs : quittingLiveMassLimit reward profile = 0 := by
    exact quittingLiveMassLimit_rootSequenceUpdate_pureTime_eq_zero
      reward roots who quitTime start hstart
  have hopponents : quittingOpponentOnlyProfile reward profile who =
      quittingOpponentOnlyProfile reward
        (quittingRootSequenceProfile reward roots start) who := by
    funext player time history
    by_cases hp : player = who
    · subst player
      simp [profile, quittingOpponentOnlyProfile]
    · simp [profile, quittingOpponentOnlyProfile,
        quittingRootSequenceProfile, quittingRootSequenceUpdate,
        Function.update_of_ne hp]
  have hbound :=
    abs_quittingTerminalPayoff_sub_soloReward_le_of_opponentLiveTail
      reward profile who who hM hreward habsorbs (η :=
        1 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who)) le_rfl
  rw [hopponents] at hbound
  have hpay : quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard (some quitTime))) who start := by
    rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
    dsimp [profile]
    rw [quittingRootSequenceProfile_eq_shift,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    exact (quittingRootSequenceTerminalValue_eq_shift reward _ who start).symm
  rw [hpay] at hbound
  change |quittingRootSequenceTerminalValue reward
      (quittingRootSequenceUpdate roots who
        (quittingPureTimeHazard (some quitTime))) who start -
      reward (quittingSingletonTerminal who) who| ≤ _
  have hsolo : quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := by
    unfold quittingSoloReward quittingSingletonTerminal
    congr
  rw [← hsolo]
  exact hbound

/-- Once the opponents are capped by Never, every finite late quit realizes
the singleton reward exactly. -/
theorem quittingRootSequencePureTimeTerminalValue_elementaryNever_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff quitTime : ℕ}
    (hquit : cutoff ≤ quitTime) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingElementaryTailRoots roots cutoff (.never)) who
        (some quitTime) cutoff =
      reward (quittingSingletonTerminal who) who := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le hquit
  have hall : ∀ time, cutoff ≤ time →
      quittingElementaryTailRoots roots cutoff (.never) time =
        quittingAllContinueRoot := by
    intro time htime
    exact quittingTruncatedRoots_of_le roots htime
  have hpure : ∀ (sequence : ℕ → ι → PMF Bool) (start fuel : ℕ),
      (∀ time, start ≤ time → sequence time = quittingAllContinueRoot) →
      quittingRootSequencePureTimeTerminalValue reward sequence who
          (some (start + fuel)) start =
        reward (quittingSingletonTerminal who) who := by
    intro sequence start fuel
    induction fuel generalizing start with
  | zero =>
      intro hsequence
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp only [Nat.add_zero]
      rw [quittingPureTimeHazard_some_self]
      simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, one_mul,
        Bool.false_eq_true, ENNReal.toReal_zero, zero_mul, add_zero]
      unfold quittingFixedOpponentsQuitValue
      rw [hsequence start le_rfl]
      change quittingStationaryFixedOpponentsQuitValue reward
        quittingAllContinueRoot who = _
      rw [show quittingAllContinueRoot =
        quittingSoloStationaryRoot who (PMF.pure false) by
          funext player
          simp [quittingAllContinueRoot, quittingSoloStationaryRoot]]
      have hsolo := quittingStationaryFixedOpponentsQuitValue_solo_owner
        reward who (PMF.pure false)
      rw [hsolo]
      unfold quittingSoloReward quittingSingletonTerminal
      congr
  | succ fuel ih =>
      intro hsequence
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      rw [quittingPureTimeHazard_some_of_ne (show start ≠ start + (fuel + 1) by omega)]
      simp only [PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      have hcontinueReward :
          quittingFixedOpponentsContinueReward reward sequence who start = 0 := by
        unfold quittingFixedOpponentsContinueReward
        rw [hsequence start le_rfl]
        change quittingStationaryFixedOpponentsContinueReward reward
          quittingAllContinueRoot who = 0
        rw [show quittingAllContinueRoot =
          quittingSoloStationaryRoot who (PMF.pure false) by
            funext player
            simp [quittingAllContinueRoot, quittingSoloStationaryRoot]]
        simp
      have hcontinueMass :
          quittingFixedOpponentsContinueMass sequence who start = 1 := by
        unfold quittingFixedOpponentsContinueMass
        rw [hsequence start le_rfl]
        change quittingStationaryFixedOpponentsContinueMass
          quittingAllContinueRoot who = 1
        rw [show quittingAllContinueRoot =
          quittingSoloStationaryRoot who (PMF.pure false) by
            funext player
            simp [quittingAllContinueRoot, quittingSoloStationaryRoot]]
        simp
      rw [hcontinueReward, hcontinueMass, zero_add, one_mul]
      change quittingRootSequencePureTimeTerminalValue reward sequence who
        (some (start + (fuel + 1))) (start + 1) = _
      rw [show start + (fuel + 1) = (start + 1) + fuel by omega]
      exact ih (start := start + 1)
        (fun time htime => hsequence time (by omega))
  exact hpure _ cutoff fuel hall

/-- Sharp fixed-atom coupling for every finite quit time at or after the
cutoff.  The error is precisely charged to deleted survival lost after the
cutoff. -/
theorem abs_quittingRootSequencePureTimeTerminalValue_sub_elementaryNever_le_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {cutoff quitTime : ℕ}
    (hquit : cutoff ≤ quitTime) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequencePureTimeTerminalValue reward roots who
          (some quitTime) 0 -
        quittingRootSequencePureTimeTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who
          (some quitTime) 0| ≤
      2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
  let capped := quittingElementaryTailRoots roots cutoff (.never)
  let hazard := quittingPureTimeHazard (some quitTime)
  let x := quittingRootSequenceUpdate roots who hazard
  let y := quittingRootSequenceUpdate capped who hazard
  have hprefix : ∀ time, time < cutoff → x time = y time := by
    intro time htime
    dsimp [x, y]
    rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate]
    rw [show capped time = roots time by
      exact quittingElementaryTailRoots_of_lt roots (.never) htime]
  have hscaled := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward x y who cutoff hprefix
  have hsurvival : quittingJointSurvivalWeight y 0 cutoff =
      quittingOpponentSurvivalWeight roots who 0 cutoff := by
    rw [quittingJointSurvivalWeight_eq_prod]
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_congr rfl
    intro offset hoffset
    have hoffsetLt : offset < cutoff := Finset.mem_range.mp hoffset
    dsimp [y, capped, hazard]
    rw [Nat.zero_add, quittingRootSequenceUpdate,
      quittingPureTimeHazard_some_of_ne (show offset ≠ quitTime by omega),
      quittingTruncatedRoots_of_lt roots hoffsetLt]
    rfl
  have htailOriginal :
      |quittingRootSequenceTerminalValue reward x who cutoff -
          reward (quittingSingletonTerminal who) who| ≤
        2 * M * (1 - quittingOpponentSurvivalLimit roots who 0 /
          quittingOpponentSurvivalWeight roots who 0 cutoff) := by
    have hbound := abs_quittingRootSequencePureTimeTerminalValue_sub_singleton_le
      reward roots who quitTime cutoff hquit hM hreward
    rw [quittingLiveMassLimit_opponentOnly_rootSequenceProfile_eq_ratio
      reward roots who cutoff hpositive] at hbound
    simpa [x, hazard, quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue] using hbound
  have htailCapped : quittingRootSequenceTerminalValue reward y who cutoff =
      reward (quittingSingletonTerminal who) who := by
    dsimp [y, capped, hazard]
    simpa [quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue] using
      (quittingRootSequencePureTimeTerminalValue_elementaryNever_of_le
        reward roots who hquit)
  have hprefixPos : 0 < quittingOpponentSurvivalWeight roots who 0 cutoff :=
    quittingOpponentSurvivalWeight_pos_of_limit_pos roots who
      (quittingOpponentSurvivalLimit roots who 0)
      (tendsto_quittingOpponentSurvivalLimit roots who 0) hpositive cutoff
  rw [htailCapped] at hscaled
  change |quittingRootSequenceTerminalValue reward x who 0 -
      quittingRootSequenceTerminalValue reward y who 0| ≤ _
  rw [hscaled, hsurvival, abs_mul, abs_of_pos hprefixPos]
  calc
    quittingOpponentSurvivalWeight roots who 0 cutoff *
        |quittingRootSequenceTerminalValue reward x who cutoff -
          reward (quittingSingletonTerminal who) who| ≤
      quittingOpponentSurvivalWeight roots who 0 cutoff *
        (2 * M * (1 - quittingOpponentSurvivalLimit roots who 0 /
          quittingOpponentSurvivalWeight roots who 0 cutoff)) :=
      mul_le_mul_of_nonneg_left htailOriginal hprefixPos.le
    _ = 2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
      field_simp [hprefixPos.ne']

/-- Conditional Never payoff is paid only by eventual opponent absorption. -/
theorem abs_quittingRootSequencePureTimeTerminalValue_none_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequencePureTimeTerminalValue reward roots who none start| ≤
      M * (1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingRootSequenceProfile reward roots start) who)) := by
  let profile := quittingRootSequenceProfile reward roots start
  have hbound := abs_quittingTerminalPayoff_update_never_le_opponentTail
    reward profile who hreward
  have hpay : quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who none)) who =
      quittingRootSequencePureTimeTerminalValue reward roots who none start := by
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    dsimp [profile]
    rw [quittingRootSequenceProfile_eq_shift,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    unfold quittingRootSequencePureTimeTerminalValue
      quittingRootSequenceHazardTerminalValue
    rw [quittingRootSequenceTerminalValue_eq_shift reward
      (quittingRootSequenceUpdate roots who (quittingPureTimeHazard none))
      who start]
    congr 2
  rw [hpay] at hbound
  exact hbound

/-- Sharp coupling for the Never pure-time atom. -/
theorem abs_quittingRootSequencePureTimeTerminalValue_none_sub_elementaryNever_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
        quittingRootSequencePureTimeTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who none 0| ≤
      2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
  let capped := quittingElementaryTailRoots roots cutoff (.never)
  let x := quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard
  let y := quittingRootSequenceUpdate capped who quittingAlwaysContinueHazard
  have hprefix : ∀ time, time < cutoff → x time = y time := by
    intro time htime
    dsimp [x, y]
    rw [quittingRootSequenceUpdate, quittingRootSequenceUpdate]
    rw [show capped time = roots time by
      exact quittingElementaryTailRoots_of_lt roots (.never) htime]
  have hscaled := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward x y who cutoff hprefix
  have hsurvival : quittingJointSurvivalWeight y 0 cutoff =
      quittingOpponentSurvivalWeight roots who 0 cutoff := by
    dsimp [y]
    rw [quittingJointSurvivalWeight_quittingRootSequenceUpdate_alwaysContinue]
    exact quittingOpponentSurvivalWeight_elementaryTailRoots_plan
      roots cutoff (.never) who
  have htailOriginal : |quittingRootSequenceTerminalValue reward x who cutoff| ≤
      M * (1 - quittingOpponentSurvivalLimit roots who 0 /
        quittingOpponentSurvivalWeight roots who 0 cutoff) := by
    have hbound := abs_quittingRootSequencePureTimeTerminalValue_none_le
      reward roots who cutoff hreward
    rw [quittingLiveMassLimit_opponentOnly_rootSequenceProfile_eq_ratio
      reward roots who cutoff hpositive] at hbound
    have hhazard : quittingPureTimeHazard none = quittingAlwaysContinueHazard := by
      funext time
      rfl
    unfold quittingRootSequencePureTimeTerminalValue
      quittingRootSequenceHazardTerminalValue at hbound
    rw [hhazard] at hbound
    simpa [x] using hbound
  have htailCapped : quittingRootSequenceTerminalValue reward y who cutoff = 0 := by
    apply quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    intro time htime
    dsimp [y, capped]
    rw [quittingRootSequenceUpdate, quittingTruncatedRoots_of_le roots htime]
    simp [quittingAlwaysContinueHazard, quittingAllContinueRoot]
  have hprefixPos : 0 < quittingOpponentSurvivalWeight roots who 0 cutoff :=
    quittingOpponentSurvivalWeight_pos_of_limit_pos roots who
      (quittingOpponentSurvivalLimit roots who 0)
      (tendsto_quittingOpponentSurvivalLimit roots who 0) hpositive cutoff
  rw [htailCapped, sub_zero] at hscaled
  change |quittingRootSequenceTerminalValue reward x who 0 -
      quittingRootSequenceTerminalValue reward y who 0| ≤ _
  rw [hscaled, hsurvival, abs_mul, abs_of_pos hprefixPos]
  calc
    quittingOpponentSurvivalWeight roots who 0 cutoff *
        |quittingRootSequenceTerminalValue reward x who cutoff| ≤
      quittingOpponentSurvivalWeight roots who 0 cutoff *
        (M * (1 - quittingOpponentSurvivalLimit roots who 0 /
          quittingOpponentSurvivalWeight roots who 0 cutoff)) :=
      mul_le_mul_of_nonneg_left htailOriginal hprefixPos.le
    _ = M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
      field_simp [hprefixPos.ne']
    _ ≤ 2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
      have hdrop : 0 ≤ quittingOpponentSurvivalWeight roots who 0 cutoff -
          quittingOpponentSurvivalLimit roots who 0 := sub_nonneg.mpr
        (quittingOpponentSurvivalLimit_le_prefix roots who
          (quittingOpponentSurvivalLimit roots who 0)
          (tendsto_quittingOpponentSurvivalLimit roots who 0) cutoff)
      nlinarith

/-- Uniform sharp coupling over all deterministic quit times, including
Never. -/
theorem abs_quittingRootSequencePureTimeTerminalValue_sub_elementaryNever_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (quitTime : Option ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 -
        quittingRootSequencePureTimeTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who quitTime 0| ≤
      2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
  cases quitTime with
  | none =>
      exact abs_quittingRootSequencePureTimeTerminalValue_none_sub_elementaryNever_le
        reward roots who cutoff hM hreward hpositive
  | some quitTime =>
      by_cases hquit : quitTime < cutoff
      · have heq := quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_lt
          reward roots who hquit
        rw [show quittingElementaryTailRoots roots cutoff (.never) =
          quittingTruncatedRoots roots cutoff from rfl, heq, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hM)
          (sub_nonneg.mpr (quittingOpponentSurvivalLimit_le_prefix roots who
            (quittingOpponentSurvivalLimit roots who 0)
            (tendsto_quittingOpponentSurvivalLimit roots who 0) cutoff))
      · exact
          abs_quittingRootSequencePureTimeTerminalValue_sub_elementaryNever_le_of_le
            reward roots who (Nat.le_of_not_gt hquit) hM hreward hpositive

/-- Literal all-behavior best-response envelopes inherit the sharp coupling
estimate.  The proof uses exact behavioral pure-time extremality on both root
words. -/
theorem abs_quittingRootSequenceBestResponseValue_sub_elementaryNever_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who| ≤
      2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0) := by
  let capped := quittingElementaryTailRoots roots cutoff (.never)
  let error := 2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
    quittingOpponentSurvivalLimit roots who 0)
  let xValue := fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0
  let yValue := fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward capped who quitTime 0
  have hpoint : ∀ quitTime, |xValue quitTime - yValue quitTime| ≤ error := by
    intro quitTime
    exact abs_quittingRootSequencePureTimeTerminalValue_sub_elementaryNever_le
      reward roots who cutoff quitTime hM hreward hpositive
  have hxBound : BddAbove (Set.range xValue) :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue
      reward roots who hM hreward
  have hyBound : BddAbove (Set.range yValue) :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue
      reward capped who hM hreward
  have hxy : sSup (Set.range xValue) ≤ sSup (Set.range yValue) + error := by
    apply csSup_le
    · exact ⟨xValue none, ⟨none, rfl⟩⟩
    · rintro _ ⟨quitTime, rfl⟩
      have hy := le_csSup hyBound ⟨quitTime, rfl⟩
      have hp := hpoint quitTime
      linarith [le_abs_self (xValue quitTime - yValue quitTime)]
  have hyx : sSup (Set.range yValue) ≤ sSup (Set.range xValue) + error := by
    apply csSup_le
    · exact ⟨yValue none, ⟨none, rfl⟩⟩
    · rintro _ ⟨quitTime, rfl⟩
      have hx := le_csSup hxBound ⟨quitTime, rfl⟩
      have hp := hpoint quitTime
      linarith [neg_le_abs (xValue quitTime - yValue quitTime)]
  rw [show quittingRootSequenceBestResponseValue reward roots who =
      sSup (Set.range xValue) by
    unfold quittingRootSequenceBestResponseValue
      quittingContinuationBestResponseValue
    rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward (quittingRootSequenceProfile reward roots 0) who hM hreward]
    simp only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    rfl,
    show quittingRootSequenceBestResponseValue reward capped who =
      sSup (Set.range yValue) by
    unfold quittingRootSequenceBestResponseValue
      quittingContinuationBestResponseValue
    rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward (quittingRootSequenceProfile reward capped 0) who hM hreward]
    simp only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    rfl]
  rw [abs_le]
  constructor <;> linarith

/-- Positive deleted survival makes Never-capped prefixes converge in the
literal behavioral best-response envelope. -/
theorem tendsto_quittingRootSequenceBestResponseValue_elementaryNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    Tendsto (fun cutoff => quittingRootSequenceBestResponseValue reward
        (quittingElementaryTailRoots roots cutoff (.never)) who)
      atTop (nhds (quittingRootSequenceBestResponseValue reward roots who)) := by
  have hmajorant : Tendsto (fun cutoff =>
      2 * M * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0)) atTop (nhds 0) := by
    have hsub := (tendsto_quittingOpponentSurvivalLimit roots who 0).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => quittingOpponentSurvivalLimit roots who 0) atTop
        (nhds (quittingOpponentSurvivalLimit roots who 0)))
    simpa using hsub.const_mul (2 * M)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hmajorant) ε hε
  refine ⟨threshold, fun cutoff hcutoff => ?_⟩
  have hbound := abs_quittingRootSequenceBestResponseValue_sub_elementaryNever_le
    reward roots who cutoff hM hreward hpositive
  have hclose := hthreshold cutoff hcutoff
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hclose
  · rw [Real.dist_eq]
    exact lt_of_le_of_lt (by simpa [abs_sub_comm] using hbound) hclose
  · exact mul_nonneg (mul_nonneg (by norm_num) hM)
      (sub_nonneg.mpr (quittingOpponentSurvivalLimit_le_prefix roots who
        (quittingOpponentSurvivalLimit roots who 0)
        (tendsto_quittingOpponentSurvivalLimit roots who 0) cutoff))

/-- Positive joint survival implies positive deleted survival for every
player. -/
theorem quittingOpponentSurvivalLimit_pos_of_joint_pos
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hpositive : 0 < quittingJointSurvivalLimit roots 0) :
    0 < quittingOpponentSurvivalLimit roots who 0 := by
  have hle : quittingJointSurvivalLimit roots 0 ≤
      quittingOpponentSurvivalLimit roots who 0 := by
    apply le_of_tendsto_of_tendsto
      (tendsto_quittingJointSurvivalLimit roots 0)
      (tendsto_quittingOpponentSurvivalLimit roots who 0)
    exact Filter.Eventually.of_forall fun fuel =>
      quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        roots who 0 fuel
  exact hpositive.trans_le hle

/-- One Never cap and one cutoff simultaneously approximate prescribed values
and all behavioral envelopes in the positive-joint-survival branch. -/
theorem exists_elementaryNever_terminalPair_close_of_joint_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingJointSurvivalLimit roots 0) :
    ∃ cutoff,
      (∀ who, |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who 0| < ε) ∧
      (∀ who, |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who| < ε) := by
  have hp : ∀ᶠ cutoff : ℕ in atTop, ∀ who,
      |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who 0| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_quittingRootSequenceTerminalValue_elementaryNever
        reward roots who hM hreward hpositive) ε hε
    exact eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
      simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
  have hb : ∀ᶠ cutoff : ℕ in atTop, ∀ who,
      |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.never)) who| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_quittingRootSequenceBestResponseValue_elementaryNever
        reward roots who hM hreward
          (quittingOpponentSurvivalLimit_pos_of_joint_pos roots who hpositive)) ε hε
    exact eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
      simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.and hb)
  exact ⟨N, hN N le_rfl⟩

/-- In the unique-positive-deleted-clock branch, one sure-solo cap owned by
that player simultaneously approximates every prescribed value and every
behavioral envelope. -/
theorem exists_elementarySureSolo_terminalPair_close_of_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hjoint : quittingJointSurvivalLimit roots 0 = 0)
    (howner : 0 < quittingOpponentSurvivalLimit roots owner 0)
    (hunique : ∀ who,
      0 < quittingOpponentSurvivalLimit roots who 0 → who = owner) :
    ∃ cutoff,
      (∀ who, |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who 0| < ε) ∧
      (∀ who, |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who| < ε) := by
  have hp : ∀ᶠ cutoff : ℕ in atTop, ∀ who,
      |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who 0| < ε := by
    have hmajorant : Tendsto (fun cutoff =>
        2 * M * quittingJointSurvivalWeight roots 0 cutoff) atTop (nhds 0) := by
      simpa [hjoint] using
        (tendsto_quittingJointSurvivalLimit roots 0).const_mul (2 * M)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmajorant ε hε
    exact eventually_atTop.mpr ⟨N, fun cutoff hcutoff who => by
      have hbound := abs_quittingRootSequenceTerminalValue_sub_elementarySureSolo_le
        reward roots owner who cutoff hM hreward
      have hclose := hN cutoff hcutoff
      rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hclose
      · exact lt_of_le_of_lt hbound hclose
      · exact mul_nonneg (mul_nonneg (by norm_num) hM)
          (quittingJointSurvivalWeight_nonneg roots 0 cutoff)⟩
  have hb : ∀ᶠ cutoff : ℕ in atTop, ∀ who,
      |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    by_cases hwho : who = owner
    · subst who
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
        (tendsto_quittingRootSequenceBestResponseValue_elementaryNever
          reward roots owner hM hreward howner) ε hε
      exact eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        rw [quittingRootSequenceBestResponseValue_elementarySureSolo_owner_eq_never]
        simpa [Real.dist_eq, abs_sub_comm] using hN cutoff hcutoff⟩
    · have hzero : quittingOpponentSurvivalLimit roots who 0 = 0 := by
        apply le_antisymm _ (quittingOpponentSurvivalLimit_nonneg roots who 0)
        by_contra hnot
        have hpos : 0 < quittingOpponentSurvivalLimit roots who 0 :=
          lt_of_not_ge hnot
        exact hwho (hunique who hpos)
      have hmajorant : Tendsto (fun cutoff =>
          2 * M * quittingOpponentSurvivalWeight roots who 0 cutoff)
          atTop (nhds 0) := by
        simpa [hzero] using
          (tendsto_quittingOpponentSurvivalLimit roots who 0).const_mul (2 * M)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmajorant ε hε
      exact eventually_atTop.mpr ⟨N, fun cutoff hcutoff => by
        have hbound :=
          abs_quittingRootSequenceBestResponseValue_sub_elementarySureSolo_le
            reward roots owner who cutoff hM hreward
        have hclose := hN cutoff hcutoff
        rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hclose
        · exact lt_of_le_of_lt hbound hclose
        · exact mul_nonneg (mul_nonneg (by norm_num) hM)
            (quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.and hb)
  exact ⟨N, hN N le_rfl⟩

/-- Three-case elementary semantic density.  One elementary cap and one
cutoff co-realize, for all players, both the prescribed tail value and the
literal all-behavior best-response envelope to arbitrary accuracy. -/
theorem exists_elementaryTailCap_terminalPair_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      (∀ who, |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff cap) who 0| < ε) ∧
      (∀ who, |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff cap) who| < ε) := by
  rcases quittingSurvivalLimit_trichotomy reward roots with
    hpositive | ⟨hjoint, hall | hunique⟩
  · obtain ⟨cutoff, hp, hb⟩ :=
      exists_elementaryNever_terminalPair_close_of_joint_pos
        reward roots hM hε hreward hpositive
    exact ⟨.never, cutoff, hp, hb⟩
  · obtain ⟨cutoff, hp, hb⟩ := exists_elementarySureJoint_terminalPair_close
      reward roots hM hε hreward hjoint hall
    exact ⟨.sureJoint, cutoff, hp, hb⟩
  · obtain ⟨owner, howner, hownerUnique⟩ := hunique
    obtain ⟨cutoff, hp, hb⟩ :=
      exists_elementarySureSolo_terminalPair_close_of_unique
        reward roots owner hM hε hreward hjoint howner hownerUnique
    exact ⟨.sureSolo owner, cutoff, hp, hb⟩

end GameTheory
