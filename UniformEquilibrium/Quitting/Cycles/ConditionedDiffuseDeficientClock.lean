/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Punishment.SoloFloorCompletion
import UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-!
# A deficient conditioned deleted clock produces a solo payoff

In the singleton-tight conditioned chronology, failure of one player-deleted
clock is not a residual obstruction.  If the normalized probability that an
opponent of `owner` quits is summable, then conditioned terminal delivery
concentrates on the singleton terminal `{owner}`.  The conditioned values
therefore converge to `quittingSoloReward reward owner`.

Since tight-boundary conditioning preserves every player's own singleton
floor, the limiting singleton vector dominates all own singleton payoffs.
The singleton-floor solo compiler and punishment completion then make that
vector a uniform-equilibrium payoff.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [DecidableEq ι] in
/-- Remaining eventual-absorption mass is nonincreasing along a root tail. -/
theorem antitone_quittingTailEventualAbsorption
    (roots : ℕ → ι → PMF Bool) :
    Antitone (quittingTailEventualAbsorption roots) := by
  apply antitone_nat_of_succ_le
  intro time
  have hstep :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  have hcharge := quittingRootAbsorptionMass_nonneg (roots time)
  have hnext :=
    quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)
  have hcontinue : quittingStationaryContinueMass (roots time) =
      1 - quittingRootAbsorptionMass (roots time) := by
    unfold quittingRootAbsorptionMass
    ring
  rw [hcontinue] at hstep
  nlinarith [mul_nonneg hcharge (sub_nonneg.mpr hnext.2)]

omit [DecidableEq ι] in
/-- The probability that an opponent eventually quits is bounded by the
unweighted sum of the one-stage opponent absorption charges. -/
theorem one_sub_quittingOpponentSurvivalLimit_le_opponentCharge
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hcharge : Summable (fun offset ↦
      quittingRootOpponentAbsorptionMass (roots (start + offset)) who)) :
    1 - quittingOpponentSurvivalLimit roots who start ≤
      ∑' offset : ℕ,
        quittingRootOpponentAbsorptionMass (roots (start + offset)) who := by
  let forced : ℕ → ι → PMF Bool := fun time ↦
    Function.update (roots time) who (PMF.pure false)
  have hforced : Summable (fun offset ↦
      quittingRootAbsorptionMass (forced (start + offset))) := by
    simpa [forced, quittingRootOpponentAbsorptionMass] using hcharge
  have hforcedEq : forced = quittingRootSequenceUpdate roots who
      (quittingPureTimeHazard none) := by
    funext time player
    rfl
  have hlimit : quittingJointSurvivalLimit forced start =
      quittingOpponentSurvivalLimit roots who start := by
    have hforcedOpponent : Tendsto
        (quittingJointSurvivalWeight forced start) atTop
        (nhds (quittingOpponentSurvivalLimit roots who start)) := by
      apply (tendsto_quittingOpponentSurvivalLimit
        roots who start).congr'
      apply Filter.Eventually.of_forall
      intro fuel
      rw [hforcedEq]
      exact
        (quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
          roots who start fuel).symm
    exact tendsto_nhds_unique
      (tendsto_quittingJointSurvivalLimit forced start)
      hforcedOpponent
  have hloss := one_sub_quittingJointSurvivalLimit_le_tailCharge
    forced start hforced
  rw [hlimit] at hloss
  simpa [forced, quittingRootOpponentAbsorptionMass] using hloss

/-- A conditioned opponent clock controls the probability of any future
opponent absorption after restoring the remaining eventual-absorption scale. -/
theorem one_sub_quittingOpponentSurvivalLimit_le_eventualAbsorption_mul_tsum
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hsummable : Summable (fun offset ↦
      quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    1 - quittingOpponentSurvivalLimit roots who start ≤
      quittingTailEventualAbsorption roots start *
        ∑' offset : ℕ,
          quittingTailConditionedOpponentWeight
            roots (start + offset) who := by
  let physical : ℕ → ℝ := fun offset ↦
    quittingRootOpponentAbsorptionMass (roots (start + offset)) who
  let conditioned : ℕ → ℝ := fun offset ↦
    quittingTailConditionedOpponentWeight roots (start + offset) who
  have hphysicalEq : ∀ offset,
      physical offset =
        quittingTailEventualAbsorption roots (start + offset) *
          conditioned offset := by
    intro offset
    dsimp only [physical, conditioned]
    unfold quittingTailConditionedOpponentWeight
    field_simp [ne_of_gt (hpositive (start + offset))]
  have hconditioned0 : ∀ offset, 0 ≤ conditioned offset := by
    intro offset
    exact quittingTailConditionedOpponentWeight_nonneg
      roots (start + offset) who (hpositive (start + offset))
  have hphysical0 : ∀ offset, 0 ≤ physical offset := by
    intro offset
    exact quittingRootAbsorptionMass_nonneg _
  have hphysicalLe : ∀ offset,
      physical offset ≤
        quittingTailEventualAbsorption roots start * conditioned offset := by
    intro offset
    rw [hphysicalEq offset]
    exact mul_le_mul_of_nonneg_right
      (antitone_quittingTailEventualAbsorption roots
        (Nat.le_add_right start offset))
      (hconditioned0 offset)
  have hphysicalSummable : Summable physical := by
    apply Summable.of_nonneg_of_le hphysical0 hphysicalLe
    exact hsummable.mul_left
      (quittingTailEventualAbsorption roots start)
  have hloss :=
    one_sub_quittingOpponentSurvivalLimit_le_opponentCharge
      roots who start hphysicalSummable
  have hsum := hphysicalSummable.tsum_le_tsum hphysicalLe
    (hsummable.mul_left (quittingTailEventualAbsorption roots start))
  calc
    1 - quittingOpponentSurvivalLimit roots who start ≤
        ∑' offset, physical offset := by
      simpa [physical] using hloss
    _ ≤ ∑' offset,
        quittingTailEventualAbsorption roots start * conditioned offset := hsum
    _ = quittingTailEventualAbsorption roots start *
        ∑' offset, conditioned offset := by rw [tsum_mul_left]
    _ = _ := by rfl

/-- Terminal payoff is close to the absorbed-mass multiple of one singleton
payoff vector, with error charged only to non-singleton absorption.  Unlike
the usual concentration theorem, no almost-sure-absorption hypothesis is
needed. -/
theorem abs_quittingTerminalPayoff_sub_absorbedMass_mul_soloReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward profile who -
        (1 - quittingLiveMassLimit reward profile) *
          quittingSoloReward reward owner who| ≤
      2 * M * quittingNonSoloMassLimit reward profile owner := by
  classical
  let singleton := quittingSingletonTerminal owner
  let mass := fun terminal =>
    quittingAbsorbedMassLimit reward profile terminal
  let solo := quittingSoloReward reward owner who
  have htotal : (∑ terminal, mass terminal) =
      1 - quittingLiveMassLimit reward profile := by
    have hconservation :=
      quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
    dsimp only [mass]
    linarith
  have hsolo : reward singleton who = solo := by
    rfl
  have hidentity :
      quittingTerminalPayoff reward profile who -
          (1 - quittingLiveMassLimit reward profile) * solo =
        ∑ terminal,
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo) := by
    calc
      quittingTerminalPayoff reward profile who -
          (1 - quittingLiveMassLimit reward profile) * solo =
        (∑ terminal, mass terminal * reward terminal who) -
          (∑ terminal, mass terminal) * solo := by rw [htotal]
      _ = ∑ terminal, mass terminal * (reward terminal who - solo) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro terminal _
        ring
      _ = ∑ terminal,
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo) := by
        apply Finset.sum_congr rfl
        intro terminal _
        by_cases hterminal : terminal = singleton
        · subst terminal
          simp [hsolo]
        · simp [hterminal]
  rw [hidentity]
  calc
    |∑ terminal,
        if terminal = singleton then 0
        else mass terminal * (reward terminal who - solo)| ≤
      ∑ terminal,
        |if terminal = singleton then 0
        else mass terminal * (reward terminal who - solo)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun terminal =>
          if terminal = singleton then 0
          else mass terminal * (reward terminal who - solo))
        Finset.univ
    _ = ∑ terminal,
        if terminal = singleton then 0
        else mass terminal * |reward terminal who - solo| := by
      apply Finset.sum_congr rfl
      intro terminal _
      by_cases hterminal : terminal = singleton
      · simp [hterminal]
      · simp only [hterminal, ↓reduceIte, abs_mul]
        rw [abs_of_nonneg]
        exact quittingAbsorbedMassLimit_nonneg reward profile terminal
    _ ≤ ∑ terminal,
        if terminal = singleton then 0
        else mass terminal * (2 * M) := by
      apply Finset.sum_le_sum
      intro terminal _
      by_cases hterminal : terminal = singleton
      · simp [hterminal]
      · simp only [hterminal, ↓reduceIte]
        apply mul_le_mul_of_nonneg_left
        · calc
            |reward terminal who - solo| ≤
                |reward terminal who| + |solo| := abs_sub _ _
            _ ≤ M + M := add_le_add (hreward terminal who) (by
              rw [← hsolo]
              exact hreward singleton who)
            _ = 2 * M := by ring
        · exact quittingAbsorbedMassLimit_nonneg reward profile terminal
    _ = 2 * M * quittingNonSoloMassLimit reward profile owner := by
      unfold quittingNonSoloMassLimit
      dsimp only [mass, singleton]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro terminal _
      by_cases hterminal : terminal = quittingSingletonTerminal owner
      · simp [hterminal]
      · simp [hterminal, mul_comm]

omit [DecidableEq ι] in
/-- The conditional all-continue mass of a behavior profile is the stationary
continue mass of its current live root. -/
theorem quittingJointContinueMass_eq_stationaryContinueMass_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass
        (quittingProfileLiveRoot reward profile time) := by
  unfold quittingJointContinueMass quittingStationaryContinueMass
    quittingProfileLiveRoot StochasticGame.stageActionDist
  rfl

omit [DecidableEq ι] in
/-- Finite live mass is exactly joint survival along the profile's canonical
live-root sequence. -/
theorem quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ time,
      quittingLiveMass reward profile time =
        quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward profile) 0 time := by
  intro time
  induction time with
  | zero => simp [quittingJointSurvivalWeight]
  | succ time ih =>
      rw [quittingLiveMass_succ,
        quittingJointSurvivalWeight_succ, ih,
        quittingJointContinueMass_eq_stationaryContinueMass_profileLiveRoot]
      simp

/-- The live-mass limit of a root-sequence profile is its joint-survival
limit at the selected starting date. -/
theorem quittingLiveMassLimit_rootSequenceProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingLiveMassLimit reward
        (quittingRootSequenceProfile reward roots start) =
      quittingJointSurvivalLimit roots start := by
  let profile := quittingRootSequenceProfile reward roots start
  have hfinite : quittingLiveMass reward profile =
      quittingJointSurvivalWeight roots start := by
    funext fuel
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
    unfold profile quittingProfileLiveRoot quittingRootSequenceProfile
    rw [quittingJointSurvivalWeight_eq_shift]
  have hlive := tendsto_quittingLiveMass reward profile
  rw [hfinite] at hlive
  exact tendsto_nhds_unique hlive
    (tendsto_quittingJointSurvivalLimit roots start)

/-- The opponent-only live-mass limit of a root-sequence profile is the
matching opponent-survival limit. -/
theorem quittingOpponentLiveMassLimit_rootSequenceProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingRootSequenceProfile reward roots start) owner) =
      quittingOpponentSurvivalLimit roots owner start := by
  let profile := quittingRootSequenceProfile reward roots start
  have hfinite : quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile owner) =
      quittingOpponentSurvivalWeight roots owner start := by
    funext fuel
    have hroot :=
      quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
        reward profile owner fuel
    symm
    simpa [profile, quittingProfileLiveRoot, quittingRootSequenceProfile,
      quittingOpponentSurvivalWeight,
      quittingFixedOpponentsContinueMass, Nat.add_assoc] using hroot
  have hlive := tendsto_quittingLiveMass reward
    (quittingOpponentOnlyProfile reward profile owner)
  rw [hfinite] at hlive
  exact tendsto_nhds_unique hlive
    (tendsto_quittingOpponentSurvivalLimit roots owner start)

/-- **Conditioned singleton concentration.**  A summable conditioned
opponent clock makes the conditioned annotation close to the owner's
singleton payoff vector.  The bound is the tail sum of that normalized clock. -/
theorem abs_quittingTailConditionedValue_sub_soloReward_le_tsum
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (owner : ι) (start : ℕ)
    (hsummable : Summable (fun offset ↦
      quittingTailConditionedOpponentWeight roots (start + offset) owner))
    (who : ι) :
    |quittingTailConditionedValue roots value boundary start who -
        quittingSoloReward reward owner who| ≤
      2 * quittingRewardBound reward *
        ∑' offset : ℕ,
          quittingTailConditionedOpponentWeight
            roots (start + offset) owner := by
  let profile := quittingRootSequenceProfile reward roots start
  have hconcentration :=
    abs_quittingTerminalPayoff_sub_absorbedMass_mul_soloReward_le
      reward profile owner who (abs_reward_le_quittingRewardBound reward)
  have hlive := quittingLiveMassLimit_rootSequenceProfile reward roots start
  have hopponent :=
    quittingOpponentLiveMassLimit_rootSequenceProfile
      reward roots owner start
  have hterminal : quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward roots who start := by
    rfl
  rw [hterminal, hlive, hopponent] at hconcentration
  have hloss :=
    one_sub_quittingOpponentSurvivalLimit_le_eventualAbsorption_mul_tsum
      roots owner start hpositive hsummable
  have hscale : 0 ≤ 2 * quittingRewardBound reward :=
    mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
  have hscaled := mul_le_mul_of_nonneg_left hloss hscale
  have hconditioned := congrFun
    (quittingTailConditionedValue_eq_terminalValue_div
      roots value boundary hpolicy
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hboundary start) who
  rw [hconditioned]
  have halgebra :
      quittingRootSequenceTerminalValue reward roots who start /
          quittingTailEventualAbsorption roots start -
          quittingSoloReward reward owner who =
        (quittingRootSequenceTerminalValue reward roots who start -
          quittingTailEventualAbsorption roots start *
            quittingSoloReward reward owner who) /
          quittingTailEventualAbsorption roots start := by
    field_simp [ne_of_gt (hpositive start)]
    ring
  rw [halgebra, abs_div, abs_of_pos (hpositive start)]
  apply (div_le_iff₀ (hpositive start)).2
  calc
    |quittingRootSequenceTerminalValue reward roots who start -
        quittingTailEventualAbsorption roots start *
          quittingSoloReward reward owner who| ≤
      2 * quittingRewardBound reward *
        (1 - quittingOpponentSurvivalLimit roots owner start) := by
      simpa [profile, quittingTailEventualAbsorption] using hconcentration
    _ ≤ 2 * quittingRewardBound reward *
        (quittingTailEventualAbsorption roots start *
          ∑' offset : ℕ,
            quittingTailConditionedOpponentWeight
              roots (start + offset) owner) := hscaled
    _ = (2 * quittingRewardBound reward *
          ∑' offset : ℕ,
            quittingTailConditionedOpponentWeight
              roots (start + offset) owner) *
        quittingTailEventualAbsorption roots start := by ring

/-- Summability of one conditioned player-deleted clock forces the entire
conditioned payoff vector to converge to that player's singleton payoff
vector. -/
theorem tendsto_quittingTailConditionedValue_soloReward_of_summable
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (owner : ι)
    (hsummable : Summable (fun time ↦
      quittingTailConditionedOpponentWeight roots time owner)) :
    ∀ who,
      Tendsto (fun time ↦
        quittingTailConditionedValue roots value boundary time who)
        atTop (nhds (quittingSoloReward reward owner who)) := by
  let clock : ℕ → ℝ := fun time ↦
    quittingTailConditionedOpponentWeight roots time owner
  have htail : Tendsto (fun start : ℕ ↦
      ∑' offset : ℕ, clock (offset + start)) atTop (nhds 0) :=
    tendsto_sum_nat_add clock
  have hscaled : Tendsto (fun start : ℕ ↦
      2 * quittingRewardBound reward *
        ∑' offset : ℕ, clock (offset + start)) atTop (nhds 0) := by
    simpa using htail.const_mul (2 * quittingRewardBound reward)
  intro who
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) ε hε
  refine ⟨threshold, fun start hstart ↦ ?_⟩
  rw [Real.dist_eq]
  have hshiftSummable : Summable (fun offset ↦
      quittingTailConditionedOpponentWeight roots (start + offset) owner) := by
    have hadd : Summable (fun offset ↦ clock (offset + start)) :=
      (summable_nat_add_iff start).2 hsummable
    simpa [clock, Nat.add_comm] using hadd
  have hbound := abs_quittingTailConditionedValue_sub_soloReward_le_tsum
    (reward := reward) roots value boundary hpolicy hboundary hpositive
      owner start hshiftSummable who
  have hclose := hthreshold start hstart
  rw [Real.dist_eq, sub_zero] at hclose
  have hnonneg : 0 ≤ 2 * quittingRewardBound reward *
      ∑' offset : ℕ, clock (offset + start) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (tsum_nonneg fun offset ↦
        quittingTailConditionedOpponentWeight_nonneg
          roots (offset + start) owner (hpositive (offset + start)))
  rw [abs_of_nonneg hnonneg] at hclose
  exact hbound.trans_lt (by simpa [clock, Nat.add_comm] using hclose)

/-- **Deficient-clock solo compiler.**  On a singleton-tight conditioned
chronology, a summable player-deleted clock makes the corresponding singleton
payoff vector a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_conditionedClock_summable
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (hpunishment : ∀ who,
      quittingPunishmentValue reward who ≤ boundary who)
    (owner : ι)
    (hsummable : Summable (fun time ↦
      quittingTailConditionedOpponentWeight roots time owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hlimit :=
    tendsto_quittingTailConditionedValue_soloReward_of_summable
      (reward := reward) roots value boundary hpolicy hboundary hpositive
        owner hsummable
  apply isUniformEquilibriumPayoff_soloReward_of_soloFloor_of_punishmentIR
    reward owner
  · intro who
    have hlower : ∀ time,
        quittingSoloBaseline reward who ≤
          quittingTailConditionedValue roots value boundary time who := by
      intro time
      exact quittingSoloBaseline_le_conditionedValue_of_tightBoundary
        roots value boundary time who (hpositive time) (htight who)
          (hsourceFloor time who)
    have hclosed := le_of_tendsto (hlimit who)
      (Filter.Eventually.of_forall hlower)
    simpa [quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using hclosed
  · exact (hpunishment owner).trans_eq (htight owner)

/-- In a game with no uniform-equilibrium payoff, every conditioned deleted
clock is therefore nonsummable on the singleton-tight floor-safe branch. -/
theorem not_summable_conditionedOpponentWeight_of_not_exists_uniformPayoff
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (hpunishment : ∀ who,
      quittingPunishmentValue reward who ≤ boundary who)
    (hnot : ¬ ∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    ∀ owner,
      ¬ Summable (fun time ↦
        quittingTailConditionedOpponentWeight roots time owner) := by
  intro owner hsummable
  apply hnot
  exact ⟨quittingSoloReward reward owner,
    isUniformEquilibriumPayoff_soloReward_of_conditionedClock_summable
      (reward := reward) roots value boundary hpolicy hboundary hpositive
        htight hsourceFloor hpunishment owner hsummable⟩

end GameTheory
