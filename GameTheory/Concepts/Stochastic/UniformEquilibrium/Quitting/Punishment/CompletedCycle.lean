/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.CycleIsolatedCoordinate
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-!
# Punishment-completed absorbing cycles

The existing admissible-cycle compiler repeats an exact absorbing cycle
forever.  At a coordinate whose opponents are silent throughout the cycle,
that profile leaves the deviation "continue forever" unpunished and therefore
requires a nonnegative singleton payoff.

This file replaces that passive continuation by the exact quitting punishment
value.  An absorbing cycle is **punishment-admissible** at `who` when either
its deleted survival product contracts, or

`quittingPunishmentValue reward who ≤ reward {who} who`.

At most one coordinate of an absorbing cycle can fail to contract.  When such
an isolated coordinate exists, the construction repeats the cycle for a long
finite prefix and then switches to a near-optimal stationary punishment of that
coordinate.  The coupled phase-switch estimate keeps the negative singleton
anchor attached to the survival coefficient.  Every other coordinate is
controlled by comparison with the exact infinite cyclic profile; the suffix
replacement is reached with vanishing opponent-survival probability.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The corrected admissibility predicate -/

/-- A cyclic coordinate is punishment-admissible when its deleted survival
contracts, or its exact quitting punishment value is no larger than its solo
exit payoff. -/
def IsQuittingCyclePunishmentAdmissibleAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (who : ι) : Prop :=
  (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1 ∨
    quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who

/-- Punishment-admissibility at every coordinate. -/
def IsQuittingCyclePunishmentAdmissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) : Prop :=
  ∀ who : ι, IsQuittingCyclePunishmentAdmissibleAt reward cycle who

/-- The old nonnegative-solo admissibility condition is a special case of
punishment-admissibility. -/
theorem isQuittingCyclePunishmentAdmissible_of_admissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (hadmissible : IsQuittingCycleAdmissible reward cycle) :
    IsQuittingCyclePunishmentAdmissible reward cycle := by
  intro who
  rcases hadmissible who with hcontracts | hsolo
  · exact Or.inl hcontracts
  · right
    have hchi := quittingPunishmentValue_le_max_solo reward who
    have hset : quittingSetReward reward ({who} : Finset ι) who =
        reward (quittingSingletonTerminal who) who := by
      rw [quittingSetReward_of_nonempty reward
        (Finset.singleton_nonempty who)]
      rfl
    rw [hset, max_eq_left hsolo] at hchi
    exact hchi

/-! ## Noncontraction is isolation -/

/-- If the deleted one-turn product does not contract, every phase is isolated
at that coordinate. -/
theorem isQuittingIsolatedRoot_of_not_cycleContracts
    (cycle : Fin K → ι → PMF Bool) (who : ι)
    (hnot : ¬ (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1)
    (phase : Fin K) :
    IsQuittingIsolatedRoot (cycle phase) who := by
  let coefficient : Fin K → ℝ := fun p =>
    quittingStationaryFixedOpponentsContinueMass (cycle p) who
  have hnonneg : ∀ p, 0 ≤ coefficient p := fun p =>
    quittingStationaryFixedOpponentsContinueMass_nonneg (cycle p) who
  have hle : ∀ p, coefficient p ≤ 1 := fun p =>
    quittingStationaryFixedOpponentsContinueMass_le_one (cycle p) who
  have hprodLe : (∏ p : Fin K, coefficient p) ≤ 1 :=
    Finset.prod_le_one (fun p _ => hnonneg p) (fun p _ => hle p)
  have hprodEq : (∏ p : Fin K, coefficient p) = 1 :=
    le_antisymm hprodLe (not_lt.mp hnot)
  have hfactor : coefficient phase = 1 :=
    eq_one_of_prod_eq_one_of_mem
      (fun p _ => hnonneg p) (fun p _ => hle p) hprodEq
      (Finset.mem_univ phase)
  apply isQuittingIsolatedRoot_of_deletedContinueMass_eq_one
  change quittingStationaryFixedOpponentsContinueMass (cycle phase) who = 1
  exact hfactor

omit [DecidableEq ι] in
/-- A strict joint one-turn contraction has an actually absorbing phase. -/
theorem exists_cycle_phase_continueMass_lt_one
    (cycle : Fin K → ι → PMF Bool)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1) :
    ∃ phase : Fin K, quittingStationaryContinueMass (cycle phase) < 1 := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ phase : Fin K,
      quittingStationaryContinueMass (cycle phase) = 1 := by
    intro phase
    exact le_antisymm
      (quittingStationaryContinueMass_le_one (cycle phase))
      (hnone phase)
  have hprod : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) = 1 := by
    apply Finset.prod_eq_one
    intro phase _
    exact hall phase
  rw [hprod] at habsorb
  exact (lt_irrefl 1) habsorb

/-- An absorbing cycle has at most one noncontracting coordinate. -/
theorem eq_of_not_cycleContracts
    (cycle : Fin K → ι → PMF Bool)
    (habsorb : (∏ phase : Fin K,
      quittingStationaryContinueMass (cycle phase)) < 1)
    {first second : ι}
    (hfirst : ¬ (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) first) < 1)
    (hsecond : ¬ (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) second) < 1) :
    first = second := by
  obtain ⟨phase, hphase⟩ := exists_cycle_phase_continueMass_lt_one cycle habsorb
  have habsorbPhase : 0 < quittingRootAbsorptionMass (cycle phase) := by
    rw [quittingRootAbsorptionMass]
    linarith
  exact eq_of_isQuittingIsolatedRoot_of_absorbing
    (isQuittingIsolatedRoot_of_not_cycleContracts cycle first hfirst phase)
    (isQuittingIsolatedRoot_of_not_cycleContracts cycle second hsecond phase)
    habsorbPhase

/-! ## Isolated-prefix accounting -/

/-- Along a finite prefix where all opponents of `who` continue surely, every
absorption pays the same singleton reward.  The truncated deviated payoff is
therefore exactly `(1 - survival) * solo`. -/
theorem quittingRootSequenceHazardTerminalValue_truncated_eq_one_sub_survival_mul_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (hiso : ∀ time, time < cutoff → IsQuittingIsolatedRoot (roots time) who) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots roots cutoff) who
        (quittingTruncatedHazard hazard cutoff) 0 =
      (1 - quittingJointSurvivalWeight
          (quittingRootSequenceUpdate roots who hazard) 0 cutoff) *
        reward (quittingSingletonTerminal who) who := by
  unfold quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceUpdate_quittingTruncatedRoots,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  let updated := quittingRootSequenceUpdate roots who hazard
  have hstage : ∀ time, time < cutoff →
      quittingRootAbsorbingContribution reward (updated time) who =
        (1 - quittingStationaryContinueMass (updated time)) *
          reward (quittingSingletonTerminal who) who := by
    intro time htime
    have hroot : updated time =
        quittingSoloStationaryRoot who (hazard time) := by
      have hbase : updated time =
          quittingSoloStationaryRoot who (updated time who) :=
        eq_quittingSoloStationaryRoot_of_others_continue (by
          intro other hother
          unfold updated quittingRootSequenceUpdate
          rw [Function.update_of_ne hother]
          exact hiso time htime other hother)
      simpa [updated, quittingRootSequenceUpdate] using hbase
    rw [hroot, quittingRootAbsorbingContribution_solo,
      quittingStationaryContinueMass_solo, quittingSoloReward_self]
    have hmass := quittingSoloHazardMass_add (hazard time)
    have hquit : 1 - ((hazard time) false).toReal =
        ((hazard time) true).toReal := by
      linarith
    rw [hquit]
  calc
    (∑ offset ∈ Finset.range cutoff,
        quittingJointSurvivalWeight updated 0 offset *
          quittingRootAbsorbingContribution reward (updated offset) who) =
      ∑ offset ∈ Finset.range cutoff,
        (quittingJointSurvivalWeight updated 0 offset *
          (1 - quittingStationaryContinueMass (updated offset))) *
            reward (quittingSingletonTerminal who) who := by
      apply Finset.sum_congr rfl
      intro offset hoffset
      rw [hstage offset (Finset.mem_range.mp hoffset)]
      ring
    _ = (∑ offset ∈ Finset.range cutoff,
        quittingJointSurvivalWeight updated 0 offset *
          (1 - quittingStationaryContinueMass (updated offset))) *
            reward (quittingSingletonTerminal who) who := by
      rw [Finset.sum_mul]
    _ = (1 - quittingJointSurvivalWeight updated 0 cutoff) *
          reward (quittingSingletonTerminal who) who := by
      have htel :=
        sum_quittingJointSurvivalWeight_mul_one_sub_continueMass updated 0 cutoff
      simp only [zero_add] at htel
      rw [htel]

/-! ## Cyclic joint survival and isolated values -/

omit [DecidableEq ι] in
/-- Joint survival along a cyclic root sequence is the corresponding cyclic
prefix product of joint continue masses. -/
theorem quittingJointSurvivalWeight_cyclicRootSequence
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (fuel : ℕ) :
    quittingJointSurvivalWeight
        (quittingCyclicRootSequence cycle phase) 0 fuel =
      quittingCyclicPrefixWeight
        (fun cyclePhase =>
          quittingStationaryContinueMass (cycle cyclePhase)) phase fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold quittingCyclicPrefixWeight
  apply Finset.prod_congr rfl
  intro offset _
  simp [quittingCyclicRootSequence]

omit [DecidableEq ι] in
/-- Strict joint contraction around one turn makes cyclic joint survival tend
to zero. -/
theorem tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1) :
    Tendsto (quittingJointSurvivalWeight
      (quittingCyclicRootSequence cycle phase) 0) atTop (nhds 0) := by
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  have hcoefficient0 : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg (cycle cyclePhase)
  have hcoefficient1 : ∀ cyclePhase, coefficient cyclePhase ≤ 1 :=
    fun cyclePhase => quittingStationaryContinueMass_le_one (cycle cyclePhase)
  have hprefix := tendsto_zero_quittingCyclicPrefixWeight coefficient
    hcoefficient0 hcoefficient1 habsorb phase
  convert hprefix using 1
  funext fuel
  exact quittingJointSurvivalWeight_cyclicRootSequence cycle phase fuel

omit [DecidableEq ι] in
/-- The displayed value of an exact isolated absorbing cycle equals the
isolated player's singleton reward at every phase. -/
theorem quittingCyclicValue_eq_soloReward_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (who : ι)
    (hiso : ∀ cyclePhase, IsQuittingIsolatedRoot (cycle cyclePhase) who)
    (phase : Fin K) :
    value phase who = reward (quittingSingletonTerminal who) who := by
  let roots := quittingCyclicRootSequence cycle phase
  let pathValue : ℕ → Payoff ι := fun time =>
    value (quittingCyclicOrbit phase time)
  have hpath : ∀ time, time < K →
      pathValue time = quittingRootSuccessorPayoff reward
        (pathValue (time + 1)) (roots time) := by
    intro time _
    dsimp only [pathValue, roots, quittingCyclicRootSequence]
    rw [hpolicy (quittingCyclicOrbit phase time),
      quittingCyclicOrbit_succ]
  have hisoWindow : IsQuittingIsolatedWindow roots who K := by
    intro time _
    exact hiso (quittingCyclicOrbit phase time)
  have htransport := quittingIsolatedValue_sub_soloReward_eq_prod_mul
    reward roots who pathValue K hpath hisoWindow 0 K (by omega)
  have hprod :
      (∏ offset ∈ Finset.range K,
        quittingStationaryContinueMass (roots offset)) =
      ∏ cyclePhase : Fin K,
        quittingStationaryContinueMass (cycle cyclePhase) := by
    simpa [roots, quittingCyclicRootSequence, quittingCyclicPrefixWeight] using
      (quittingCyclicPrefixWeight_card
        (fun cyclePhase =>
          quittingStationaryContinueMass (cycle cyclePhase)) phase)
  dsimp only [pathValue] at htransport
  simp only [zero_add, quittingCyclicOrbit_zero,
    quittingCyclicOrbit_card] at htransport
  rw [hprod] at htransport
  have hfactor :
      (value phase who - reward (quittingSingletonTerminal who) who) *
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryContinueMass (cycle cyclePhase)) = 0 := by
    linear_combination htransport
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exact absurd hzero (by linarith)

end GameTheory

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Suffix-replacement bounds -/

omit [Fintype ι] [DecidableEq ι] in
/-- A sequence is the phase switch that keeps its prefix and restarts its own
suffix at an arbitrary cutoff. -/
theorem quittingPhaseSwitchRoots_shift
    (roots : ℕ → ι → PMF Bool) (switch : ℕ) :
    quittingPhaseSwitchRoots roots (fun offset => roots (switch + offset)) switch =
      roots := by
  funext time
  by_cases htime : time < switch
  · exact quittingPhaseSwitchRoots_of_lt roots _ htime
  · rw [quittingPhaseSwitchRoots_of_le roots _ (Nat.not_lt.mp htime)]
    congr 1
    omega

omit [DecidableEq ι] in
/-- Replacing the suffix after a cutoff changes the prescribed terminal value
by at most twice the reward bound, weighted by the probability of reaching the
cutoff. -/
theorem abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound) :
    |quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 -
        quittingRootSequenceTerminalValue reward plan who 0| ≤
      2 * bound * quittingJointSurvivalWeight plan 0 switch := by
  let shiftedPlan : ℕ → ι → PMF Bool := fun offset => plan (switch + offset)
  have hswitch := quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
    reward plan punish switch who
  have hplan := quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
    reward plan shiftedPlan switch who
  have hshift : quittingPhaseSwitchRoots plan shiftedPlan switch = plan := by
    exact quittingPhaseSwitchRoots_shift plan switch
  rw [hshift] at hplan
  have hpunishBound := abs_quittingRootSequenceTerminalValue_le
    reward punish who 0 hbound hreward
  have hplanBound := abs_quittingRootSequenceTerminalValue_le
    reward shiftedPlan who 0 hbound hreward
  have hsurvival0 : 0 ≤ quittingJointSurvivalWeight plan 0 switch :=
    quittingJointSurvivalWeight_nonneg plan 0 switch
  rw [hswitch, hplan]
  have htail :
      |quittingRootSequenceTerminalValue reward punish who 0 -
          quittingRootSequenceTerminalValue reward shiftedPlan who 0| ≤
        2 * bound := by
    calc
      |quittingRootSequenceTerminalValue reward punish who 0 -
          quittingRootSequenceTerminalValue reward shiftedPlan who 0| ≤
          |quittingRootSequenceTerminalValue reward punish who 0| +
            |quittingRootSequenceTerminalValue reward shiftedPlan who 0| :=
        abs_sub _ _
      _ ≤ 2 * bound := by linarith
  rw [show
      (quittingRootSequenceTerminalValue reward
            (quittingTruncatedRoots plan switch) who 0 +
          quittingJointSurvivalWeight plan 0 switch *
            quittingRootSequenceTerminalValue reward punish who 0) -
        (quittingRootSequenceTerminalValue reward
            (quittingTruncatedRoots plan switch) who 0 +
          quittingJointSurvivalWeight plan 0 switch *
            quittingRootSequenceTerminalValue reward shiftedPlan who 0) =
        quittingJointSurvivalWeight plan 0 switch *
          (quittingRootSequenceTerminalValue reward punish who 0 -
            quittingRootSequenceTerminalValue reward shiftedPlan who 0) by ring,
    abs_mul, abs_of_nonneg hsurvival0]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left htail hsurvival0)

/-- Hazard-level suffix replacement.  If the unswitched plan already caps one
hazard deviation, replacing its suffix changes the resulting gain by at most
four reward bounds times the deviator-independent opponent-survival weight. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : quittingRootSequenceHazardTerminalValue reward plan who hazard 0 ≤
      quittingRootSequenceTerminalValue reward plan who 0) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 +
        4 * bound * quittingOpponentSurvivalWeight plan who 0 switch := by
  let shiftedPlan : ℕ → ι → PMF Bool := fun offset => plan (switch + offset)
  let shiftedHazard : ℕ → PMF Bool := fun offset => hazard (switch + offset)
  let deviatedSurvival := quittingJointSurvivalWeight
    (quittingRootSequenceUpdate plan who hazard) 0 switch
  let prescribedSurvival := quittingJointSurvivalWeight plan 0 switch
  have hdevSwitch := quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
    reward plan punish switch who hazard
  have hdevPlan := quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
    reward plan shiftedPlan switch who hazard
  have hshift : quittingPhaseSwitchRoots plan shiftedPlan switch = plan := by
    exact quittingPhaseSwitchRoots_shift plan switch
  rw [hshift] at hdevPlan
  have hpunishDevBound :
      |quittingRootSequenceHazardTerminalValue reward punish who shiftedHazard 0| ≤
        bound := by
    unfold quittingRootSequenceHazardTerminalValue
    exact abs_quittingRootSequenceTerminalValue_le reward _ who 0 hbound hreward
  have hplanDevBound :
      |quittingRootSequenceHazardTerminalValue reward shiftedPlan who
          shiftedHazard 0| ≤ bound := by
    unfold quittingRootSequenceHazardTerminalValue
    exact abs_quittingRootSequenceTerminalValue_le reward _ who 0 hbound hreward
  have hdevTail :
      quittingRootSequenceHazardTerminalValue reward punish who shiftedHazard 0 ≤
        quittingRootSequenceHazardTerminalValue reward shiftedPlan who
          shiftedHazard 0 + 2 * bound := by
    have h1 := (abs_le.mp hpunishDevBound).2
    have h2 := (abs_le.mp hplanDevBound).1
    linarith
  have hdevSurvival0 : 0 ≤ deviatedSurvival :=
    quittingJointSurvivalWeight_nonneg _ 0 switch
  have hdevScaled := mul_le_mul_of_nonneg_left hdevTail hdevSurvival0
  have hdevCompare :
      quittingRootSequenceHazardTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
        quittingRootSequenceHazardTerminalValue reward plan who hazard 0 +
          2 * bound * deviatedSurvival := by
    rw [hdevSwitch, hdevPlan]
    dsimp only [shiftedHazard, deviatedSurvival] at hdevScaled ⊢
    nlinarith
  have hpresCompare :=
    abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
      reward plan punish switch who hbound hreward
  have hdevLeOpponent : deviatedSurvival ≤
      quittingOpponentSurvivalWeight plan who 0 switch := by
    exact quittingJointSurvivalWeight_update_le_quittingOpponentSurvivalWeight
      plan who hazard 0 switch
  have hpresLeOpponent : prescribedSurvival ≤
      quittingOpponentSurvivalWeight plan who 0 switch := by
    exact quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      plan who 0 switch
  have hdevError : 2 * bound * deviatedSurvival ≤
      2 * bound * quittingOpponentSurvivalWeight plan who 0 switch := by
    exact mul_le_mul_of_nonneg_left hdevLeOpponent
      (mul_nonneg (by norm_num) hbound)
  have hpresError :
      quittingRootSequenceTerminalValue reward plan who 0 ≤
        quittingRootSequenceTerminalValue reward
            (quittingPhaseSwitchRoots plan punish switch) who 0 +
          2 * bound * quittingOpponentSurvivalWeight plan who 0 switch := by
    have hraw := (abs_le.mp hpresCompare).1
    have hjointError : 2 * bound * prescribedSurvival ≤
        2 * bound * quittingOpponentSurvivalWeight plan who 0 switch := by
      exact mul_le_mul_of_nonneg_left hpresLeOpponent
        (mul_nonneg (by norm_num) hbound)
    dsimp only [prescribedSurvival] at hjointError
    linarith
  linarith

/-! ## Target-identified terminal selection -/

/-- Terminal approximate equilibria whose terminal payoffs converge uniformly
to one prescribed target make that target a uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who, |quittingTerminalPayoff reward profile who - target who| ≤ ε) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro ε hε
  let terminalError := ε / 4
  have hterminalError : 0 < terminalError := by
    dsimp only [terminalError]
    linarith
  obtain ⟨profile, hnash, htarget⟩ :=
    hterminal terminalError hterminalError
  have huniform : (quittingGame reward).IsUniformεEquilibrium none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite reward profile
      (by dsimp only [terminalError]; linarith) hnash
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have hhalf : 0 < ε / 2 := by linarith
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          target who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hhalf)
    filter_upwards [hball] with horizon hhorizon
    have hclose := htarget who
    have htriangle :
        |(quittingGame reward).finiteAveragePayoff none horizon profile who -
            target who| ≤
          |(quittingGame reward).finiteAveragePayoff none horizon profile who -
              quittingTerminalPayoff reward profile who| +
            |quittingTerminalPayoff reward profile who - target who| := by
      calc
        |(quittingGame reward).finiteAveragePayoff none horizon profile who -
            target who| =
          |((quittingGame reward).finiteAveragePayoff none horizon profile who -
              quittingTerminalPayoff reward profile who) +
            (quittingTerminalPayoff reward profile who - target who)| := by
              ring_nf
        _ ≤ _ := abs_add_le _ _
    have hdelivery :
        |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          quittingTerminalPayoff reward profile who| < ε / 2 := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
    dsimp only [terminalError] at hclose
    linarith
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon => ⟨?_, ?_⟩⟩
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

/-- **Terminal compiler for a punishment-admissible absorbing cycle.**  At
every positive error it produces a terminal approximate equilibrium whose
terminal payoff is uniformly close to the cycle's displayed value at the
selected initial phase. -/
theorem exists_isεAsymptoticNash_close_of_punishmentAdmissibleCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (hadmissible : IsQuittingCyclePunishmentAdmissible reward cycle)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who - value phase who| ≤ ε := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    reward cycle value hpolicy habsorb
  have hnashTerminal : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase) := by
    rw [← hvalue]
    exact hnash
  by_cases hall : ∀ who : ι,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1
  · let profile := quittingCyclicBehaviorProfile reward cycle phase
    have hzero : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 profile :=
      isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate_finite
        reward cycle value phase hpolicy hnash hall
    refine ⟨profile, hzero.mono (by simpa using hε.le), ?_⟩
    intro who
    dsimp only [profile]
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue]
    simpa using hε.le
  · obtain ⟨owner, howner⟩ := not_forall.mp hall
    have hownerIR : quittingPunishmentValue reward owner ≤
        reward (quittingSingletonTerminal owner) owner :=
      (hadmissible owner).resolve_left howner
    have hisolated : ∀ cyclePhase,
        IsQuittingIsolatedRoot (cycle cyclePhase) owner :=
      isQuittingIsolatedRoot_of_not_cycleContracts cycle owner howner
    have hotherContracts : ∀ who, who ≠ owner →
        (∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who) < 1 := by
      intro who hwho
      by_contra hnot
      exact hwho (eq_of_not_cycleContracts cycle habsorb hnot howner)
    have hownerValue : value phase owner =
        reward (quittingSingletonTerminal owner) owner :=
      quittingCyclicValue_eq_soloReward_of_isolated reward cycle value
        hpolicy habsorb owner hisolated phase
    let bound := quittingRewardBound reward
    have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
    let tailError := ε / 4
    have htailError : 0 < tailError := by
      dsimp only [tailError]
      linarith
    obtain ⟨punishRow, hpunishStrict⟩ :=
      exists_quittingStationaryPunishmentRoot_lt_add
        reward owner htailError
    have hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
        reward (quittingSingletonTerminal owner) owner + tailError := by
      linarith
    let survivalCap := ε / (8 * bound + 1)
    have hdenominator : 0 < 8 * bound + 1 := by nlinarith
    have hsurvivalCap : 0 < survivalCap := by
      exact div_pos hε hdenominator
    have hsurvivalCap0 : 0 ≤ survivalCap := hsurvivalCap.le
    have hcapIdentity : (8 * bound + 1) * survivalCap = ε := by
      dsimp only [survivalCap]
      field_simp [ne_of_gt hdenominator]
    have hotherError : 4 * bound * survivalCap ≤ ε := by
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    have hownerError : tailError + 2 * bound * survivalCap ≤ ε := by
      dsimp only [tailError]
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    have htargetError : 2 * bound * survivalCap ≤ ε := by
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    let plan := quittingCyclicRootSequence cycle phase
    let punish : ℕ → ι → PMF Bool := fun _ => punishRow
    have hjointTendsto : Tendsto
        (quittingJointSurvivalWeight plan 0) atTop (nhds 0) := by
      exact tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
        cycle phase habsorb
    have hjointEventually : ∀ᶠ switch : ℕ in atTop,
        quittingJointSurvivalWeight plan 0 switch ≤ survivalCap := by
      have hlt := (tendsto_order.1 hjointTendsto).2
        survivalCap hsurvivalCap
      filter_upwards [hlt] with switch hswitch
      exact hswitch.le
    have hotherEventually : ∀ᶠ switch : ℕ in atTop,
        ∀ who, who ≠ owner →
          quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap := by
      apply Filter.eventually_all.mpr
      intro who
      by_cases hwho : who = owner
      · exact Filter.Eventually.of_forall fun _ hne => absurd hwho hne
      · have htendsto : Tendsto
            (quittingOpponentSurvivalWeight plan who 0) atTop (nhds 0) := by
          exact tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
            cycle phase who (hotherContracts who hwho)
        have hlt := (tendsto_order.1 htendsto).2 survivalCap hsurvivalCap
        filter_upwards [hlt] with switch hswitch
        intro _
        exact hswitch.le
    obtain ⟨threshold, hthreshold⟩ :=
      Filter.eventually_atTop.1 (hjointEventually.and hotherEventually)
    let switch := threshold
    have hswitch :
        quittingJointSurvivalWeight plan 0 switch ≤ survivalCap ∧
          ∀ who, who ≠ owner →
            quittingOpponentSurvivalWeight plan who 0 switch ≤ survivalCap :=
      hthreshold threshold le_rfl
    let profile := quittingPhaseSwitchProfile reward plan punish switch
    have hplanIsolated : ∀ time,
        IsQuittingIsolatedRoot (plan time) owner := by
      intro time
      exact hisolated (quittingCyclicOrbit phase time)
    have hnashProfile : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
      intro who deviation
      dsimp only [profile]
      rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        quittingProfileLiveRoot_quittingPhaseSwitchProfile]
      change quittingRootSequenceHazardTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who
          (quittingBehaviorLiveHazard reward deviation) 0 ≤
        quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 + ε
      by_cases hwho : who = owner
      · subst who
        have hprefix : ∀ g : ℕ → PMF Bool,
            quittingRootSequenceHazardTerminalValue reward
                (quittingTruncatedRoots plan switch) owner
                (quittingTruncatedHazard g switch) 0 ≤
              (1 - quittingJointSurvivalWeight
                (quittingRootSequenceUpdate plan owner g) 0 switch) *
                  reward (quittingSingletonTerminal owner) owner + 0 := by
          intro g
          rw [add_zero]
          exact le_of_eq
            (quittingRootSequenceHazardTerminalValue_truncated_eq_one_sub_survival_mul_of_isolated
              reward plan owner g switch
              (fun time _ => hplanIsolated time))
        have htail : ∀ g : ℕ → PMF Bool,
            quittingRootSequenceHazardTerminalValue reward punish owner g 0 ≤
              reward (quittingSingletonTerminal owner) owner + tailError := by
          intro g
          have hcap := quittingRootSequenceHazardTerminalValue_const_le_cap
            reward punishRow owner g
          simpa only [punish] using hcap.trans hpunish
        have hdeviation :=
          quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_coupled
            reward plan punish switch owner htailError.le hprefix htail
              (quittingBehaviorLiveHazard reward deviation)
        have hclose :=
          abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
            reward plan punish switch owner hbound
              (abs_reward_le_quittingRewardBound reward)
        have hbase : quittingRootSequenceTerminalValue reward plan owner 0 =
            reward (quittingSingletonTerminal owner) owner := by
          dsimp only [plan]
          rw [quittingRootSequenceTerminalValue_cyclic_eq]
          simp only [quittingCyclicOrbit_zero]
          rw [← hvalue]
          exact hownerValue
        have hreach : 2 * bound *
            quittingJointSurvivalWeight plan 0 switch ≤
              2 * bound * survivalCap := by
          exact mul_le_mul_of_nonneg_left hswitch.1
            (mul_nonneg (by norm_num) hbound)
        rw [hbase] at hclose
        have hlower := (abs_le.mp hclose).1
        linarith
      · have hbase :=
          quittingCyclicHazardTerminalValue_le_of_isZeroRootNash
            reward cycle phase who
              (quittingBehaviorLiveHazard reward deviation)
              bound hbound (abs_reward_le_quittingRewardBound reward)
              hnashTerminal (hotherContracts who hwho)
        have hdeviation :=
          quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan
            reward plan punish switch who
              (quittingBehaviorLiveHazard reward deviation)
              hbound (abs_reward_le_quittingRewardBound reward) (by
                dsimp only [plan]
                simpa only [quittingRootSequenceTerminalValue_cyclic_eq,
                  quittingCyclicOrbit_zero] using hbase)
        have hreach : 4 * bound *
            quittingOpponentSurvivalWeight plan who 0 switch ≤
              4 * bound * survivalCap := by
          exact mul_le_mul_of_nonneg_left (hswitch.2 who hwho)
            (mul_nonneg (by norm_num) hbound)
        linarith
    refine ⟨profile, hnashProfile, ?_⟩
    intro who
    dsimp only [profile]
    change |quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who 0 -
          value phase who| ≤ ε
    have hclose :=
      abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
        reward plan punish switch who hbound
          (abs_reward_le_quittingRewardBound reward)
    have hbase : quittingRootSequenceTerminalValue reward plan who 0 =
        value phase who := by
      dsimp only [plan]
      rw [quittingRootSequenceTerminalValue_cyclic_eq]
      simp only [quittingCyclicOrbit_zero]
      rw [← hvalue]
    rw [hbase] at hclose
    have hreach : 2 * bound *
        quittingJointSurvivalWeight plan 0 switch ≤
          2 * bound * survivalCap :=
      mul_le_mul_of_nonneg_left hswitch.1
        (mul_nonneg (by norm_num) hbound)
    exact hclose.trans (hreach.trans htargetError)

/-- **Named-payoff punishment-completed cycle compiler.**  The selected phase
value of every exact absorbing punishment-admissible cycle is a uniform
equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (hadmissible : IsQuittingCyclePunishmentAdmissible reward cycle) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value phase) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  intro ε hε
  exact exists_isεAsymptoticNash_close_of_punishmentAdmissibleCycle
    reward cycle value phase hpolicy hnash habsorb hadmissible hε


/-- Block-level form: a punishment-admissible absorbing cyclic continuation
block makes its named terminal vector a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_terminal_of_punishmentAdmissibleBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hadmissible : IsQuittingCyclePunishmentAdmissible reward
      (quittingCyclicContinuationBlockCycle period block)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none terminal := by
  have hresult := isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    reward (quittingCyclicContinuationBlockCycle period block)
      (quittingCyclicContinuationBlockValue period block) 0
      (quittingCyclicContinuationBlock_policy reward terminal period block hblock)
      (quittingCyclicContinuationBlock_rootNash reward terminal period block hblock)
      (quittingCyclicContinuationBlock_prod_continueMass_lt_one reward terminal
        period block hblock)
      hadmissible
  have horigin : quittingCyclicContinuationBlockValue period block 0 = terminal :=
    hblock.2.1
  rwa [horigin] at hresult

/-- Existential wrapper of the named block-level theorem. -/
theorem exists_uniformEquilibriumPayoff_of_punishmentAdmissibleBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hadmissible : IsQuittingCyclePunishmentAdmissible reward
      (quittingCyclicContinuationBlockCycle period block)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  ⟨terminal,
    isUniformEquilibriumPayoff_terminal_of_punishmentAdmissibleBlock
      reward terminal period block hblock hadmissible⟩

/-- The existing admissible-cycle compiler is recovered as a direct corollary
of punishment completion. -/
theorem isUniformEquilibriumPayoff_of_admissibleCycle_via_punishment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (hadmissible : IsQuittingCycleAdmissible reward cycle) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value phase) :=
  isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
    reward cycle value phase hpolicy hnash habsorb
      (isQuittingCyclePunishmentAdmissible_of_admissible
        reward cycle hadmissible)

end GameTheory
