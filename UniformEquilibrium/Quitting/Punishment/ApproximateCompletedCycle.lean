/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.CompletedCycle
import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate
import UniformEquilibrium.Quitting.Projective.Lasso

/-!
# Approximate punishment completion of absorbing cycles

Punishment completion remains valid when the contracting coordinates are only
approximately optimal.  The relevant local error is not the largest root
residual by itself: it is its cyclic survival charge divided by the deleted
contraction gap.  This module proves the corresponding quantitative compiler
against the cycle's actual terminal value.

The sole noncontracting coordinate of an absorbing cycle is still treated by
the exact isolated-prefix argument and an eventual stationary punishment.
Thus no approximation is charged at that coordinate.  This is the form needed
near a vanishing-hazard solo face, where the owner can postpone forever but
the other coordinates have contracting clocks.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Suffix replacement with an approximate base plan -/

/-- Replacing a suffix preserves a unilateral plan bound, up to the original
plan error and four reward bounds times the probability that the deviator's
opponents survive to the switch. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool) {bound planError : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hplan : quittingRootSequenceHazardTerminalValue reward plan who hazard 0 ≤
      quittingRootSequenceTerminalValue reward plan who 0 + planError) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 +
        planError +
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
  have hshift : quittingPhaseSwitchRoots plan shiftedPlan switch = plan :=
    quittingPhaseSwitchRoots_shift plan switch
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
      quittingOpponentSurvivalWeight plan who 0 switch :=
    quittingJointSurvivalWeight_update_le_quittingOpponentSurvivalWeight
      plan who hazard 0 switch
  have hpresLeOpponent : prescribedSurvival ≤
      quittingOpponentSurvivalWeight plan who 0 switch :=
    quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      plan who 0 switch
  have hdevError : 2 * bound * deviatedSurvival ≤
      2 * bound * quittingOpponentSurvivalWeight plan who 0 switch :=
    mul_le_mul_of_nonneg_left hdevLeOpponent
      (mul_nonneg (by norm_num) hbound)
  have hpresError :
      quittingRootSequenceTerminalValue reward plan who 0 ≤
        quittingRootSequenceTerminalValue reward
            (quittingPhaseSwitchRoots plan punish switch) who 0 +
          2 * bound * quittingOpponentSurvivalWeight plan who 0 switch := by
    have hraw := (abs_le.mp hpresCompare).1
    have hjointError : 2 * bound * prescribedSurvival ≤
        2 * bound * quittingOpponentSurvivalWeight plan who 0 switch :=
      mul_le_mul_of_nonneg_left hpresLeOpponent
        (mul_nonneg (by norm_num) hbound)
    dsimp only [prescribedSurvival] at hjointError
    linarith
  linarith

/-! ## One-cycle quantitative compiler -/

/-- **Approximate punishment-completed cycle compiler.**

At contracting coordinates, `cycleError` bounds the exact cyclic residual
charge.  At the possible isolated coordinate the punishment-admissibility
inequality closes the Never deviation.  The resulting terminal approximate
equilibrium delivers the cycle's actual terminal payoff at the selected phase.
-/
theorem exists_isεAsymptoticNash_close_of_punishmentAdmissibleCycle_rootError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ) {cycleError ε : ℝ}
    (hcycleError0 : 0 ≤ cycleError) (hcycleError : cycleError < ε)
    (hrootError0 : ∀ cyclePhase who, 0 ≤ rootError cyclePhase who)
    (hroot : ∀ cyclePhase who (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) who oneShot) who ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) who + rootError cyclePhase who)
    (habsorb : (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1)
    (hadmissible : IsQuittingCyclePunishmentAdmissible reward cycle)
    (hcharge : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 →
      quittingCyclicResidualCharge
          (fun cyclePhase =>
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) who)
          (fun cyclePhase => rootError cyclePhase who) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who) ≤ cycleError) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who -
            quittingCyclicTerminalValue reward cycle phase who| ≤ ε := by
  have hε : 0 < ε := lt_of_le_of_lt hcycleError0 hcycleError
  by_cases hall : ∀ who : ι,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1
  · let profile := quittingCyclicBehaviorProfile reward cycle phase
    have hnash : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) cycleError profile :=
      isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError_finite
        reward cycle phase rootError cycleError hrootError0 hroot hall
          (fun who => hcharge who (hall who))
    refine ⟨profile, hnash.mono (le_of_lt hcycleError), ?_⟩
    intro who
    dsimp only [profile]
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, sub_self, abs_zero]
    exact hε.le
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
    have hownerValue :
        quittingCyclicTerminalValue reward cycle phase owner =
          reward (quittingSingletonTerminal owner) owner := by
      let value : Fin K → Payoff ι :=
        quittingCyclicTerminalValue reward cycle
      have hpolicy : ∀ cyclePhase,
          value cyclePhase = quittingRootSuccessorPayoff reward
            (value (finRotate K cyclePhase)) (cycle cyclePhase) := by
        intro cyclePhase
        exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
          reward cycle cyclePhase
      exact quittingCyclicValue_eq_soloReward_of_isolated reward cycle value
        hpolicy habsorb owner hisolated phase
    let bound := quittingRewardBound reward
    have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
    let slack := ε - cycleError
    have hslack : 0 < slack := sub_pos.mpr hcycleError
    let tailError := slack / 4
    have htailError : 0 < tailError := by
      dsimp only [tailError]
      linarith
    obtain ⟨punishRow, hpunishStrict⟩ :=
      exists_quittingStationaryPunishmentRoot_lt_add
        reward owner htailError
    have hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
        reward (quittingSingletonTerminal owner) owner + tailError := by
      linarith
    let survivalCap := slack / (8 * bound + 1)
    have hdenominator : 0 < 8 * bound + 1 := by nlinarith
    have hsurvivalCap : 0 < survivalCap := div_pos hslack hdenominator
    have hsurvivalCap0 : 0 ≤ survivalCap := hsurvivalCap.le
    have hcapIdentity : (8 * bound + 1) * survivalCap = slack := by
      dsimp only [survivalCap]
      field_simp [ne_of_gt hdenominator]
    have hotherError : cycleError + 4 * bound * survivalCap ≤ ε := by
      dsimp only [slack] at hcapIdentity ⊢
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    have hownerError : tailError + 2 * bound * survivalCap ≤ ε := by
      dsimp only [tailError, slack] at hcapIdentity ⊢
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    have htargetError : 2 * bound * survivalCap ≤ ε := by
      dsimp only [slack] at hcapIdentity ⊢
      nlinarith [mul_nonneg hbound hsurvivalCap0]
    let plan := quittingCyclicRootSequence cycle phase
    let punish : ℕ → ι → PMF Bool := fun _ => punishRow
    have hjointTendsto : Tendsto
        (quittingJointSurvivalWeight plan 0) atTop (nhds 0) :=
      tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
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
            (quittingOpponentSurvivalWeight plan who 0) atTop (nhds 0) :=
          tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
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
          exact hownerValue
        have hreach : 2 * bound *
            quittingJointSurvivalWeight plan 0 switch ≤
              2 * bound * survivalCap :=
          mul_le_mul_of_nonneg_left hswitch.1
            (mul_nonneg (by norm_num) hbound)
        rw [hbase] at hclose
        have hlower := (abs_le.mp hclose).1
        linarith
      · have hbaseGap := quittingCyclicHazardTerminalGap_le_of_rootError
          reward cycle phase who
          (quittingBehaviorLiveHazard reward deviation)
          (fun cyclePhase => rootError cyclePhase who)
          bound hbound (abs_reward_le_quittingRewardBound reward)
          (fun cyclePhase => hrootError0 cyclePhase who)
          (fun cyclePhase oneShot => hroot cyclePhase who oneShot)
          (hotherContracts who hwho)
        have hbase : quittingRootSequenceHazardTerminalValue reward plan who
              (quittingBehaviorLiveHazard reward deviation) 0 ≤
            quittingRootSequenceTerminalValue reward plan who 0 +
              cycleError := by
          have hcharged := hcharge who (hotherContracts who hwho)
          have hbaseGap' :
              quittingRootSequenceHazardTerminalValue reward plan who
                    (quittingBehaviorLiveHazard reward deviation) 0 -
                  quittingRootSequenceTerminalValue reward plan who 0 ≤
                quittingCyclicResidualCharge
                    (fun cyclePhase =>
                      quittingStationaryFixedOpponentsContinueMass
                        (cycle cyclePhase) who)
                    (fun cyclePhase => rootError cyclePhase who) phase K /
                  (1 - ∏ cyclePhase : Fin K,
                    quittingStationaryFixedOpponentsContinueMass
                      (cycle cyclePhase) who) := by
            simpa only [plan, quittingRootSequenceTerminalValue_cyclic_eq,
              quittingCyclicOrbit_zero] using hbaseGap
          linarith
        have hdeviation :=
          quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add
            reward plan punish switch who
              (quittingBehaviorLiveHazard reward deviation)
              hbound (abs_reward_le_quittingRewardBound reward) hbase
        have hreach : 4 * bound *
            quittingOpponentSurvivalWeight plan who 0 switch ≤
              4 * bound * survivalCap :=
          mul_le_mul_of_nonneg_left (hswitch.2 who hwho)
            (mul_nonneg (by norm_num) hbound)
        linarith
    refine ⟨profile, hnashProfile, ?_⟩
    intro who
    dsimp only [profile]
    change |quittingRootSequenceTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who 0 -
          quittingCyclicTerminalValue reward cycle phase who| ≤ ε
    have hclose :=
      abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
        reward plan punish switch who hbound
          (abs_reward_le_quittingRewardBound reward)
    have hbase : quittingRootSequenceTerminalValue reward plan who 0 =
        quittingCyclicTerminalValue reward cycle phase who := by
      dsimp only [plan]
      rw [quittingRootSequenceTerminalValue_cyclic_eq]
      simp only [quittingCyclicOrbit_zero]
    rw [hbase] at hclose
    have hreach : 2 * bound *
        quittingJointSurvivalWeight plan 0 switch ≤
          2 * bound * survivalCap :=
      mul_le_mul_of_nonneg_left hswitch.1
        (mul_nonneg (by norm_num) hbound)
    exact hclose.trans (hreach.trans htargetError)

/-! ## Sharp period-one solo specialization -/

/-- A positive-hazard solo row need not be exactly Nash.  It is enough that
every outsider's complete stationary unilateral cap is within
`outsiderError` of the owner's singleton payoff vector.  Punishment completion
handles the owner, and no division by the vanishing owner hazard occurs. -/
theorem exists_isεAsymptoticNash_close_soloReward_of_cap_of_punishmentIR
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    {outsiderError ε : ℝ}
    (hpositive : 0 < (hazard true).toReal)
    (herror0 : 0 ≤ outsiderError) (herror : outsiderError < ε)
    (hcap : ∀ other, other ≠ owner →
      quittingStationaryUnilateralCap reward
          (quittingSoloStationaryRoot owner hazard) other ≤
        quittingSoloReward reward owner other + outsiderError)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who -
            quittingSoloReward reward owner who| ≤ ε := by
  let root := quittingSoloStationaryRoot owner hazard
  let cycle : Fin 1 → ι → PMF Bool := fun _ => root
  let target := quittingSoloReward reward owner
  have habsorb : (∏ cyclePhase : Fin 1,
      quittingStationaryContinueMass (cycle cyclePhase)) < 1 := by
    rw [Fin.prod_univ_one]
    dsimp only [cycle, root]
    exact quittingStationaryContinueMass_soloStationaryRoot_lt_one
      owner hazard hpositive
  have hpolicy : ∀ cyclePhase : Fin 1,
      (fun _ : Fin 1 => target) cyclePhase =
        quittingRootSuccessorPayoff reward
          ((fun _ : Fin 1 => target) (finRotate 1 cyclePhase))
          (cycle cyclePhase) := by
    intro cyclePhase
    dsimp only [cycle, root, target]
    exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward owner hazard).symm
  have hterminal : quittingCyclicTerminalValue reward cycle 0 = target := by
    have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
      reward cycle (fun _ : Fin 1 => target) hpolicy habsorb
    exact congrFun hvalue 0 |>.symm
  have hisolated : ∀ cyclePhase : Fin 1,
      IsQuittingIsolatedRoot (cycle cyclePhase) owner := by
    intro cyclePhase other hother
    simp [cycle, root, quittingSoloStationaryRoot, hother]
  have hotherContracts : ∀ other, other ≠ owner →
      (∏ cyclePhase : Fin 1,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) other) < 1 := by
    intro other hother
    rw [Fin.prod_univ_one]
    dsimp only [cycle, root]
    exact quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
      hother hazard hpositive
  let bound := quittingRewardBound reward
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  let slack := ε - outsiderError
  have hslack : 0 < slack := sub_pos.mpr herror
  let tailError := slack / 4
  have htailError : 0 < tailError := by
    dsimp only [tailError]
    linarith
  obtain ⟨punishRow, hpunishStrict⟩ :=
    exists_quittingStationaryPunishmentRoot_lt_add
      reward owner htailError
  have hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
      quittingSoloReward reward owner owner + tailError := by
    linarith
  let survivalCap := slack / (8 * bound + 1)
  have hdenominator : 0 < 8 * bound + 1 := by nlinarith
  have hsurvivalCap : 0 < survivalCap := div_pos hslack hdenominator
  have hsurvivalCap0 : 0 ≤ survivalCap := hsurvivalCap.le
  have hcapIdentity : (8 * bound + 1) * survivalCap = slack := by
    dsimp only [survivalCap]
    field_simp [ne_of_gt hdenominator]
  have hotherError : outsiderError + 4 * bound * survivalCap ≤ ε := by
    dsimp only [slack] at hcapIdentity ⊢
    nlinarith [mul_nonneg hbound hsurvivalCap0]
  have hownerError : tailError + 2 * bound * survivalCap ≤ ε := by
    dsimp only [tailError, slack] at hcapIdentity ⊢
    nlinarith [mul_nonneg hbound hsurvivalCap0]
  have htargetError : 2 * bound * survivalCap ≤ ε := by
    dsimp only [slack] at hcapIdentity ⊢
    nlinarith [mul_nonneg hbound hsurvivalCap0]
  let plan := quittingCyclicRootSequence cycle 0
  let punish : ℕ → ι → PMF Bool := fun _ => punishRow
  have hplanConst : plan = fun _ => root := by
    funext time who
    simp [plan, cycle, quittingCyclicRootSequence]
  have hjointTendsto : Tendsto
      (quittingJointSurvivalWeight plan 0) atTop (nhds 0) :=
    tendsto_zero_quittingJointSurvivalWeight_cyclicRootSequence
      cycle 0 habsorb
  have hjointEventually : ∀ᶠ switch : ℕ in atTop,
      quittingJointSurvivalWeight plan 0 switch ≤ survivalCap := by
    have hlt := (tendsto_order.1 hjointTendsto).2
      survivalCap hsurvivalCap
    filter_upwards [hlt] with switch hswitch
    exact hswitch.le
  have hotherEventually : ∀ᶠ switch : ℕ in atTop,
      ∀ other, other ≠ owner →
        quittingOpponentSurvivalWeight plan other 0 switch ≤ survivalCap := by
    apply Filter.eventually_all.mpr
    intro other
    by_cases hother : other = owner
    · exact Filter.Eventually.of_forall fun _ hne => absurd hother hne
    · have htendsto : Tendsto
          (quittingOpponentSurvivalWeight plan other 0) atTop (nhds 0) :=
        tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
          cycle 0 other (hotherContracts other hother)
      have hlt := (tendsto_order.1 htendsto).2 survivalCap hsurvivalCap
      filter_upwards [hlt] with switch hswitch
      intro _
      exact hswitch.le
  obtain ⟨threshold, hthreshold⟩ :=
    Filter.eventually_atTop.1 (hjointEventually.and hotherEventually)
  let switch := threshold
  have hswitch :
      quittingJointSurvivalWeight plan 0 switch ≤ survivalCap ∧
        ∀ other, other ≠ owner →
          quittingOpponentSurvivalWeight plan other 0 switch ≤ survivalCap :=
    hthreshold threshold le_rfl
  let profile := quittingPhaseSwitchProfile reward plan punish switch
  have hplanIsolated : ∀ time,
      IsQuittingIsolatedRoot (plan time) owner := by
    intro time
    exact hisolated (quittingCyclicOrbit 0 time)
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
                quittingSoloReward reward owner owner + 0 := by
        intro g
        rw [add_zero]
        exact le_of_eq
          (quittingRootSequenceHazardTerminalValue_truncated_eq_one_sub_survival_mul_of_isolated
            reward plan owner g switch (fun time _ => hplanIsolated time))
      have htail : ∀ g : ℕ → PMF Bool,
          quittingRootSequenceHazardTerminalValue reward punish owner g 0 ≤
            quittingSoloReward reward owner owner + tailError := by
        intro g
        have hpunishCap := quittingRootSequenceHazardTerminalValue_const_le_cap
          reward punishRow owner g
        simpa only [punish] using hpunishCap.trans hpunish
      have hdeviation :=
        quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_coupled
          reward plan punish switch owner htailError.le hprefix htail
            (quittingBehaviorLiveHazard reward deviation)
      have hclose :=
        abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
          reward plan punish switch owner hbound
            (abs_reward_le_quittingRewardBound reward)
      have hbase : quittingRootSequenceTerminalValue reward plan owner 0 =
          quittingSoloReward reward owner owner := by
        dsimp only [plan]
        rw [quittingRootSequenceTerminalValue_cyclic_eq,
          quittingCyclicOrbit_zero, hterminal]
      have hreach : 2 * bound * quittingJointSurvivalWeight plan 0 switch ≤
          2 * bound * survivalCap :=
        mul_le_mul_of_nonneg_left hswitch.1
          (mul_nonneg (by norm_num) hbound)
      rw [hbase] at hclose
      have hlower := (abs_le.mp hclose).1
      linarith
    · have hbase : quittingRootSequenceHazardTerminalValue reward plan who
            (quittingBehaviorLiveHazard reward deviation) 0 ≤
          quittingRootSequenceTerminalValue reward plan who 0 +
            outsiderError := by
        rw [hplanConst]
        have hcapBound := quittingRootSequenceHazardTerminalValue_const_le_cap
          reward root who (quittingBehaviorLiveHazard reward deviation)
        have hterminalPlan :
            quittingRootSequenceTerminalValue reward (fun _ => root) who 0 =
              quittingSoloReward reward owner who := by
          rw [← hplanConst]
          dsimp only [plan]
          rw [quittingRootSequenceTerminalValue_cyclic_eq,
            quittingCyclicOrbit_zero, hterminal]
        rw [hterminalPlan]
        exact hcapBound.trans (hcap who hwho)
      have hdeviation :=
        quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_of_plan_add
          reward plan punish switch who
            (quittingBehaviorLiveHazard reward deviation)
            hbound (abs_reward_le_quittingRewardBound reward) hbase
      have hreach : 4 * bound *
          quittingOpponentSurvivalWeight plan who 0 switch ≤
            4 * bound * survivalCap :=
        mul_le_mul_of_nonneg_left (hswitch.2 who hwho)
          (mul_nonneg (by norm_num) hbound)
      linarith
  refine ⟨profile, hnashProfile, ?_⟩
  intro who
  dsimp only [profile]
  change |quittingRootSequenceTerminalValue reward
      (quittingPhaseSwitchRoots plan punish switch) who 0 -
        quittingSoloReward reward owner who| ≤ ε
  have hclose :=
    abs_quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots_sub_plan_le
      reward plan punish switch who hbound
        (abs_reward_le_quittingRewardBound reward)
  have hbase : quittingRootSequenceTerminalValue reward plan who 0 =
      quittingSoloReward reward owner who := by
    dsimp only [plan]
    rw [quittingRootSequenceTerminalValue_cyclic_eq,
      quittingCyclicOrbit_zero, hterminal]
  rw [hbase] at hclose
  have hreach : 2 * bound * quittingJointSurvivalWeight plan 0 switch ≤
      2 * bound * survivalCap :=
    mul_le_mul_of_nonneg_left hswitch.1
      (mul_nonneg (by norm_num) hbound)
  exact hclose.trans (hreach.trans htargetError)

/-- Vanishing positive solo hazards with vanishing outsider stationary caps
make the owner's singleton payoff vector a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_approximate_caps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : ℕ → PMF Bool) (error : ℕ → ℝ)
    (hpositive : ∀ n, 0 < (hazard n true).toReal)
    (herror0 : ∀ n, 0 ≤ error n)
    (herrorVanish : Tendsto error atTop (nhds 0))
    (hcap : ∀ n other, other ≠ owner →
      quittingStationaryUnilateralCap reward
          (quittingSoloStationaryRoot owner (hazard n)) other ≤
        quittingSoloReward reward owner other + error n)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  intro ε hε
  have heventually : ∀ᶠ n : ℕ in atTop, error n < ε :=
    (tendsto_order.1 herrorVanish).2 ε hε
  obtain ⟨n, hn⟩ := heventually.exists
  exact exists_isεAsymptoticNash_close_soloReward_of_cap_of_punishmentIR
    reward owner (hazard n) (hpositive n) (herror0 n) hn
      (hcap n) hpunishment

/-- Approximate endpoint Nash against continuations converging to the owner's
singleton vector implies the cap hypothesis above.  No lower bound, rate of
decay, or convergence assumption on the positive hazards is needed. -/
theorem isUniformEquilibriumPayoff_soloReward_of_approximate_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : ℕ → PMF Bool)
    (continuation : ℕ → Payoff ι)
    (endpointError targetError : ℕ → ℝ)
    (hpositive : ∀ n, 0 < (hazard n true).toReal)
    (hendpointError0 : ∀ n, 0 ≤ endpointError n)
    (htargetError0 : ∀ n, 0 ≤ targetError n)
    (hendpointVanish : Tendsto endpointError atTop (nhds 0))
    (htargetVanish : Tendsto targetError atTop (nhds 0))
    (hclose : ∀ n who,
      |continuation n who - quittingSoloReward reward owner who| ≤
        targetError n)
    (hnash : ∀ n, IsεQuittingRootEndpointNash reward (continuation n)
      (endpointError n) (quittingSoloStationaryRoot owner (hazard n)))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let totalError : ℕ → ℝ := fun n => endpointError n + targetError n
  apply isUniformEquilibriumPayoff_soloReward_of_approximate_caps
    reward owner hazard totalError hpositive
  · intro n
    exact add_nonneg (hendpointError0 n) (htargetError0 n)
  · simpa [totalError] using hendpointVanish.add htargetVanish
  · intro n other hother
    let root := quittingSoloStationaryRoot owner (hazard n)
    let solo := quittingSoloReward reward owner
    have happroxDiff :
        quittingRootEndpointDifference reward (continuation n) root other ≤
          endpointError n := by
      have h := (hnash n other).1
      simpa [root, quittingSoloStationaryRoot, hother] using h
    have hdiffClose := abs_quittingRootEndpointDifference_sub_le_tail
      reward solo (continuation n) root other
    have hdiffClose' :
        |quittingRootEndpointDifference reward solo root other -
            quittingRootEndpointDifference reward (continuation n) root other| ≤
          targetError n :=
      hdiffClose.trans (by simpa [solo, abs_sub_comm] using hclose n other)
    have hsoloDiff :
        quittingRootEndpointDifference reward solo root other ≤
          totalError n := by
      dsimp only [totalError]
      linarith [(abs_le.mp hdiffClose').2]
    rw [quittingStationaryUnilateralCap_solo_other
      reward hother (hazard n) (hpositive n)]
    apply max_le
    · have hquit :
          quittingStationaryFixedOpponentsQuitValue reward root other =
            quittingRootQuitPayoff reward solo root other := by
        symm
        simpa [root, quittingStationaryFixedOpponentsQuitValue] using
          (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward (fun _ => root) other solo 0)
      have hcontinue :
          quittingRootContinuePayoff reward solo root other = solo other := by
        dsimp only [root, solo]
        rw [quittingRootContinuePayoff_soloStationaryRoot_other
          reward hother]
        have hsum := quittingSoloHazardMass_add (hazard n)
        rw [← add_mul]
        rw [add_comm, hsum, one_mul]
      rw [hquit]
      change quittingRootQuitPayoff reward solo root other ≤
        solo other + totalError n
      unfold quittingRootEndpointDifference at hsoloDiff
      rw [hcontinue] at hsoloDiff
      linarith
    · exact le_add_of_nonneg_right
        (add_nonneg (hendpointError0 n) (htargetError0 n))
  · exact hpunishment

/-! ## Accuracy families -/

/-- Fixed-period approximate punishment-completed cycles whose charged errors
vanish and whose selected terminal values approach one target compile that
target to a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_approximate_punishmentAdmissibleCycles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (cycle : ℕ → Fin K → ι → PMF Bool)
    (phase : ℕ → Fin K)
    (rootError : ℕ → Fin K → ι → ℝ)
    (cycleError targetError : ℕ → ℝ)
    (hvanish : Tendsto cycleError atTop (nhds 0))
    (htargetVanish : Tendsto targetError atTop (nhds 0))
    (hcycleError0 : ∀ n, 0 ≤ cycleError n)
    (hrootError0 : ∀ n cyclePhase who,
      0 ≤ rootError n cyclePhase who)
    (hroot : ∀ n cyclePhase who (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward (cycle n)
            (finRotate K cyclePhase))
          (Function.update (cycle n cyclePhase) who oneShot) who ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward (cycle n)
              (finRotate K cyclePhase))
            (cycle n cyclePhase) who + rootError n cyclePhase who)
    (habsorb : ∀ n, (∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle n cyclePhase)) < 1)
    (hadmissible : ∀ n,
      IsQuittingCyclePunishmentAdmissible reward (cycle n))
    (hcharge : ∀ n who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle n cyclePhase) who) < 1 →
      quittingCyclicResidualCharge
          (fun cyclePhase =>
            quittingStationaryFixedOpponentsContinueMass
              (cycle n cyclePhase) who)
          (fun cyclePhase => rootError n cyclePhase who) (phase n) K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle n cyclePhase) who) ≤ cycleError n)
    (htarget : ∀ n who,
      |quittingCyclicTerminalValue reward (cycle n) (phase n) who -
        target who| ≤ targetError n) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  have hcycleEventually : ∀ᶠ n : ℕ in atTop, cycleError n < ε / 3 :=
    (tendsto_order.1 hvanish).2 (ε / 3) hthird
  have htargetEventually : ∀ᶠ n : ℕ in atTop, targetError n < ε / 3 :=
    (tendsto_order.1 htargetVanish).2 (ε / 3) hthird
  obtain ⟨n, hn⟩ := (hcycleEventually.and htargetEventually).exists
  obtain ⟨profile, hnash, hclose⟩ :=
    exists_isεAsymptoticNash_close_of_punishmentAdmissibleCycle_rootError
      reward (cycle n) (phase n) (rootError n)
      (cycleError := cycleError n) (ε := 2 * ε / 3)
      (hcycleError0 n) (by linarith [hn.1])
      (hrootError0 n) (hroot n) (habsorb n) (hadmissible n) (hcharge n)
  refine ⟨profile, hnash.mono (by linarith), ?_⟩
  intro who
  calc
    |quittingTerminalPayoff reward profile who - target who| ≤
        |quittingTerminalPayoff reward profile who -
            quittingCyclicTerminalValue reward (cycle n) (phase n) who| +
          |quittingCyclicTerminalValue reward (cycle n) (phase n) who -
            target who| := abs_sub_le _ _ _
    _ ≤ ε := by linarith [hclose who, htarget n who, hn.2]

end GameTheory
