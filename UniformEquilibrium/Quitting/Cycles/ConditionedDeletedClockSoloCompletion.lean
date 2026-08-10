/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockTerminalConcentration
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseCompiler
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseUniform
import UniformEquilibrium.Quitting.Punishment.ApproximateCompletedCycle

/-!
# Approximate solo completion after deleting a deficient clock

This module is the strategic consumer for the conditioned owner-monopoly
branch.  If the original roots have vanishing opponent hazard, their selected
continuations converge to one owner's singleton vector, and outsiders' pure
Quit endpoints are asymptotically safe, then deleting the other hazards gives
vanishing unilateral caps for a solo stationary root.  The existing
punishment-completed solo compiler then produces the singleton vector as a
uniform-equilibrium payoff.

The theorem keeps the punishment inequality explicit.  Terminal
concentration alone does not imply individual rationality for the exceptional
owner.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A joint-absorption-scaled policy error with a coefficient tending to zero
makes the stored value and the literal terminal value asymptotically agree on
late suffixes.  Unlike the strategic compiler, this selection statement needs
only joint survival. -/
theorem tendsto_value_sub_terminalValue_of_vanishing_jointPolicyCoefficient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (coefficient : ℕ → ℝ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hvalue : ∀ time player, |value time player| ≤ M)
    (hcoefficientVanish : Tendsto coefficient atTop (nhds 0))
    (hpolicy : ∀ time player,
      |value time player -
          quittingRootSuccessorPayoff reward (value (time + 1))
            (roots time) player| ≤
        coefficient time * quittingRootAbsorptionMass (roots time))
    (hsurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0)) :
    Tendsto (fun start =>
      value start who -
        quittingRootSequenceTerminalValue reward roots who start)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  have heventually : ∀ᶠ time : ℕ in atTop,
      coefficient time < epsilon / 2 :=
    (tendsto_order.1 hcoefficientVanish).2 (epsilon / 2) hhalf
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨threshold, fun start hstart => ?_⟩
  let shiftedRoots : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let shiftedValue : ℕ → Payoff ι := fun time => value (start + time)
  have hshiftedSurvival : ∀ later,
      Tendsto (quittingJointSurvivalWeight shiftedRoots later)
        atTop (nhds 0) := by
    intro later
    apply (hsurvival (start + later)).congr'
    exact Filter.Eventually.of_forall fun fuel => by
      unfold shiftedRoots
      rw [quittingJointSurvivalWeight_eq_prod,
        quittingJointSurvivalWeight_eq_prod]
      apply Finset.prod_congr rfl
      intro offset _
      congr 2
      omega
  have hshiftedPolicy : ∀ time player,
      |shiftedValue time player -
          quittingRootSuccessorPayoff reward (shiftedValue (time + 1))
            (shiftedRoots time) player| ≤
        (epsilon / 2) * quittingRootAbsorptionMass (shiftedRoots time) := by
    intro time player
    have hlocal := hpolicy (start + time) player
    have hcoefficient : coefficient (start + time) ≤ epsilon / 2 :=
      (hthreshold (start + time) (hstart.trans
        (Nat.le_add_right start time))).le
    have habsorption := quittingRootAbsorptionMass_nonneg (roots (start + time))
    calc
      |_ - _| ≤ coefficient (start + time) *
          quittingRootAbsorptionMass (roots (start + time)) := by
        simpa only [shiftedValue, shiftedRoots, Nat.add_assoc] using hlocal
      _ ≤ (epsilon / 2) * quittingRootAbsorptionMass (roots (start + time)) :=
        mul_le_mul_of_nonneg_right hcoefficient habsorption
      _ = _ := rfl
  have hselected :=
    abs_value_sub_rootSequenceTerminalValue_le_of_jointPolicyError
      reward shiftedRoots shiftedValue hM hreward
      (fun time player => hvalue (start + time) player)
      hshiftedPolicy hshiftedSurvival 0 who
  rw [show shiftedValue 0 who = value start who by
      simp [shiftedValue]] at hselected
  rw [show quittingRootSequenceTerminalValue reward shiftedRoots who 0 =
      quittingRootSequenceTerminalValue reward roots who start by
    symm
    exact quittingRootSequenceTerminalValue_eq_shift reward roots who start]
    at hselected
  rw [Real.dist_eq, sub_zero]
  exact hselected.trans_lt (by linarith)

/-- Vanishing opponent hazards, continuation error, and outsider pure-Quit
error are sufficient for approximate punishment-completed solo cycles. -/
theorem isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (roots : ℕ → ι → PMF Bool)
    (continuation : ℕ → Payoff ι)
    (hazardError targetError quitError : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ n, 0 < (roots n owner true).toReal)
    (hhazardError0 : ∀ n, 0 ≤ hazardError n)
    (htargetError0 : ∀ n, 0 ≤ targetError n)
    (hquitError0 : ∀ n, 0 ≤ quitError n)
    (hhazardVanish : Tendsto hazardError atTop (nhds 0))
    (htargetVanish : Tendsto targetError atTop (nhds 0))
    (hquitVanish : Tendsto quitError atTop (nhds 0))
    (hhazard : ∀ n,
      1 - quittingStationaryFixedOpponentsContinueMass (roots n) owner ≤
        hazardError n)
    (hclose : ∀ n who,
      |continuation n who - quittingSoloReward reward owner who| ≤
        targetError n)
    (hquit : ∀ n who, who ≠ owner →
      quittingStationaryFixedOpponentsQuitValue reward (roots n) who ≤
        continuation n who + quitError n)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let totalError : ℕ → ℝ := fun n =>
    2 * M * hazardError n + targetError n + quitError n
  apply isUniformEquilibriumPayoff_soloReward_of_approximate_caps
    reward owner (fun n => roots n owner) totalError hpositive
  · intro n
    dsimp only [totalError]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hM) (hhazardError0 n))
        (htargetError0 n))
      (hquitError0 n)
  · have hdeleteVanish : Tendsto (fun n => 2 * M * hazardError n)
        atTop (nhds 0) := by
      simpa using hhazardVanish.const_mul (2 * M)
    simpa [totalError] using hdeleteVanish.add htargetVanish |>.add hquitVanish
  · intro n who hwho
    have hdelete :=
      abs_quittingStationaryFixedOpponentsQuitValue_sub_solo_le_of_hazard
        reward (roots n) hwho hM hreward (hhazard n)
    have hdeleteLower := (abs_le.mp hdelete).1
    have htargetUpper := (abs_le.mp (hclose n who)).2
    have hfull := hquit n who hwho
    rw [quittingStationaryUnilateralCap_solo_other
      reward hwho (roots n owner) (hpositive n)]
    apply max_le
    · dsimp only [totalError]
      linarith
    · exact le_add_of_nonneg_right
        (add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hM)
              (hhazardError0 n))
            (htargetError0 n))
          (hquitError0 n))
  · exact hpunishment

/-- **Deficient conditioned clock compiler.**  On the singleton-tight
diffuse stratum, a summable deleted clock is not a residual counterexample
branch once the exceptional owner's singleton payoff is individually
rational.  The rescaled chronology concentrates on that singleton vector;
late owner-active rows have vanishing outsider caps and compile through
approximate punishment completion. -/
theorem isUniformEquilibriumPayoff_soloReward_of_summableConditionedDeletedClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (owner : ι) (start : ℕ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsmall : ∀ time, start ≤ time → Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let M := quittingRewardBound reward
  let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
  let targetValue : ℕ → Payoff ι := fun time =>
    quittingTailConditionedValue roots value boundary time
  obtain ⟨hopponentTotal, _hothers, howner, hpositiveLate⟩ :=
    conditionedDeletedClock_ownerMonopoly roots owner start hpositive
      heventualZero hmesh hsummable
  have hopponentRaw :=
    summable_quittingTailDiffuseRescaledRoot_opponentAbsorption
      roots owner start hpositive hopponentTotal
  have hopponent : Summable (fun offset =>
      quittingOpponentClockCharge targetRoots owner (start + offset)) := by
    simpa [targetRoots, quittingOpponentClockCharge,
      quittingTailDiffuseRescaledRoots] using hopponentRaw
  have habsorptionRaw :=
    not_summable_quittingTailDiffuseRescaledRoot_absorptionMass
      roots owner start hpositive howner
  have habsorption : ¬Summable (fun offset =>
      quittingRootAbsorptionMass (targetRoots (start + offset))) := by
    simpa [targetRoots, quittingTailDiffuseRescaledRoots] using habsorptionRaw
  let monoRoots : ℕ → ι → PMF Bool := fun time => targetRoots (start + time)
  let monoValue : ℕ → Payoff ι := fun time => targetValue (start + time)
  let coefficient : ℕ → ℝ := fun time =>
    6 * M * Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots (start + time)
  have hcoefficientVanish : Tendsto coefficient atTop (nhds 0) := by
    have halpha := hmesh.comp (tendsto_add_atTop_nat start)
    simpa [coefficient, Nat.add_comm] using
      halpha.const_mul (6 * M * Fintype.card ι)
  have habsorptionTail : ∀ later, ¬Summable (fun offset =>
      quittingRootAbsorptionMass (monoRoots (later + offset))) := by
    intro later hsuffix
    let charge : ℕ → ℝ := fun offset =>
      quittingRootAbsorptionMass (targetRoots (start + offset))
    have hshift : Summable (fun offset => charge (offset + later)) := by
      simpa only [charge, monoRoots, Nat.add_assoc, Nat.add_comm later]
        using hsuffix
    exact habsorption ((summable_nat_add_iff later).1 hshift)
  have hsurvival : ∀ later,
      Tendsto (quittingJointSurvivalWeight monoRoots later)
        atTop (nhds 0) := by
    intro later
    exact tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
      monoRoots later (habsorptionTail later)
  have hpolicyError : ∀ time who,
      |monoValue time who -
          quittingRootSuccessorPayoff reward (monoValue (time + 1))
            (monoRoots time) who| ≤
        coefficient time * quittingRootAbsorptionMass (monoRoots time) := by
    intro time who
    have hlocal :=
      abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
        (reward := reward) roots value boundary hpolicy
        (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward) hconditionedBound
        (start + time) who (hpositive (start + time))
          (hpositive (start + time + 1)) le_rfl
          (hsmall (start + time) (Nat.le_add_right start time))
    simpa [monoRoots, monoValue, targetRoots, targetValue, coefficient,
      M, quittingTailDiffuseRescaledRoots, Nat.add_assoc] using hlocal
  have hrealization : ∀ who, Tendsto (fun time =>
      monoValue time who -
        quittingRootSequenceTerminalValue reward monoRoots who time)
      atTop (nhds 0) := by
    intro who
    exact tendsto_value_sub_terminalValue_of_vanishing_jointPolicyCoefficient
      reward monoRoots monoValue coefficient who
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      (fun time player => hconditionedBound (start + time) player)
      hcoefficientVanish hpolicyError hsurvival
  have hterminalOriginal :=
    tendsto_quittingRootSequenceTerminalValue_soloReward_of_ownerMonopoly
      reward targetRoots owner
  have hterminal : ∀ who, Tendsto (fun time =>
      quittingRootSequenceTerminalValue reward monoRoots who time)
      atTop (nhds (quittingSoloReward reward owner who)) := by
    intro who
    have horiginal := hterminalOriginal who start
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) habsorption hopponent
    apply horiginal.congr'
    exact Filter.Eventually.of_forall fun time => by
      change quittingRootSequenceTerminalValue reward targetRoots who
          (start + time) =
        quittingRootSequenceTerminalValue reward monoRoots who time
      calc
        quittingRootSequenceTerminalValue reward targetRoots who
            (start + time) =
          quittingRootSequenceTerminalValue reward
            (fun offset => targetRoots ((start + time) + offset)) who 0 :=
              quittingRootSequenceTerminalValue_eq_shift
                reward targetRoots who (start + time)
        _ = quittingRootSequenceTerminalValue reward
            (fun offset => monoRoots (time + offset)) who 0 := by
              congr 3
              funext offset
              simp only [monoRoots, Nat.add_assoc]
        _ = quittingRootSequenceTerminalValue reward monoRoots who time :=
          (quittingRootSequenceTerminalValue_eq_shift
            reward monoRoots who time).symm
  have hmonoValue : ∀ who, Tendsto (fun time => monoValue time who)
      atTop (nhds (quittingSoloReward reward owner who)) := by
    intro who
    have hadd := (hrealization who).add (hterminal who)
    simpa only [sub_add_cancel, zero_add] using hadd
  let select : ℕ → ℕ := fun threshold =>
    Classical.choose (hpositiveLate threshold)
  have hselectSpec : ∀ threshold,
      threshold ≤ select threshold ∧
        0 < quittingTailDiffuseRescaledHazard
          roots (start + select threshold) owner := fun threshold =>
    Classical.choose_spec (hpositiveLate threshold)
  have hselectTendsto : Tendsto select atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro threshold
    filter_upwards [eventually_ge_atTop threshold] with later hlater
    exact hlater.trans (hselectSpec later).1
  let selectedRoots : ℕ → ι → PMF Bool := fun n =>
    targetRoots (start + select n)
  let selectedValue : ℕ → Payoff ι := fun n => monoValue (select n)
  let hazardError : ℕ → ℝ := fun n =>
    quittingTailDiffuseRescaledOpponentTotal
      roots (start + select n) owner
  let targetError : ℕ → ℝ := fun n =>
    ∑ who : ι,
      |selectedValue n who - quittingSoloReward reward owner who|
  let quitError : ℕ → ℝ := fun n =>
    6 * M * Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots (start + select n)
  have hselectedPositive : ∀ n,
      0 < (selectedRoots n owner true).toReal := by
    intro n
    change 0 < hazardOfRoot
      (quittingTailDiffuseRescaledRoot roots (start + select n)
        (hpositive (start + select n))) owner
    rw [congrFun (hazardOfRoot_quittingTailDiffuseRescaledRoot
      roots (start + select n) (hpositive (start + select n))) owner]
    exact (hselectSpec n).2
  have hhazardError0 : ∀ n, 0 ≤ hazardError n := by
    intro n
    unfold hazardError quittingTailDiffuseRescaledOpponentTotal
    exact Finset.sum_nonneg fun other _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots
        (start + select n) other (hpositive (start + select n))
  have htargetError0 : ∀ n, 0 ≤ targetError n := by
    intro n
    unfold targetError
    exact Finset.sum_nonneg fun who _ => abs_nonneg _
  have hquitError0 : ∀ n, 0 ≤ quitError n := by
    intro n
    unfold quitError
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
        (Nat.cast_nonneg _))
      (quittingTailConditionedAbsorptionWeight_nonneg roots
        (start + select n) (hpositive (start + select n)))
  have hhazardVanish : Tendsto hazardError atTop (nhds 0) := by
    have hbase := hopponentTotal.tendsto_atTop_zero
    have hselected := hbase.comp hselectTendsto
    change Tendsto (fun n =>
      quittingTailDiffuseRescaledOpponentTotal
        roots (start + select n) owner) atTop (nhds 0)
    convert hselected using 1
    funext n
    rfl
  have htargetVanish : Tendsto targetError atTop (nhds 0) := by
    have hsum := tendsto_finsetSum Finset.univ (fun who _ => by
      have hselected := (hmonoValue who).comp hselectTendsto
      have habs :=
        (hselected.sub_const (quittingSoloReward reward owner who)).abs
      simpa only [Function.comp_apply, selectedValue, sub_self, abs_zero]
        using habs)
    simpa [targetError] using hsum
  have hquitVanish : Tendsto quitError atTop (nhds 0) := by
    have halpha := (hmesh.comp (tendsto_add_atTop_nat start)).comp hselectTendsto
    simpa [quitError, M, Function.comp_apply, Nat.add_comm] using
      halpha.const_mul (6 * quittingRewardBound reward * Fintype.card ι)
  apply isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits
    reward owner selectedRoots selectedValue hazardError targetError quitError
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward) hselectedPositive
    hhazardError0 htargetError0 hquitError0 hhazardVanish htargetVanish
    hquitVanish
  · intro n
    exact quittingTailDiffuseRescaledRoot_opponentAbsorption_le_opponentTotal
      roots (start + select n) owner (hpositive (start + select n))
  · intro n who
    unfold targetError
    exact Finset.single_le_sum
      (fun player _ => abs_nonneg
        (selectedValue n player - quittingSoloReward reward owner player))
      (Finset.mem_univ who)
  · intro n who hwho
    simpa [selectedRoots, selectedValue, targetRoots, monoValue, targetValue,
      quitError, M, quittingTailDiffuseRescaledRoots] using
        quittingStationaryFixedOpponentsQuitValue_rescaledRoot_le_conditionedValue_add_of_nash
          (reward := reward) roots value boundary hpolicy hnash
          (start + select n) who
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
          (hpositive (start + select n)) (htight who)
          (hsmall (start + select n)
            (Nat.le_add_right start (select n)))
  · exact hpunishment

/-- **Closed singleton-tight diffuse alternative.**  If every singleton
payoff is above its owner's punishment value, then deleted-clock completeness
is no longer an assumption: complete clocks use the diffuse compiler, while a
deficient clock uses owner-monopoly concentration and punishment-completed
solo cycles. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseTail_punishmentIR
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hclock : ∃ owner start, Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner)
  · obtain ⟨owner, start, hsummable⟩ := hclock
    have hscaled : Tendsto (fun time =>
        Fintype.card ι * quittingTailConditionedAbsorptionWeight roots time)
        atTop (nhds 0) := by
      simpa using hmesh.const_mul (Fintype.card ι : ℝ)
    have heventually : ∀ᶠ time : ℕ in atTop,
        Fintype.card ι *
          quittingTailConditionedAbsorptionWeight roots time < 1 :=
      (tendsto_order.1 hscaled).2 1 zero_lt_one
    obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
    let newStart := start + threshold
    have hsummableNew : Summable (fun offset =>
        quittingTailConditionedOpponentWeight
          roots (newStart + offset) owner) := by
      have hshift : Summable (fun offset =>
          (fun later => quittingTailConditionedOpponentWeight
            roots (start + later) owner) (offset + threshold)) :=
        (summable_nat_add_iff threshold).2 hsummable
      simpa [newStart, Nat.add_assoc, Nat.add_comm threshold] using hshift
    have hsmall : ∀ time, newStart ≤ time →
        Fintype.card ι *
          quittingTailConditionedAbsorptionWeight roots time ≤ 1 := by
      intro time htime
      exact (hthreshold time (by
        dsimp only [newStart] at htime
        omega)).le
    refine ⟨quittingSoloReward reward owner, ?_⟩
    exact
      isUniformEquilibriumPayoff_soloReward_of_summableConditionedDeletedClock
        reward roots value boundary owner newStart hpolicy hnash hpositive
        heventualZero hconditionedBound htight hmesh hsmall
        hsummableNew (hpunishment owner)
  · apply quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseTail
      reward roots value boundary hpolicy hnash hpositive hconditionedBound
        htight hmesh
    push Not at hclock
    exact hclock

end GameTheory
